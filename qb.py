#!/usr/bin/env python

"""
(qb conf) ->
    print qb conf

(qb last) ->
    print last jobid

(qb qubits [TARGETS]) ->
    print all the qubits for TARGETS

(qb make [TARGETS]) ->
    start making TARGETS from Qfile

(qb pack [TARGETS]) ->
    create QPACK for TARGETS

(qb seed [TARGETS]) ->
    start making TARGETS from QUBITS_FILE
    continue until QUBITS_FILE complete

(qb sync [JOBID]) ->
    sync jobspace

(qb stat [JOBID]) ->
    get who did what and when

(qb spawn [JOBID] [QPACK]) ->
    ssh each NODE:
     cd [JOBID] job directory
     spawn `qb seed -j [JOBID] -p PROFILE DIVVY(TARGETS from QPACK)`
    splits TARGETS across both processes & nodes

(qb share [QPACK]) ->
    copies QPACK to all nodes, unpacks
    returns JOBID

(qb pssh COMMAND) ->
    ssh each NODE:
     COMMAND

(qb kill [JOBISH] [SIGNAL]) ->
    ssh each NODE:
     pkill -SIGNAL "qb seed [-j JOBISH]"

(qb run [TARGETS]) ->
    qb pack TARGETS
    qb spawn `qb share`

(qb clean) ->
    clean entire jobspace
"""

import os
import re
import socket
import sys
import time
import uuid

from collections import defaultdict
from fnmatch import fnmatch
from itertools import chain, count, groupby
from random import randint, sample
from shutil import copytree, rmtree
from subprocess import Popen, PIPE
from traceback import format_exc
from urllib import quote_plus, unquote_plus
from warnings import warn

def verbosity(level):
    return conf.get('verbose') >= level

def log(o, v=1):
    if verbosity(v):
        sys.stderr.write(str(o) + '\n')

def sh(cmd, *args, **opts):
    log("Calling %s with %s and %s" % (cmd, args, opts), 2)
    return Popen(cmd, *args, **opts)

def cat(data, proc):
    proc.stdin.write(data)
    proc.stdin.close()
    proc.wait()

def dead((host, pid)):
    return sh(('ssh', host, 'ps %s' % pid), stdout=PIPE).wait()

def pscp(src, dsts, scp='scp', P=16):
    xargs = ('xargs', '-t') if verbosity(3) else ('xargs',)
    scp = scp + ' -v' if conf.get('verbose') else scp + ' -q'
    proc = sh(xargs + ('-L', '1', '-P', str(P), 'bash', '-c', "%s $1 $2" % scp, '-'), stdin=PIPE)
    cat('\n'.join('%s\t%s' % (src, dst) for dst in dsts), proc)

def pssh(orders, ssh='ssh', P=16):
    xargs = ('xargs', '-t') if verbosity(3) else ('xargs',)
    fmt = r"\e[35m@: %s \e[0m\n%s\n\e[36m?: %s\e[0m\n"
    enc = r"printf \"%s\" $1 \"\`(${*:2}) 2>&1\`\" \$?" % fmt
    proc = sh(xargs + ('-L', '1', '-P', str(P), 'bash', '-c', "%s $1 \"%s\"" % (ssh, enc), '-'), stdin=PIPE)
    cat('\n'.join('%s\t%s' % o for o in orders), proc)

def aws(*args, **opts):
    return sh(('aws',) + args + (() if verbosity(2) else ('--quiet', )), **opts).wait()

def dotfile(path):
    return os.path.basename(path).startswith('.')

def vclock_gte(a, b):
    return a[:len(b)] == b

class Reject(Exception):
    pass

class AWOL(Exception):
    def dstate(self):
        return self.args[0]

class Deps(dict):
    def workers(self, dep):
        _, completed = self[dep]
        return set(worker for worker, _, _ in completed)

class Job(object):
    def __init__(self, conf, id=None):
        self.conf = conf
        self.jobspace = conf.jobspace()
        self.id = id

    def __enter__(self):
        if not self.id:
            self.id = time.strftime('%Y%m%d-%H%M%S-') + uuid.uuid4().hex
        self.conf['jobid'] = self.id
        self.jobspace.subspace(self.id)
        return self

    def __exit__(self, *args):
        self.conf.pop('jobid') # cleanup

    def __str__(self):
        return self.id

    def status(self, qubit, qbdict):
        target, deps = qbtarget(qubit), qbdeps(qubit)
        cards = self.cache[target]
        completed, active, rejected = [], [], 0
        for worker, attempts in cards.items():
            for i, (t, values) in attempts.items():
                if values[-1] == 1:
                    completed.append((worker, i, (t, values)))
                elif values[-1] == 0:
                    active.append((worker, i, (t, values)))
                elif values[-1] < 0:
                    rejected += 1
        if completed:
            return 'completed', completed
        if active:
            return 'active', active
        if rejected >= conf.expand('failed'):
            return 'failed', rejected

        dstatii = [self.status((d, qbdict[d]), qbdict) for d in deps]
        dstates = zip(deps, dstatii)
        if all(tag == 'completed' for tag, _ in dstatii):
            return 'ready', dstates
        if any(tag == 'failed' for tag, _ in dstatii):
            return 'blocked', dstates
        return 'waiting', dstates

    def sync(self, up=False, down=False):
        self.jobspace.sync(self.id, up, down)
        if down: # safer to always update cache, but faster not to
            self.cache = self.punch_cards()

    def punch_cards(self):
        return self.jobspace.punch_cards(self.id)

    def punch_clock(self, target, state, code):
        if code >= -2:
            worker, i = '.', state
            value = code
        else:
            worker, i, (t, values) = state
            values.append(code) # updates cache
            value = values
        self.jobspace.punch_clock(self.id, target, worker, i, value)
        self.sync(up=True, down=False)

    def loop(self, qubits):
        idle = 0
        interval = conf['interval']
        stalled = conf['stalled']
        qubits = list(qubits)
        qbdict = dict(qubits)
        formers = dict()
        rejects = set()
        for i in count():
            log("@ %8d" % i, v=2)
            busy = False
            completed = 0
            if idle:
                time.sleep(interval + randint(0, interval))
            self.sync(down=True)
            for qubit in qubits:
                target = qbtarget(qubit)
                tag, state = self.status(qubit, qbdict)
                if formers.get(target) != tag:
                    log("%12s: %s" % (tag, target))
                formers[target] = tag
                if target in rejects:
                    continue
                elif tag == 'completed':
                    completed += 1
                elif tag == 'active':
                    for att in state:
                        worker, i, (t, values) = att
                        if t - time.time() > stalled and dead(worker):
                            self.punch_clock(target, att, -3)
                elif tag == 'ready':
                    try:
                        self.punch_clock(target, i, 0)
                        qbcall(qubit, state)
                        self.punch_clock(target, i, +1)
                    except Reject:
                        rejects.add(target)
                        log(format_exc(), v=None)
                        self.punch_clock(target, i, -1)
                    except AWOL, e:
                        dep, (_tag, atts) = e.dstate()
                        log("%12s: %s" % ('awol', dep))
                        self.punch_clock(target, i, -2)
                        self.punch_clock(dep, atts[-1], -4)
                    else:
                        self.sync(down=True)
                    busy = True
                elif tag == 'waiting':
                    pass
                elif tag == 'failed' or tag == 'blocked':
                    return # game over
            if completed == len(qubits) - len(rejects):
                return # done
            idle = 0 if busy else idle + 1

    @classmethod
    def active(cls):
        return cls(conf, conf['jobid'])

class JobSpace(object):
    def __new__(cls, url, *args):
        if cls is JobSpace:
            if url.startswith('s3://'):
                return JobSpace.__new__(S3JobSpace, url, *args)
            return JobSpace.__new__(FileJobSpace, url, *args)
        return super(JobSpace, cls).__new__(cls, url, *args)

    def __init__(self, url, worker, qspace):
        self.url = url
        self.worker = worker
        self.qspace = qspace

    def __repr__(self):
        return '%s(%r, %r)' % (type(self).__name__, self.url, self.worker)

class FileJobSpace(JobSpace):
    def __init__(self, url, *args):
        JobSpace.__init__(self, url, *args)
        self.path = self.url

    def clean(self):
        if os.path.exists(self.path):
            rmtree(self.path)
        return self.path

    def punch_cards(self, jobid):
        dd = lambda t: lambda: defaultdict(t)
        raw = defaultdict(dd(dd(dd(list))))
        cards = defaultdict(dd(dict))
        times = defaultdict(dd(dict))
        subdir = os.path.join(self.path, jobid)
        for qwstr in os.listdir(subdir):
            worker = wparse(unquote_plus(qwstr))
            for line in open(os.path.join(subdir, qwstr)):
                t, target, oworker, i, value = line.strip().split('\t')
                t = float(t)
                i = int(i)
                if oworker == '.':
                    raw[worker][oworker][target][i].append(int(value))
                    times[target][worker][i] = t
                else:
                    raw[worker][wparse(oworker)][target][i] = map(int, value.split(','))
                    times[target][worker][i] = times[target][worker].get(i, t)
        for worker, oworkers in raw.items():
            me = oworkers.pop('.', {})
            for target, attempts in me.items():
                for i, vclock in attempts.items():
                    cards[target][worker][i] = (times[target][worker][i], vclock)
            for oworker, targets in oworkers.items():
                for target, attempts in targets.items():
                    for i, vclock in attempts.items():
                        t_ = times[target][worker][i]
                        t, orig = cards[target][worker].get(i, (t_, []))
                        if vclock_gte(vclock, orig): # NB: could wait for 'quorum'
                            cards[target][worker][i] = (t, vclock)
        return cards

    def punch_clock(self, jobid, target, worker, i, value):
        with open(os.path.join(self.path, jobid, quote_plus(wformat(self.worker))), 'a') as clock:
            val = value if worker == '.' else ','.join(str(v) for v in value)
            wrk = worker if worker == '.' else wformat(worker)
            clock.write('%s\t%s\t%s\t%d\t%s\n' % (time.time(), target, wrk, i, val))

    def subspace(self, jobid):
        sh(('mkdir', '-p', os.path.join(self.path, jobid))).wait()

    def last(self):
        return sorted(p for p in os.listdir(self.path) if p != '-')[-1]

    def sync(self, jobid, up, down):
        pass

class S3JobSpace(FileJobSpace):
    def __init__(self, url, *args):
        FileJobSpace.__init__(self, url, *args)
        self.path = os.path.join(self.qspace, '-', quote_plus(self.url))

    def clean(self):
        FileJobSpace.clean(self)
        aws('s3', 'rm', '--recursive', self.url)
        return self.url

    def sync(self, jobid, up, down):
        host, pid = self.worker
        wpath = os.path.join(quote_plus(wformat((host, pid))))
        wpre = os.path.join(quote_plus(wformat((host, ''))))
        if up:
            aws('s3', 'cp',
                os.path.join(self.path, jobid, wpath),
                os.path.join(self.url, jobid, wpath))
        if down:
            aws('s3', 'sync', '--exclude', '*/' + wpre + '*',
                os.path.join(self.url, jobid),
                os.path.join(self.path, jobid))

class Config(dict):
    def __call__(self, key):
        def store(val):
            self[key] = val
            return val
        return store

    def expand(self, key, default=None):
        maybe = self.get(key, default)
        return maybe() if callable(maybe) else maybe

    def jobdir(self, id=None):
        id = id or self['jobid']
        return os.path.join(self['jobroot'], self.get('jobprefix', '') + id)

    def jobspace(self, url=None):
        if url is None:
            return self.get('jobspace') or self.jobspace(self['qspace'])
        return self('jobspace')(JobSpace(url, self['worker'], self['qspace']))

conf = Config({
    'parent': None,
    'profile': None,
    'qpack': '.qpack',
    'qubits': '.qubits',
    'qspace': '.qspace',
    'failed': lambda: sum(nmax for _, nmax in conf.expand('nodes')),
    'interval': 10,
    'stalled': 20 * 60,
    'jobroot': '/mnt',
    'jobprefix': 'qjob-',
    'nodes': [('localhost', 2)],
    'worker': (socket.gethostname(), str(os.getpid())),
    'spawnlog': 'spawn.log',
})
rules = []

def rule(regexp, deps=None, rules=rules):
    pattern = re.compile(regexp)
    def recipe(do):
        rules.append((pattern, deps, do))
        return do
    return recipe

def qbread(lines, rules=rules):
    for line in lines:
        yield qbparse(line, rules)

def qbparse(line, rules=rules):
    _name, target, deps = line.strip('\n').split('\t')
    _deps, do = match(target, rules=rules)
    return target, (deps.split(' ') if deps else [], do)

def qbformat((target, (deps, do))):
    return "%s\t%s\t%s\n" % (do.__name__, target, ' '.join(deps))

def qbdumps(qubits):
    return ''.join(qbformat(qubit) for qubit in qubits)

def qbtarget((target, (deps, do))):
    return target

def qbdeps((target, (deps, do))):
    return deps

def qbname((target, (deps, do))):
    return do.__name__

def qbcall((target, (deps, do)), dstates):
    return do(target, Deps(dstates)) if deps else do(target)

def wparse(wstr):
    return tuple(wstr.split(':'))

def wformat(worker):
    return '%s:%s' % worker

def expand(deps, m=None):
    if callable(deps):
        return deps(*(m.groups() if m else ()))
    if isinstance(deps, basestring):
        return deps,
    return deps or ()

def match(target, rules=rules):
    for pattern, deps, do in rules:
        m = pattern.match(target)
        if m:
            return expand(deps, m), do
    raise ValueError("Don't know how to make '%s'" % target)

def qubits_(target, qubits=None, ancestors=(), rules=rules):
    qubits = qubits or {}
    priors = ancestors + (target,)
    deps, do = match(target, rules=rules)
    qubits[target] = deps, do
    for dep in deps:
        if dep in priors:
            warn("Dropping circular dependency: %s, %s" % (priors, dep), Warning)
            del qubits[target]
        else:
            qubits = qubits_(dep, qubits, priors, rules)
    return qubits

def qubits(targets=(), rules=rules):
    return sum((qubits_(t, rules=rules).items() for t in targets or ('default',)), [])

def make(targets=()):
    with Job(conf, id=conf['parent']) as job:
        job.loop(qubits(targets, rules))
    return job

def pack(targets=()):
    qp = conf['qpack']
    qs = conf['qubits']
    def ignored(path, globs=[l.strip() for l in conf.expand('ignore', [])]):
        return any(fnmatch(path, i) for i in globs + ['*.pyc', '.q*', 'Qfilec'])
    def ignore(dir, names):
        return [n for n in names if ignored(n) or dotfile(n) or n == qp]
    if os.path.exists(qp):
        rmtree(qp)
    copytree('.', qp, symlinks=True, ignore=ignore)
    with open(os.path.join(qp, qs), 'w') as file:
        file.write(qbdumps(qubits(targets)))
    return qp

def seed(targets=()):
    qd = dict(qbread(open(conf['qubits'])))
    qb = [t for t in qd if t not in targets]
    ts = chain(targets, sample(qb, len(qb)))
    with Job(conf, id=conf['parent']) as job:
        job.loop(((t, qd[t]) for t in ts))
    return job

def sync(jobid=None):
    jobid = jobid or conf.jobspace().last()
    with Job(conf, id=jobid) as job:
        job.sync(down=True)
    return job

def spawn(jobid, qpack=None):
    qp = qpack or conf['qpack']
    qs = conf['qubits']
    sl = conf['spawnlog']
    ps = sum(([(addr, [])] * nmax for addr, nmax in conf.expand('nodes')), [])
    qs = qbread(open(os.path.join(qp, qs)))
    for n, qubit in enumerate(q for q in qs if not qbdeps(q)):
        ps[n % len(ps)][1].append(qbtarget(qubit))
    with Job(conf, id=jobid) as job:
        flags = '-j %s' % job.id
        if conf.get('profile'):
            flags += ' -p %s' % conf['profile']
        if conf.get('verbose'):
            flags += ' -' + 'v' * conf['verbose']
        def plant(targets):
            return '(nohup ./qb.py seed %s %s >> %s 2>&1 &)' % (flags, ' '.join(targets), sl)
        pssh(((addr, 'cd %s; %s; echo ok' %
               (conf.jobdir(job.id), '; '.join(plant(ts) for _addr, ts in group)))
              for addr, group in groupby(ps, lambda (k, v): k)))
    return job

def share(qpack=None):
    qp = qpack or conf['qpack']
    with Job(conf, id=conf['parent']) as job:
        pscp(qp + '/',
             ('%s:%s' % (addr, conf.jobdir(job.id))
              for addr, nmax in conf.expand('nodes')),
             scp='rsync -az')
    return job

def kill(jobish=None, signal='KILL'):
    flags = ('-j %s' % jobish) if jobish else ''
    match = r'\"qb.py seed %s\"' % flags
    pssh((addr, r'ps x -o \"%%r,%%a\" | grep %s | grep -v grep | cut -f 1 -d , | xargs -n 1 pkill -e -%s -g' % (match, signal or 'KILL'))
         for addr, _nmax in conf.expand('nodes'))

def run(targets=()):
    qpack = pack(targets)
    return spawn(share(qpack).id, qpack)

def load(filename='Qfile'):
    import imp
    return imp.load_source('Qfile', filename)

def cli_conf():
    for k in sorted(conf):
        print('%12s:\t%r' % (k, conf.expand(k)))

def cli_last():
    print(conf.jobspace().last())

def cli_qubits(*targets):
    for qubit in qubits(targets):
        sys.stdout.write(qbformat(qubit))

def cli_make(*targets):
    make(targets)

def cli_pack(*targets):
    print(pack(targets))

def cli_seed(*targets):
    print(seed(targets))

def cli_sync(jobid=None):
    print(sync(jobid))

def cli_stat(jobid=None):
    job = sync(jobid or conf.jobspace().last())
    for target, workers in job.cache.items():
        for worker, attempts in workers.items():
            for i, (t, values) in attempts.items():
                print("%.2f\t%30s\t%50s\t%10s" % (t, wformat(worker), target, values))

def cli_spawn(jobid, qpack=None):
    print(spawn(jobid, qpack=None))

def cli_share(qpack=None):
    print(share(qpack))

def cli_pssh(command):
    pssh((addr, command) for addr, _nmax in conf.expand('nodes'))

def cli_kill(jobish=None, signal=None):
    kill(jobish, signal)

def cli_run(*targets):
    print(run(targets))

def cli_clean():
    print(conf.jobspace().clean())

def cli_help(*args):
    print(__doc__.strip())

def main():
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('-f', '--Qfile',
                        help="the path of the Qfile",
                        default='Qfile')
    parser.add_argument('-j', '--parent',
                        help="the parent job")
    parser.add_argument('-p', '--profile',
                        help="the profile of the config")
    parser.add_argument('-v', '--verbose',
                        action='count',
                        help="enable verbose output")
    opts, args = parser.parse_known_args(sys.argv[1:])
    cmd, args = args[0] if args else 'help', args[1:]
    parent = conf['parent'] = opts.parent
    profile = conf['profile'] = opts.profile or ('dist' if cmd == 'run' else None)
    verbose = conf['verbose'] = opts.verbose
    Qfile = load(opts.Qfile)
    eval('cli_' + cmd)(*args)

if __name__ == '__main__':
    sys.modules['qb'] = sys.modules['__main__'] # NB: horrible import hack
    main()
