Qubits
======

Qubits is a nano-framework for distributed computing.
Qubits is specifically designed for building complex data pipelines.
The Qubits model can also be applied to the physical world for task coordination.

There are no hard dependencies beyond what most *nix systems provide out of the box.
However, if you want to use Qubits seriously you'll probably need to install the aws cli.

There are a few core ideas behind the design of Qubits:

1. Running a master *node* (i.e. one that is capable of computation) is annoying.
   It should not be the users responsibility to maintain a master.

2. Clusters are personal.
   It's so easy to run an ephemeral cluster nowadays, you might as well have your own.

3. In a personalized distributed system, your client + a storage medium can replace the master.
   By analogy, the physical world is the keeper of state, not a single person.
   Most of the time you just care how things look like from your POV.

4. Nodes should opt-in to doing work.
   Noone needs to keep a list of working nodes, nodes just compute what they feel like.

Qubits assumes you already have a bunch of nodes, and you want to make them do something.
You must be able to ssh into the nodes.

Coordination of nodes relies on a very simple API that can be provided by most storage systems.
Your local filesystem (single node), or S3, work perfectly well.
Qubits provides *jobspaces* (backends) for these two out of the box.

So what does Qubits do?
-----------------------

Qubits compiles a file you write, called a Qfile (a lot like a Makefile), into a list of qubits.
Each qubit is a unit of work that can be done by a node.

Your Qfile describes the work that needs to get done, and all the configuration for your project.
The work is expressed as a set of targets and dependencies, i.e. a directed acyclic graph.

Within the same directory as the Qfile, you can keep all the code needed to run your targets.
Qubits will simultaneously sync your code with the nodes when it's time to run.
One cool feature about a Qfile vs a Makefile, is that dependencies can be generated by functions.
Dynamic targets & dependencies alone would be a leap forward for building data pipelines!

Qubits will also help you run jobs made of distributed qubits.
For convenience, you can configure which nodes you want to ask to work on jobs in the Qfile.
When you run a job, the nodes are seeded with entry point targets.
The nodes keep doing work, until there's nothing left to do.

How do I use Qubits?
--------------------

Get `qb.py`, put it in your project root.

In this doc we'll assume you also do something like::

   alias qb=./qb.py

You should put a Qfile in the same directory, perhaps something like this::

  https://gist.github.com/jflatow/357cd823081b66615630

Check your configuration::

  qb conf

Assuming you have a target named *default* in your Qfile, type::

  qb make

You just made your targets and ran your qubits locally.
Want to see it in slow motion? Type::

  qb make -v

Want to run in your cluster?
Make sure you configure your **nodes** in your Qfile.
You can set a function up to do whatever you want, e.g. read from a file, or ask Amazon.

You might also configure the **jobspace** to be an S3 url.
If that is the case, make sure the aws cli is installed, with appropriate credentials.

Now, for the moment of truth. Type::

  qb run -v

Yay, that's it!

If you want more, check `qb.py` for a brief description of the CLI commands, or type::

  qb

What's a nano-framework?
-------------------------------

I'm not sure, but this README is almost as big as the code-base.
