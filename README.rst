Mini-HoTT   |Build Status| |GitHub issues| |MIT license| |GitHub tag|
=====================================================================

Mini-HoTT is a basic `Agda <http://github.com/agda/agda>`__ library which
contains basic definitions and results in `Univalent type
theory <http://homotopytypetheory.org/>`__. There is no guarantee whatsoever
of any kind. At the moment, this library suffers of many changes without any warning.

-  Website documentation: https://mini-hott.readthedocs.io/

Quick start
-----------

Installation
~~~~~~~~~~~~

The only prerequisite is to have installed the latest version of
`Agda <http://github.com/agda/agda>`__ and a text editor with Agda
support, e.g., Emacs or Atom. Then, you can install the library
as usual after cloning the sources by running the following command.

.. code:: bash

   $ git clone http://github.com/jonaprieto/mini-hott

For newcomers, the easiest way to install a library is using
`agda-pkg <http://github.com/agda/agda-pkg>`__
You can run the following commands to install it:

.. code:: bash

   $ pip3 install agda-pkg
   $ apkg init
   $ apkg install --github jonaprieto/mini-hott

After installing the sources, just include in your code at the top the
following line:

.. code:: agda
   
   open import MiniHoTT

.. toctree::
   :caption: Table of Contents
   :maxdepth: 2
   
   src/Intro
   src/MiniHoTT
   src/BasicTypes
   src/BasicFunctions
   src/DecidableEquality
   src/AlgebraOnPaths
   src/AlgebraOnDependentPaths
   src/Transport
   src/TransportLemmas
   src/CoproductIdentities
   src/DependentAlgebra
   src/FibreType
   src/Fibrewise
   src/HomotopyType
   src/HomotopyLemmas
   src/EquivalenceType
   src/QuasiinverseType
   src/QuasiinverseLemmas
   src/BiinverseEquivalenceType
   src/HalfAdjointType
   src/EquivalenceReasoning
   src/BasicEquivalences
   src/PiPreserves
   src/SigmaPreserves
   src/SigmaEquivalence
   src/UnivalenceAxiom
   src/FunExtAxiom
   src/UnivalenceLemmas
   src/UnivalenceIdEquiv
   src/UnivalenceTransport
   src/FunExtTransport
   src/FunExtTransportDependent
   src/HLevelTypes
   src/HedbergLemmas
   src/HLevelLemmas
   src/TypesofMorphisms
   src/Rewriting
   src/SetTruncationType
   src/ProductIdentities
   src/SuspensionType
   src/IntervalType
   src/TruncationType
   src/QuotientType
   src/CircleType
   src/FundamentalGroupType
   src/MonoidType
   src/RelationType
   src/IntegerType
   src/GroupType
   src/NaturalType
   src/Connectedness
   src/TheAxiomOfChoice


Contributors
------------

Collaborations are always welcomed. At the moment, me,
Jonathan Prieto-Cubides, I'm using the library to type-check
my proofs for my research project at the `University of
Bergen <https://www.uib.no/>`__.

-  `Jonathan Prieto-Cubides <mailto:jonathan.cubides@uib.no>`__ 

People involved in making this library better, although not directly involved are:

-  `Håkon Robbestad Gylterud <https://hakon.gylterud.net>`__
-  `Marc
   Bezem <https://cas.oslo.no/fellows/marc-bezem-article2086-828.html>`__
-  People from the `Agda mailing
   list <https://lists.chalmers.se/mailman/listinfo/agda>`__

References
----------

-  Theory

   -  The Univalent Foundations Program. `Homotopy Type Theory:
      Univalent Foundations of
      Mathematics <http://homotopytypetheory.org>`__. 2013.
   -  The Homotopy Type Theory and Univalent Foundations CAS project.
      `Symmetry Book <https://github.com/UniMath/SymmetryBook>`__. 2020.
   -  Escardo, M. `Introduction to Univalent Foundations of Mathematics
      with
      Agda <https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/>`__.
      2019.
   -  Rikje, E. `Introduction to Homotopy Type
      Theory <https://github.com/EgbertRijke/HoTT-Intro>`__. 2019.

-  Implementation:

   -  `Agda-HoTT <https://mroman42.github.io/ctlc/agda-hott/Total.html>`__
   -  `Agda-premises <https://hub.darcs.net/gylterud/agda-premises>`__
   -  `HoTT-Agda <https://hott.github.io/HoTT-Agda/>`__
   -  `Agda-Base <https://github.com/pcapriotti/agda-base>`__

.. |Build Status| image:: https://travis-ci.org/jonaprieto/mini-hott.svg?branch=master
   :target: https://travis-ci.org/jonaprieto/mini-hott
.. |GitHub issues| image:: https://img.shields.io/github/issues/jonaprieto/mini-hott.svg
   :target: https://GitHub.com/jonaprieto/mini-hott/issues/
.. |MIT license| image:: https://img.shields.io/badge/License-MIT-blue.svg
   :target: https://lbesson.mit-license.org/
.. |GitHub tag| image:: https://img.shields.io/github/tag/jonaprieto/mini-hott.svg
   :target: https://GitHub.com/jonaprieto/mini-hott/tags/


