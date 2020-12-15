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

The library should work with the `Agda <http://github.com/agda/agda>`__
latest version, and it tested with (v 2.6.1).

.. code:: bash

   $ git clone http://github.com/jonaprieto/mini-hott

For newcomers, the easiest way to install a library is using
`agda-pkg <http://github.com/agda/agda-pkg>`__

You can run the following commands to install it:

.. code:: bash

   $ pip3 install agda-pkg
   $ apkg init
   $ apkg install --github jonaprieto/mini-hott

After installing the sources, include at the top of your file the
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
   src/SectionsAndRetractions
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


