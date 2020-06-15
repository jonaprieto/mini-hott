Mini-HoTT   |Build Status| |GitHub issues| |MIT license| |GitHub tag|
=====================================================================

Mini-HoTT is a basic `Agda <http://github.com/agda/agda>`__ library that
contains basic definitions and results in `Univalent type
theory <http://homotopytypetheory.org/>`__.

-  Website documentation: http://jonaprieto.github.io/mini-hott
-  Source repository: http://github.com/jonaprieto/mini-hott

Quick start
-----------

Installation
~~~~~~~~~~~~

The only prerequisite is to have installed the latest version of
`Agda <http://github.com/agda/agda>`__ and one text editor with Agda
support, e.g., Emacs or Atom. If you know about the library management
in Agda, install as usual this library after cloning the sources by
running the following command.

.. code:: bash

   $ git clone http://github.com/jonaprieto/mini-hott

For newcomers, the easiest way to install a library is by using
`agda-pkg <http://github.com/agda/agda-pkg>`__, the package manager for
Agda. Then, run one of the following commands.

.. raw:: html

   <!-- tabs:start -->

\*\* Stable version \*\*
^^^^^^^^^^^^^^^^^^^^^^^^

.. code:: bash

   $ apkg install mini-hott

\*\* Latest version \*\*
^^^^^^^^^^^^^^^^^^^^^^^^

.. code:: bash

   $ apkg install --github jonaprieto/mini-hott

\*\* Apkg installation \*\*
^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. code:: bash

   $ pip3 install agda-pkg
   $ apkg init

.. raw:: html

   <!-- tabs:end -->

After installing the sources, just include in your code at the top the
following line:

-  ``open import MiniHoTT``

.. toctree::
   :maxdepth: 2
   :glob:

   src/*
   
Contributors
------------

Collaborations are always welcomed. At the moment, this library is
supported by Jonathan Prieto-Cubides at the `University of
Bergen <https://www.uib.no/>`__. Mini-HoTT grows with ideas from
discussions among the following people.

-  `Jonathan Prieto-Cubides <mailto:jonathan.cubides@uib.no>`__ (code)
-  `Håkon Robbestad Gylterud <https://hakon.gylterud.net>`__
-  `Marc
   Bezem <https://cas.oslo.no/fellows/marc-bezem-article2086-828.html>`__
-  `Agda mailing
   list <https://lists.chalmers.se/mailman/listinfo/agda>`__

To improve this project, please open an `issue on
Github <https://github.com/jonaprieto/mini-hott/issues>`__.

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


