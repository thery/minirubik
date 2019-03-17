[![Build Status](https://travis-ci.org/thery/minirubik.svg?branch=master)](https://travis-ci.org/thery/minirubik)

## MiniRubik

This is a certified solver for the Rubik 2x2

The formalisation is explained in the file `paper.pdf`,

A position of the cube is encoded by the constructor
``State`` that takes 7 cubes (``C1``, ``C2``, ``C3``, ``C4``, ``C5``, ``C6``, ``C7``)
and their respective orientation (``O1`` ``O2`` ``O3``).

For example, the initial configuration is

``State C1 C2 C3 C4 C5 C6 C7 O1 O1 O1 O1 O1 O1 O1``

Swapping two adjacent corners gives:

``State C2 C1 C3 C4 C5 C6 C7 O1 O1 O1 O1 O1 O1 O1``

Swapping two opposite corners gives

``State C7 C2 C3 C4 C5 C6 C1 O1 O1 O1 O1 O1 O1 O1``

The ``solve`` function takes a position and returns
a list of minimal length to return to the initial
position.
