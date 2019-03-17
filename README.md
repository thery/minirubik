[![Build Status](https://travis-ci.org/thery/minirubik.svg?branch=master)](https://travis-ci.org/thery/minirubik)

## MiniRubik

This is a certified solver for the Rubik 2x2

The formalisation is explained in the file [paper.pdf](https://github.com/thery/minirubik/blob/master/paper.pdf),

A position of the cube is encoded by the constructor
``State`` that takes 7 cubes (`C1`, `C2`, `C3`, `C4`, `C5`, `C6`, `C7`)
and their respective orientation (`O1`, `O2`, `O3`).

For example, the initial configuration is

``State C1 C2 C3 C4 C5 C6 C7 O1 O1 O1 O1 O1 O1 O1``

Swapping two adjacent corners gives:

``State C2 C1 C3 C4 C5 C6 C7 O1 O1 O1 O1 O1 O1 O1``

Swapping two opposite corners gives

``State C7 C2 C3 C4 C5 C6 C1 O1 O1 O1 O1 O1 O1 O1``

There are 3 positive moves that corresponds to the right face, the back face and the down face.
Each move can be applied once (`Right`, `Back`, `Down`),
twice (`Right2`, `Back2`, `Down2`) or three times
(`Rightm1`, `Backm1`, `Downm1`) and is still considered
as a single move.

For example, applying the move `Right` to the initial
configuration gives

``State C2 C5 C3 C1 C4 C6 C7 O2 O3 O1 O3 O2 O1 O1``

The ``solve`` function takes a position and returns
a list of minimal length of the moves to return to
the initial position.

For example, solving

``State C2 C1 C3 C4 C5 C6 C7 O1 O1 O1 O1 O1 O1 O1``

returns a list of length 11

``Right :: Backm1 :: Down2 :: Rightm1 :: Back
:: Rightm1 :: Backm1 :: Right :: Down2 :: Right :: Back :: nil``

Other examples are given in the file [Example.v](https://github.com/thery/minirubik/blob/master/Example.v)
