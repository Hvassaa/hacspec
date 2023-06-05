Hi, we are trying to run an example of the protocol with these values. We believe all these values
are valid, but the check in the final step fails. If you have time, we would really appreciate if 
you could validate, that we do not do not use anything invalid. :-)

n = 4
n_a = 3
n_q = 2
n_g = 4
ω = 4265513433803163958251475299683560813532603332905934989976535652412227143402
(or in hex 96E31EEA5205EE7829A559CEC3CAB14D83233F67234D59A2F17C7C5B54146EA)

Let us call the generator
(1, 12418654782883325593414442427049395787963493412651469444558597405572177144507)
(or in hex  (1, 1B74B5A30A12937C53DFA9F06378EE548F655BD4333D477119CF7A23CAED2ABB))
for the Pallas-curve "gen".
(from https://o1-labs.github.io/proof-systems/specs/pasta.html#pallas:)

pp = (
   Group = the pallas-curve,
   field = scalar-field for pallas,
   G = [22*gen, 7*gen, 9*gen, 43*gen],
   U = 743*gen,
   W = 123*gen
)
and the CRS for Pedersen Vector commitments = (
   Group = as above
   G = as above,
   H = W from above,
   field = as aboe,
)

We use the circuit: (inspired by https://www.youtube.com/watch?v=7eaRAQmFueA)
 
| i | a_0 | a_1 | a_2 | q_add |
|---|-----|-----|-----|-------|
| 0 | 2   | 3   | 5   | 1     |
| 1 | 10  |     |     | 0     |
| 2 | 5   | 8   | 13  | 1     |
| 3 | 26  |     |     | 0     |

The $a_i$'s are determined with lagrange interpolation.
g(X) = q_add(X) * (a_0(X) + a_1(X) + a_2(X) - a_0(ωX))
*p* = [{0,1}, {0}, {0}]
*q* = [{0}, {0,1}]

(Are we right to assume that the $C_i$ challenges in step 1 can be omitted
for simplicity, so that $a_i = a'_i$ and $g = g'$?)

$r(X)$ (step 3) is set to $987 + 2x + 64x^2 + 355x^3$.

$s(X)$ (step 20) is determined with lagrange interpolation over the points:
[(729, 23), (73, 102), (444, 484), ($x_3$, 0)]

Then we have a number of challenges:

* $x$ = 345
* $x_1$ = 475
* $x_2$ = 286
* $x_3$ = 175
* $x_4$ = 391
* $\xi$ = 98
* $z$ = 8438
* $u$ = [723, 9283] (for step 24)

and blindess:

* step 1: [99, 123, 748] (for $A_j$'s)
* step 3: 78
* step 6: [5, 76, 726] (for $H_i$'s)
* step 14: 32
* step 20: 532
