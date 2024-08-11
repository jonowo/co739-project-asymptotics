# CO 739 Project: Asymptotics

Submitted by Jonathan Leung (j23leung@uwaterloo.ca).

This project is motivated by the discussion of order notation
in CS 240 Data Structures and Data Management. Order notation
is used to express relations between growth rates of functions.
In Computer Science, order notation is most known for its use
in algorithm analysis, to quantify the efficiency of algorithm
in terms of runtime and space.

We formalize Big O notation and friends, prove a number of
properties about them, and finally put our theorems to work in
two assignment questions.

Contents of `Co739ProjectAsymptotics/Asymptotics.lean`:
- Definitions for Big O, Big $\Omega$, Big $\Theta$,
  little o and little $\omega$ notation.
- 13 theorems about relationships between order notations,
  transitivity, addition and maximum rules.
- 2 assignment questions on proving $\Theta$-bounds:
  for positive functions $f, g$ and $h$,
    - if $f(n), h(n) \in \Theta(g(n))$,
      then $\frac{f(n)}{h(n)} \in \Theta(1)$.
    - $\min(f(n), g(n)) \in \Theta
       \left(\frac{f(n)g(n)}{f(n) + g(n)}\right)$.
