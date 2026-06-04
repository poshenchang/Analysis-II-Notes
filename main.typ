#import "typst/packages/preview/mousse-notes/1.1.0/src/lib.typ": *
#import "@preview/xarrow:0.3.1": xarrow

#let smallcaps-strong = it => smallcaps(strong(it))
#let claim = thm-env("Claim", fmt: smallcaps-strong, body-fmt: emph)

// override default numbering-internal for theorem-like environments
#let theorem = theorem.with(numbering-internal: "(i)")
#let proposition = proposition.with(numbering-internal: "(i)")
#let lemma = lemma.with(numbering-internal: "(i)")
#let corollary = corollary.with(numbering-internal: "(i)")
#let definition = definition.with(numbering-internal: "(i)")
#let example = example.with(numbering-internal: "(i)")
#let remark = remark.with(numbering-internal: "(i)")
#let proof = proof.with(numbering-internal: "(i)")
#let claim = thm-env("Claim", fmt: smallcaps-strong, body-fmt: emph).with(numbering-internal: "(i)")

#set page(paper: "us-letter")
#show: book.with(
  title: [Analysis II],
  subtitle: [Lecture Notes],
  author: "Poshen Chang",
  font-style: "serif",
)

#set enum(numbering: "(i)")

#let varinjlim = math.accent(math.lim, sym.arrow.r.long)
#let iff = math.arrow.l.r.double.long


#outline(indent: auto)
#pagebreak()

= Lebesgue Measure

This chapter is devoted to the construction of Lebesgue measure in $RR^d$ and the study of the resulting class of measurable functions. 

== Preliminaries

The goal of this section is to construct a measure on $RR$, which assigns to each subset $E$ of $RR$ a non-negative number $m(E)$, such that

+ $m(E) = b - a$ if $E$ is an interval $[a, b]$;
+ $m$ is countably additive, i.e., 
$ 
m(union.big_(n=1)^oo E_n) = sum_(n=1)^oo m(E_n)
$
for any sequence of disjoint sets $E_1, E_2, ...$;
+ $m$ is translation invariant, i.e., $m(E + x) = m(E)$ for any $x in RR$.

A (closed) rectangle in $RR^d$ is a set of the form
$ 
R = [a_1, b_1] times [a_2, b_2] times dots.c times [a_d, b_d].
$
The volume of $R$ is defined to be
$ 
|R| = (b_1 - a_1)(b_2 - a_2) dots.c (b_d - a_d).
$
A cube is a rectangle with $b_1 - a_1 = b_2 - a_2 = dots.c = b_d - a_d$. A union of rectangles is said to be almost disjoint if the interiors of the rectangles are disjoint.

#lemma[
    If a rectangle is the union of finitely many other rectangles $R_1, R_2, ..., R_N$ that are almost disjoint, then
    $ 
    |R| = |R_1| + |R_2| + dots.c + |R_N|.
    $
]
#proof[
    Consider the grid formed by extending the sides of the rectangles. The resulting grid divides the original rectangle into finitely many almost disjoint rectangles $R_1', R_2', ..., R_M'$ and a partition $J_1, J_2, ..., J_N$ of integers from $1$ to $M$, such that
    $ 
    R = union.big_(j=1)^M R_j'  quad "and" quad  R_k = union.big_(j in J_k) R_j' "for" k = 1, 2, ..., N.
    $
    Since the grid partitions the sides of $R$, by simply expanding the products we have
    $ 
    |R| = sum_(j=1)^M |R_j'|.
    $
    This also holds for each $R_k$, so
    $ 
    |R| = sum_(j=1)^M |R_j'| = sum_(k=1)^N sum_(j in J_k) |R_j'| = sum_(k=1)^N |R_k|.
    $
    $qed$
]

#lemma(id: "lm:rectangle_cover")[
    If $R, R_1, R_2, ..., R_N$ are rectangles and $R subset.eq union.big_(n=1)^N R_n$, then
    $ 
    |R| <= |R_1| + |R_2| + dots.c + |R_N|.
    $
]
#proof[
    We may employ the same grid as in the previous lemma, which partitions $R$ into almost disjoint rectangles $R_1', R_2', ..., R_M'$. $R$ can be written as a almost disjoint union of a subset of these rectangles, and each $R_j'$ is contained in some $R_n$. Therefore,
    $ 
    |R| <= sum_(j=1)^M |R_j'| <= sum_(n=1)^N |R_n|.
    $
    $qed$
]

If $cal(U)$ is open in $RR$, then $cal(U)$ can be written as a countable union of almost disjoint open intervals, say $cal(U) = union.big_(n=1)^oo I_n$. We define the measure of $cal(U)$ to be
$ 
m(cal(U)) = sum_(n=1)^oo |I_n|.
$
We wish to generalize this to higher dimensions. 

#proposition[
    Every open subset $cal(U) subset.eq RR^d$ can be written as a countable union of almost disjoint closed cubes.
]
#proof[
    At a first step, consider the grid formed by taking all closed cubes of side length $1$ with vertices in $ZZ^d$. We either accept or reject cubes $Q$ in the initial grid according to the following rule: if $Q$ is entirely contained in $cal(U)$ then we accept $Q$; if $Q$ intersects both $cal(U)$ and $cal(U)^c$ then we tentatively accept it; and if $Q$ is entirely contained in $cal(U)^c$ then we reject it.

    As a second step, we bisect the tentatively accepted cubes into $2^d$ cubes with side length $1/2$. We then repeat our procedure, by accepting the smaller cubes if they are completely contained in $cal(U)$, tentatively accepting them if they intersect both $cal(U)$ and $cal(U)^c$, and rejecting them if they are contained in $cal(U)^c$.

    This procedure is then repeated indefinitely, and (by construction) the resulting collection of all accepted cubes is countable and consists of almost disjoint cubes. To see why their union is all of $cal(U)$, we note that given $x in cal(U)$ there exists a cube of side length $2^(-N)$ (obtained from successive bisections of the original grid) that contains $x$ and that is entirely contained in $cal(U)$. Either this cube has been accepted, or it is contained in a cube that has been previously accepted. This shows that the union of all cubes in Q covers $cal(U)$.
    $qed$
]

We can try to define the measure of $cal(U)$ to be the sum of the volumes of the cubes in the decomposition. The subtle issue is that the decomposition of $cal(U)$ into cubes is not unique.

== Outer Measure

#definition[
    Let $E subset.eq RR^d$. The outer measure of $E$ is defined to be
    $ 
    m_*(E) = inf { sum_(n=1)^oo |Q_n| : E subset.eq union.big_(n=1)^oo Q_n },
    $
    where the infimum is taken over all countable collections of closed cubes ${Q_n}$ that cover $E$.
]

#example[
    - Let $Q$ be a closed cube. Since $Q$ covers itself, we have $m_*(Q) <= |Q|$. On the other hand, suppose $Q subset.eq union.big_(n=1)^oo Q_n$. Let $epsilon > 0$. Choose an open cube $S_j supset.eq Q_j$ such that $|S_j| <= (1 + epsilon)|Q_j|$. Then $Q subset.eq union.big_(n=1)^oo S_n$. Since $Q$ is compact, there exists a finite subcover $Q subset.eq union.big_(n=1)^N S_n$. By @lm:rectangle_cover, we have
    $ 
    |Q| <= sum_(n=1)^N |S_n| <= (1 + epsilon) sum_(n=1)^N |Q_n| <= (1 + epsilon) sum_(n=1)^oo |Q_n|.
    $
    Since $epsilon$ is arbitrary, we conclude that $m_*(Q) >= |Q|$. Therefore, $m_*(Q) = |Q|$.
    - Let $Q$ be an open cube. Since $overline(Q)$ covers $Q$, we have $m_*(Q) <= |overline(Q)| = |Q|$. On the other hand, for a closed cube $Q_0$ contained in $Q$, we have $m_*(Q) >= m_*(Q_0) = |Q_0|$. By letting $|Q_0| -> |Q|$, we conclude that $m_*(Q) >= |Q|$. Therefore, $m_*(Q) = |Q|$.
    - Let $R$ be a closed rectangle. We can argue similarly as in (a) to show that $m_*(R) >= |R|$. On the other hand, consider a grid formed by cubes of side length $1/k$. Let $cal(Q)$ be the collection of cubes that are entirely contained in $R$, and let $cal(Q)'$ be the collection of cubes that intersect both $R$ and $R^c$. Note that
    $ 
    sum_(Q in cal(Q)) |Q| <= |R|
    $
    and $R subset.eq union.big_(Q in cal(Q)) Q union union.big_(Q in cal(Q)') Q$. Since there are at most $O(k^(d-1))$ cubes in $cal(Q)'$, we have $sum_(Q in cal(Q)') |Q| = O(1/k)$. By letting $k -> oo$, we conclude that $m_*(R) = |R|$.
    + $m_*(RR^d) = oo$ since every cube is contained in $RR^d$, and these cubes can have arbitrarily large volume.
    + The Cantor set $cal(C)$ has zero outer measure. This follows from the construction of $cal(C)$, where $cal(C) subset.eq C_k$ for each $k$, and each $C_k$ is a disjoint union of $2^k$ closed intervals of length $3^(-k)$. 
]

#proposition[
    For every $epsilon > 0$, there exists a covering $E subset.eq union.big_(n=1)^oo Q_n$ by closed cubes such that
    $ 
    sum_(n=1)^oo m_*(Q_n) <= m_*(E) + epsilon.
    $
]
#proof[
    Follows from the definition of $m_*(E)$ as an infimum and $|Q_n| = m_*(Q_n)$ for closed cubes $Q_n$.
    $qed$
]

#proposition(name: "Monotonicity")[
    If $E subset.eq F$, then $m_*(E) <= m_*(F)$.
]
#proof[
    Follows immediately from the definition of $m_*$ as an infimum over a set of coverings.
    $qed$
]

#proposition(name: "Countable Subadditivity")[
    If $E = union.big_(n=1)^oo E_n$, then $m_*(E) <= sum_(n=1)^oo m_*(E_n)$.
]
#proof[
    First assume that $m_*(E_n) < oo$ for each $n$. Given $epsilon > 0$, for each $n$ there exists a covering $E_n subset.eq union.big_(k=1)^oo Q_(n, k)$ such that
    $ 
    sum_(k=1)^oo m_*(Q_(n, k)) <= m_*(E_n) + epsilon/2^n.
    $
    Then $E subset.eq union.big_(n=1)^oo union.big_(k=1)^oo Q_(n, k)$ and
    $ 
    sum_(n=1)^oo sum_(k=1)^oo m_*(Q_(n, k)) <= sum_(n=1)^oo (m_*(E_n) + epsilon/2^n) = sum_(n=1)^oo m_*(E_n) + epsilon.
    $
    Since $epsilon$ is arbitrary, we conclude that $m_*(E) <= sum_(n=1)^oo m_*(E_n)$.
    $qed$
]

#proposition(name: "Outer Regularity")[
    If $E subset.eq RR^d$, then
    $ 
    m_*(E) = inf{m_*(cal(U)) : cal(U) "is open and" E subset.eq cal(U)}.
    $
]
#proof[
    Clearly $m_*(E) <= inf{m_*(cal(U))}$. On the other hand, given $epsilon > 0$, there exists a covering $E subset.eq union.big_(n=1)^oo Q_n$ by closed cubes such that
    $ 
    sum_(n=1)^oo m_*(Q_n) <= m_*(E) + epsilon/2.
    $
    Let $Q_j^0$ denote an open cube containing $Q_j$ such that $|Q_j^0| <= |Q_j| + epsilon/2^(j+1)$. Then $cal(U) = union.big_(n=1)^oo Q_n^0$ is an open set containing $E$ and by countable subadditivity we have
    $ 
    m_*(cal(U)) <= sum_(n=1)^oo m_*(Q_n^0) <= sum_(n=1)^oo (m_*(Q_n) + epsilon/2^(n+1)) <= m_*(E) + epsilon.
    $
    Since $epsilon$ is arbitrary, we conclude that $m_*(E) >= inf{m_*(cal(U))}$.
    $qed$
]

#proposition[
    If $E = E_1 union E_2$ and $d(E_1, E_2) > 0$, then $m_*(E) = m_*(E_1) + m_*(E_2)$.
]
#proof[
    By subadditivity, we have $m_*(E) <= m_*(E_1) + m_*(E_2)$. On the other hand, fix $epsilon > 0$. Choose $delta > 0$ such that $d(E_1, E_2) > delta$. Choose a cover $E subset.eq union.big_(n=1)^oo Q_n$ by closed cubes with side length less than $delta$. Then each $Q_n$ can intersect at most one of $E_1$ and $E_2$. Let $cal(Q)_1$ be the collection of cubes that intersect $E_1$, and let $cal(Q)_2$ be the collection of cubes that intersect $E_2$. Then
    $ 
    m_*(E_1) + m_*(E_2) <= sum_(Q in cal(Q)_1) m_*(Q) + sum_(Q in cal(Q)_2) m_*(Q) <= sum_(n=1)^oo m_*(Q_n) <= m_*(E) + epsilon.
    $
    Since $epsilon$ is arbitrary, we conclude that $m_*(E) >= m_*(E_1) + m_*(E_2)$.
    $qed$
]

#proposition[
    If $E = union.big_(n=1)^oo Q_n$ is a countable union of almost disjoint closed cubes, then $m_*(E) = sum_(n=1)^oo |Q_n|$.
]
#proof[
    By subadditivity, we have $m_*(E) <= sum_(n=1)^oo m_*(Q_n) = sum_(n=1)^oo |Q_n|$. On the other hand, given $epsilon > 0$, let $Q_j'$ be a cube strictly contained in $Q_j$ such that $|Q_j| <= |Q_j'| + epsilon/2^j$. Then for every $N$, the cubes $Q_1', Q_2', ..., Q_N'$ are disjoint and have positive distance from each other, so
    $ 
    m_*(union.big_(j=1)^N Q_j') = sum_(j=1)^N |Q_j'| >= sum_(j=1)^N (|Q_j| - epsilon/2^j).
    $
    Since $union.big_(j=1)^N Q_j' subset.eq E$, we have
    $ 
    m_*(E) >= sum_(j=1)^N (|Q_j| - epsilon/2^j) >= sum_(j=1)^N |Q_j| - epsilon.
    $
    By letting $N -> oo$, we conclude that $m_*(E) >= sum_(n=1)^oo |Q_n| - epsilon$. Since $epsilon$ is arbitrary, we conclude that $m_*(E) >= sum_(n=1)^oo |Q_n|$.
    $qed$
]

== Measurable Sets and the Lebesgue Measure

#definition[
    A subset $E subset.eq RR^d$ is said to be (Lebesgue) measurable if for every $epsilon > 0$, there exists an open set $cal(U) subset.eq RR^d$ such that $E subset.eq cal(U)$ and $m_*(cal(U) backslash E) <= epsilon$. If $E$ is measurable, we define the Lebesgue measure of $E$ to be $m(E) = m_*(E)$.
]

#proposition[
    Every open set is measurable.
]
#proof[
    Follows immediately from the definition of measurability, since we can take $cal(U) = E$ and $m_*(emptyset) = 0$.
    $qed$
]

#proposition[
    If $m_*(E) = 0$, then $E$ is measurable.
]
#proof[
    Since $m_*(E) = 0$, by outer regularity there exists an open set $cal(U)$ containing $E$ such that $m_*(cal(U)) <= epsilon$. Then $cal(U) backslash E subset.eq cal(U)$, so $m_*(cal(U) backslash E) <= m_*(cal(U)) <= epsilon$. Since $epsilon$ is arbitrary, we conclude that $E$ is measurable.
    $qed$
]

#proposition[
    A countable union of measurable sets is measurable.
]
#proof[
    Using the $epsilon/2^n$ argument, we can find a sequence of open sets $cal(U)_1, cal(U)_2, ...$ such that $E_n subset.eq cal(U)_n$ and $m_*(cal(U)_n backslash E_n) <= epsilon/2^n$. Then $union.big_(n=1)^oo E_n subset.eq union.big_(n=1)^oo cal(U)_n$ and
    $ 
    m_*(union.big_(n=1)^oo cal(U)_n backslash union.big_(n=1)^oo E_n) <= m_*(union.big_(n=1)^oo (cal(U)_n backslash E_n)) <= sum_(n=1)^oo m_*(cal(U)_n backslash E_n) <= epsilon.
    $
    Since $epsilon$ is arbitrary, we conclude that $union.big_(n=1)^oo E_n$ is measurable.
    $qed$
]

#proposition[
  Closed sets are measurable.
]
#proof[
    It suffices to show that compact sets are measurable since every closed set can be written as a countable union of compact sets (take the intersection of the closed set with a large closed cube). 

    Let $F subset.eq RR^d$ be compact and let $epsilon > 0$. We have $m_*(F) < oo$ since $F$ is bounded. By outer regularity, there exists an open set $cal(U)$ containing $F$ such that $m_*(cal(U)) <= m_*(F) + epsilon$. Since $F$ is closed, $cal(U) backslash F$ is open, so $cal(U) backslash F$ can be written as a countable union of almost disjoint cubes
    $ 
    cal(U) backslash F = union.big_(n=1)^oo Q_n.
    $
    For each $N$, the finite union $K = union.big_(n=1)^N Q_n$ is compact hence has positive distance from $F$. Therefore, 
    $ 
    m_*(cal(U)) >= m_*(F) + m_*(K) = m_*(F) + sum_(n=1)^N |Q_n| \
    => sum_(n=1)^N |Q_n| <= m_*(cal(U)) - m_*(F) <= epsilon.
    $
    Letting $N -> oo$, we conclude that
    $ 
    m_*(cal(U) backslash F) = m_*(union.big_(n=1)^oo Q_n) <= sum_(n=1)^oo |Q_n| <= epsilon.
    $
    Since $epsilon$ is arbitrary, we conclude that $F$ is measurable.
    $qed$
]

#proposition[
    The complement of a measurable set is measurable.
]
#proof[
    Suppose that $E$ is measurable. For positive integer $n$, there exists an open set $cal(U)_n$ containing $E$ such that $m_*(cal(U)_n backslash E) <= 1/n$. Then $cal(U)_n^c$ is a closed set contained in $E^c$, so
    $ 
    S := union.big_(n=1)^oo cal(U)_n^c subset.eq E^c
    $
    is measurable. Also, $E^c backslash S = inter_(n=1)^oo (cal(U)_n backslash E)$, so $m_*(E^c backslash S) <= m_*(cal(U)_n backslash E) <= 1/n$ for each $n$, thus $m_*(E^c backslash S) = 0$. Since $S$ is measurable and $E^c backslash S$ has zero outer measure, we conclude that $E^c$ is measurable.
    $qed$
]

#proposition[
    A countable intersection of measurable sets is measurable.
]
#proof[
    Follows immediately from the previous proposition and De Morgan's laws.
    $qed$
]

The family of measurable sets is closed under countable unions, countable intersections and complements, and contains all open sets and closed sets, and hence $G_delta$ sets and $F_sigma$ sets. 

#theorem[
    If $E_1, E_2, ...$ are pairwise disjoint measurable sets, then
    $ 
    m(union.big_(n=1)^oo E_n) = sum_(n=1)^oo m(E_n).
    $
]
#proof[
    Assume each $E_n$ is bounded. Apply the definition of measurability to each $E_n^c$ to find an open set $cal(U)_n supset.eq E_n^c$ such that $m_*(cal(U)_n backslash E_n^c) <= epsilon/2^n$. Then $F_n := cal(U)_n^c$ is a closed set contained in $E_n$ with $m_*(E_n backslash F_n) <= epsilon/2^n$. Note that $F_1, F_2, ...$ are compact and pairwise disjoint, so we have
    $ 
    m(union.big_(n=1)^N F_n) = sum_(n=1)^N m(F_n).
    $
    Since $union.big_(n=1)^N F_n subset.eq union.big_(n=1)^N E_n$, we have
    $ 
    m(union.big_(n=1)^N E_n) >= m(union.big_(n=1)^N F_n) = sum_(n=1)^N m(F_n) >= sum_(n=1)^N (m(E_n) - epsilon/2^n).
    $
    By letting $N -> oo$, we conclude that
    $ 
    m(union.big_(n=1)^oo E_n) >= sum_(n=1)^oo m(E_n) - epsilon. 
    $
    Since $epsilon$ is arbitrary, we conclude that $m(union.big_(n=1)^oo E_n) >= sum_(n=1)^oo m(E_n)$. The reverse inequality follows from countable subadditivity.

    In the general case, we can write each $E_n$ as a countable union of bounded measurable sets, and then apply the above argument to these bounded sets.
    $qed$
]

=== Continuity of Lebesgue Measure

#definition[
    A sequence of sets $E_1, E_2, ...$ increases to $E$ if $E_1 subset.eq E_2 subset.eq dots.c$ and $union.big_(n=1)^oo E_n = E$, denoted by $E_n arrow.t E$. A sequence of sets $E_1, E_2, ...$ decreases to $E$ if $E_1 supset.eq E_2 supset.eq dots.c$ and $inter_(n=1)^oo E_n = E$, denoted by $E_n arrow.b E$.
]

#proposition(id: "prop:continuity_of_measure")[
    Suppose that $E_1, E_2, ...$ are measurable sets.

    + If $E_n arrow.t E$, then $m(E_n) -> m(E)$.
    + If $E_n arrow.b E$ and $m(E_1) < oo$, then $m(E_n) -> m(E)$.
]
#proof[
    + Let $F_1 = E_1$ and $F_n = E_n backslash E_(n-1)$ for $n >= 2$. Then $F_1, F_2, ...$ are pairwise disjoint measurable sets and $union.big_(n=1)^N F_n = E_N$ for each $N$. Therefore,
    $ 
    m(E) = m(union.big_(n=1)^oo F_n) = sum_(n=1)^oo m(F_n) = lim_(N -> oo) sum_(n=1)^N m(F_n) = lim_(N -> oo) m(E_N).
    $
    + Let $F_k = E_k backslash E_(k+1)$ for each $k$. Then $F_1, F_2, ...$ are pairwise disjoint measurable sets and $E_1 = E union union.big_(k=1)^oo F_k$. Since $m(E_k) < oo$ for each $k$, we have
    $ 
    m(E_k) = m(F_k) + m(E_(k+1)) => m(F_k) = m(E_k) - m(E_(k+1)).
    $
    Therefore,
    $ 
    m(E_1) = m(E) + sum_(k=1)^oo m(F_k) = m(E) + m(E_1) - lim_(N -> oo) m(E_(N+1)) \
    => lim_(N -> oo) m(E_N) = m(E).
    $
    $qed$
]

=== Approximation of Measurable Sets

#proposition[
    Suppose that $E subset.eq RR^d$ is measurable. Let $epsilon > 0$.

    + There exists a closed set $F subset.eq E$ such that $m(E backslash F) <= epsilon$.
    + If $m(E) < oo$, then there exists a compact set $K subset.eq E$ such that $m(E backslash K) <= epsilon$.
    + If $m(E) < oo$, then there exists a finite union $F$ of closed cubes such that $m(E triangle.t F) <= epsilon$.
]
#proof[
    + Follows from outer regularity and the fact that the complement of measurable sets are measurable.
    + By (a), there exists a closed set $F subset.eq E$ such that $m(E backslash F) <= epsilon/2$. Define $K_n = F inter [-n, n]^d$ for each $n$. Then $K_n arrow.t F$, so $E backslash K_n arrow.b E backslash F$. By continuity of measure, we have $m(E backslash K_n) -> m(E backslash F) <= epsilon/2$. Therefore, there exists $N$ such that $m(E backslash K_N) <= epsilon$.
    + By definition of outer measure, there exists a covering $E subset.eq union.big_(n=1)^oo Q_n$ by closed cubes such that $sum_(n=1)^oo |Q_n| <= m(E) + epsilon/2$. Since $m(E) < oo$, the series is convergent, so there exists $N$ such that $sum_(n=N+1)^oo |Q_n| <= epsilon/2$. Let $F = union.big_(n=1)^N Q_n$. Then $F$ is a finite union of closed cubes and
    $ 
    m(E triangle.t F) &<= m(E backslash F) + m(F backslash E) \
    &<= m(E backslash union.big_(n=1)^N Q_n) + m(union.big_(n=1)^N Q_n backslash E) \
    &<= m(union.big_(n=N+1)^oo Q_n) + m(union.big_(n=1)^oo Q_n backslash E) \
    &<= sum_(n=N+1)^oo |Q_n| + sum_(n=1)^oo |Q_n| - m(E) \
    &<= epsilon/2 + epsilon/2 = epsilon.
    $
    $qed$
]

=== Translation Invariance and Scaling

#proposition[
    If $E subset.eq RR^d$ is measurable, then so is $E + h = {x + h : x in E}$. Moreover, $m(E + h) = m(E)$.
]
#proof[
    This holds when $E$ is a closed cube. From the definition of outer measure, we have $m_*(E + h) = m_*(E)$. It remains to show that $E + h$ is measurable. Given $epsilon > 0$, there exists an open set $cal(U)$ containing $E$ such that $m(cal(U) backslash E) <= epsilon$. Then $cal(U) + h$ is an open set containing $E + h$, and
    $ 
    m_*((cal(U) + h) backslash (E + h)) = m_*(cal(U) backslash E) <= epsilon,
    $
    so $E + h$ is measurable and $m(E + h) = m_*(E + h) = m_*(E) = m(E)$.
    $qed$
]

#remark[
    Similarly, one can prove that $m(a E) = |a|^d m(E)$ for any nonzero real number $a$.
]

=== $sigma$-Algebra and Borel Sets

#definition[
    A $sigma$-algebra of sets is a collection of subsets of a set $Omega$ that consists of $emptyset$, and is closed under countable unions and complements. 
]

#example[
    - All measurable sets in $RR^d$ form a $sigma$-algebra.
    - The power set of $Omega$ is a $sigma$-algebra. 
    - ${emptyset, Omega}$ is a $sigma$-algebra.
]

Note that the intersection of any collection of $sigma$-algebras is still a $sigma$-algebra. Therefore, given a family $cal(F)$ of subsets of $Omega$, there exists a smallest $sigma$-algebra containing $cal(F)$, which is the intersection of all $sigma$-algebras containing $cal(F)$.

The Borel $sigma$-algebra on $RR^d$, denoted by $cal(B)_(RR^d)$, is the smallest $sigma$-algebra containing all open sets in $RR^d$. The elements of $cal(B)_(RR^d)$ are called Borel sets. 

We can easily see that $cal(B)_(RR^d)$ is contained in the family of measurable sets. In fact, the containment is strict. However, a measurable set can be approximated by Borel sets in the following sense.

#proposition[
    The following are equivalent for a subset $E subset.eq RR^d$:

    + $E$ is measurable.
    + $m(G backslash E) = 0$ for some $G_delta$ set $G supset.eq E$.
    + $m(E backslash F) = 0$ for some $F_sigma$ set $F subset.eq E$.
]
#proof[
    (i) $=>$ (ii): Suppose that $E$ is measurable. For each positive integer $n$, there exists an open set $cal(U)_n$ containing $E$ such that $m_*(cal(U)_n backslash E) <= 1/n$. Then $G := inter_(n=1)^oo cal(U)_n$ is a $G_delta$ set containing $E$, and
    $ 
    m(G backslash E) <= m(cal(U)_n backslash E) <= 1/n
    $
    for each $n$, so $m(G backslash E) = 0$.

    (ii) $=>$ (iii): Follows from the fact that the complement of a $G_delta$ set is an $F_sigma$ set, and measurable sets are closed under complements.

    (iii) $=>$ (i): Obvious since $E$ is now the union of a measurable set $F$ and a set of measure zero.
    $qed$
]

The Lebesgue measurable sets can be seen as the completion of the Borel $sigma$-algebra with respect to the Lebesgue measure. 

=== Nonmeasurable Sets

Define the equivalence relation $tilde$ on $[0, 1]$ by $x tilde y$ if $x - y in QQ$. Write
$ 
[0, 1] = union.sq.big_(alpha in A) E_alpha,
$
where $E_alpha$ are the equivalence classes. Using the axiom of choice, we can choose a representative $x_alpha$ from each $E_alpha$, and let $N = {x_alpha : alpha in A}$. Then $N$ is a nonmeasurable set. 

#theorem[
    $N$ is not measurable.
]
#proof[
    Suppose that $N$ is measurable. Let $(r_k)$ be the enumeration of rational numbers in $[-1, 1]$. Define
    $ 
    N_k = N + r_k. 
    $

    If $N_k inter N_l eq.not emptyset$ for some $k eq.not l$, then there exist $x_alpha, x_beta in N$ such that $x_alpha + r_k = x_beta + r_l$, so $x_alpha - x_beta = r_l - r_k in QQ$. This contradicts the definition of $N$. Therefore, the sets $N_k$ are pairwise disjoint. 

    Let $x in [0, 1]$. Then $x tilde x_alpha$ for some $alpha$, so $x - x_alpha in QQ inter [-1, 1]$. Therefore, $x in N_k$ for some $k$, so
    $ 
    [0, 1] subset.eq union.big_(k=1)^oo N_k subset.eq [-1, 2].
    $
    Since $N_k$ are pairwise disjoint and have the same measure as $N$, we have
    $ 
    1 <= sum_(k=1)^oo m(N) <= 3.
    $
    This is a contradiction since $m(N)$ must be zero or positive. Therefore, $N$ is not measurable.
    $qed$
]

== The Brunn-Minkowski Inequality

For two measurable sets $A, B subset.eq RR^d$, we define their (Minkowski) sum to be
$ 
A + B = {a + b : a in A, b in B}.
$
In general, it is impossible to upper bound $m(A + B)$ in terms of $m(A)$ and $m(B)$, since there exists sets $A, B$ of measure zero such that $A + B$ has positive measure. 

#theorem(name: "Brunn-Minkowski Inequality")[
    Suppose $A, B subset.eq RR^d$ are measurable sets, and $A + B$ is also measurable. Then
    $ 
    m(A + B)^(1/d) >= m(A)^(1/d) + m(B)^(1/d).
    $
]
#proof[
    We first assume that $A, B$ are rectangles with side lengths $(a_i)$ and $(b_i)$ respectively. Then $A + B$ is a rectangle with side lengths $(a_i + b_i)$. Note that
    $ 
    (product_(i=1)^d a_i/a_i + b_i)^(1/d) + (product_(i=1)^d b_i/a_i + b_i)^(1/d) <= 1/d sum_(i=1)^d a_i/a_i + b_i + 1/d sum_(i=1)^d b_i/a_i + b_i = 1, \
    => m(A + B)^(1/d) = product_(i=1)^d (a_i + b_i)^(1/d) >= product_(i=1)^d a_i^(1/d) + product_(i=1)^d b_i^(1/d) = m(A)^(1/d) + m(B)^(1/d).
    $

    Now suppose that $A, B$ are unions of finitely almost disjoint rectangles. We proceed by induction on the number of rectangles. Choose a pair of disjoint rectangles $R_1, R_2 subset.eq A$, and we may WLOG assume that after some translation, $R_1$ and $R_2$ are separated by a coordinate hyperplane $x_j = 0$. Let $A_- = A inter {x_j <= 0}$ and $A_+ = A inter {x_j >= 0}$, then both $A_-$ and $A_+$ have fewer rectangles than $A$. We then translate $B$ so that $B_- = B inter {x_j <= 0}$ and $B_+ = B inter {x_j >= 0}$ satisfy
    $ 
    (m(B_+))/(m(B)) = (m(A_+))/(m(A)). 
    $
    Note that $A_+$ has strictly fewer rectangles than $A$, and $B_+$ has at most as many rectangles as $B$, and same goes for $A_-$ and $B_-$. We have
    $ 
    A + B supset (A_+ + B_+) union (A_- + B_-). 
    $
    By induction hypothesis, we have
    $ 
    m(A + B) &>= m(A_+ + B_+) + m(A_- + B_-) \
    &>= (m(A_+)^(1/d) + m(B_+)^(1/d))^d + (m(A_-)^(1/d) + m(B_-)^(1/d))^d \
    &>= m(A_+)(1 + ((m(B_+))/(m(A_+)))^(1/d))^d + m(A_-)(1 + ((m(B_-))/(m(A_-)))^(1/d))^d \
    &>= m(A)(1 + ((m(B))/(m(A)))^(1/d))^d = (m(A)^(1/d) + m(B)^(1/d))^d.
    $

    Next, suppose that $A, B$ are open sets with finite measures. For any $epsilon > 0$, we can find finite unions of almost disjoint cubes $A_epsilon subset.eq A$ and $B_epsilon subset.eq B$ such that $m(A) <= m(A_epsilon) + epsilon$ and $m(B) <= m(B_epsilon) + epsilon$. Then $A_epsilon + B_epsilon subset.eq A + B$, so
    $ 
    m(A + B) &>= m(A_epsilon + B_epsilon) \
    &>= (m(A_epsilon)^(1/d) + m(B_epsilon)^(1/d))^d \
    &>= ((m(A) - epsilon)^(1/d) + (m(B) - epsilon)^(1/d))^d.
    $
    By letting $epsilon -> 0$, we conclude that $m(A + B) >= (m(A)^(1/d) + m(B)^(1/d))^d$. 

    Suppose $A, B$ are compact sets. If $A, B$ are compact, then $A + B$ is also compact, in particular measurable. Define $A_epsilon = {x in RR^d : d(x, A) <= epsilon}$ and $B_epsilon = {x in RR^d : d(x, B) <= epsilon}$. Then $A_epsilon arrow.b A$ and $B_epsilon arrow.b B$, so $A_epsilon + B_epsilon arrow.b A + B$. By continuity of measure, we have
    $ 
    m(A + B) = lim_(epsilon -> 0) m(A_epsilon + B_epsilon) >= lim_(epsilon -> 0) (m(A_epsilon)^(1/d) + m(B_epsilon)^(1/d))^d = (m(A)^(1/d) + m(B)^(1/d))^d.
    $

    Finally, for general measurable sets $A, B$, if $m(A) = oo$ or $m(B) = oo$, then $m(A + B) = oo$, so the inequality is trivial. Otherwise, we can find compact sets $K_A subset.eq A$ and $K_B subset.eq B$ such that $m(A backslash K_A) <= epsilon$ and $m(B backslash K_B) <= epsilon$. Then $K_A + K_B subset.eq A + B$, so
    $ 
    m(A + B) &>= m(K_A + K_B) \
    &>= (m(K_A)^(1/d) + m(K_B)^(1/d))^d \
    &>= ((m(A) - epsilon)^(1/d) + (m(B) - epsilon)^(1/d))^d.
    $
    By letting $epsilon -> 0$, we conclude that $m(A + B) >= (m(A)^(1/d) + m(B)^(1/d))^d$.
    $qed$
]

#remark[
    In general, $A, B$ being measurable does not imply that $A + B$ is measurable. For example, let $N$ be the nonmeasurable set constructed above, and let $A = {0} times N$ and $B = N times {0}$, then $A + B = N times N$ is not measurable.
]

== Measurable Functions

Consider functions from $RR^d$ to extended real numbers $[-oo, oo] := RR union { plus.minus oo }$. 

#definition[
    A function $f: E -> [-oo, oo]$ is measurable if for every $a in RR$, the set
    $ 
    f^(-1)([-oo, a)) = {x in E : f(x) < a}
    $
    is measurable.
]

Roughly speaking, measurable functions are those that we would like to integrate. The simplest function to integrate is the characteristic function $chi_E$ of a measurable set $E$. 

#proposition[
    $f$ is measurable if and only if
    $ 
    f^(-1)((-oo, a]) = {x in E : f(x) <= a}
    $
    is measurable for every $a in RR$.
]
#proof[
    If $f^(-1)([-oo, a))$ is measurable for every $a$, then $f^(-1)((-oo, a]) = inter_(n=1)^oo f^(-1)([-oo, a + 1/n))$ is measurable for every $a$. Conversely, if $f^(-1)((-oo, a])$ is measurable for every $a$, then $f^(-1)([-oo, a)) = union.big_(n=1)^oo f^(-1)((-oo, a - 1/n])$ is measurable for every $a$.
$qed$
]

In the same way, we can show that $f$ is measurable if and only if $f^(-1)((a, b))$ is measurable for every $a < b$. 

#proposition[
    A finite-valued function $f$ is measurable if and only if $f^(-1)(cal(O))$ is measurable for every open set $cal(O) subset.eq RR$, and if and only if $f^(-1)(cal(F))$ is measurable for every closed set $cal(F) subset.eq RR$.
]

#proposition[
    If $f$ is continuous on $RR^d$, then $f$ is measurable.
]
#proof[
    Since $f$ is continuous, it is finite-valued. By the previous proposition it is measurable.
    $qed$
]

#proposition[
    If $f$ is measurable and $Phi$ is continuous, then $Phi compose f$ is measurable.
]
#proof[
    Since $Phi$ is continuous, $Phi^(-1)((-oo, a))$ is open, hence
    $ 
    (Phi compose f)^(-1)((-oo, a)) = f^(-1)(Phi^(-1)((-oo, a)))
    $
    is measurable for every $a$, so $Phi compose f$ is measurable.
    $qed$
]

#proposition[
    If $(f_n)$ is a sequence of measurable functions, then
    $ 
    sup_n f_n,  quad  inf_n f_n,  quad  limsup_(n -> oo) f_n,  quad  liminf_(n -> oo) f_n
    $
    are all measurable.
]
#proof[
    $ 
    { sup_n f_n > a } = union.big_(n=1)^oo { f_n > a }, quad { inf_n f_n < a } = union.big_(n=1)^oo { f_n < a }. 
    $
    Therefore, $sup_n f_n$ and $inf_n f_n$ are measurable. Since
    $ 
    limsup_(n -> oo) f_n = inf_(N) sup_(n >= N) f_n,  quad  liminf_(n -> oo) f_n = sup_(N) inf_(n >= N) f_n,
    $
    $limsup_(n -> oo) f_n$ and $liminf_(n -> oo) f_n$ are measurable as well.
    $qed$
]

#claim[
    If $(f_n)$ is a sequence of measurable functions and $lim_(n -> oo) f_n = f$ pointwise, then $f$ is measurable.
]

#proposition[
    If $f$ is measurable, then so is $f^k$ for any positive integer $k$.
]
#proof[
    If $k$ is odd, then ${f^k > a} = {f > a^(1/k)}$. If $k$ is even, then ${f^k > a} = {f > a^(1/k)} union {f < -a^(1/k)}$. In either case, $f^k$ is measurable.
    $qed$
]

#proposition[
    If $f, g$ are finite-valued measurable functions, then $f + g$ and $f g$ are measurable. 
]
#proof[
    Note that
    $ 
    {f + g > a} = union.big_(q in QQ) {f > q} inter {g > a - q},
    $
    hence $f + g$ is measurable. Write
    $ 
    f g = 1/4((f + g)^2 - (f - g)^2),
    $
    hence $f g$ is measurable.
$qed$
]

#definition[
    Two functions $f, g$ defined on a measurable set $E$ are equal almost everywhere, denoted by $f = g$ a.e., if the set ${x in E : f(x) eq.not g(x)}$ has measure zero.
]

#proposition[
    If $f$ is measurable and $g = f$ a.e., then $g$ is measurable.
]
#proof[
    ${g < a}$ and ${f < a}$ differ by a subset of ${x in E : f(x) eq.not g(x)}$, which has measure zero, so $g$ is measurable.
    $qed$
]

=== Approximation of Measurable Functions

#definition[
    A step function is a finite linear combination of characteristic functions of rectangles, i.e. a function of the form
    $ 
    f = sum_(k=1)^N a_k chi_(R_k),
    $
    where $a_k$ are real numbers and $R_k$ are rectangles.
]

#definition[
    A simple function is a finite linear combination of characteristic functions of measurable sets with finite measures, i.e. a function of the form
    $ 
    f = sum_(k=1)^N a_k chi_(E_k),
    $
    where $a_k$ are real numbers and $E_k$ are measurable sets with finite measures.
]

#theorem[
    Suppose that $f$ is a nonnegative measurable function. Then there exists an increasing sequence of nonnegative simple functions $(phi_k)$ such that $phi_k -> f$ pointwise.
]
#proof[
    For $N>= 1$, let $Q_N$ be the cube centered at the origin with side length $N$. Define the truncated function
    $ 
    F_N (x) = cases(
        f(x) & x in Q_N "and" f(x) <= N, 
        N & x in Q_N "and" f(x) > N, 
        0 & x in.not Q_N,
    )
    $
    Then $F_N -> f$ pointwise as $N -> oo$. Also, each $F_N$ is measurable and bounded. For fixed $N, M >= 1$, define
    $ 
    E_(l, M) = { x in Q_N : l/M < F_N (x) <= (l+1)/M }
    $
    for $l = 0, 1, ..., M N - 1$. Then $E_(l, M)$ are measurable sets with finite measures. Define
    $ 
    F_(N, M) = sum_(l=0)^(M N - 1) l/M chi_(E_{l, M)}.
    $
    Then $F_(N, M)$ are simple functions and
    $ 
    0 <= F_N - F_(N, M) <= 1/M. 
    $
    Choose $N = M = 2^k$ and set $phi_k = F_(2^k, 2^k)$ for each $k$. Then $(phi_k)$ is an increasing sequence of nonnegative simple functions such that $phi_k -> f$ pointwise as $k -> oo$.

    Note that the result holds for extended-value nonnegative measurable functions, if we allow the limit to be $oo$.
    $qed$
]

#theorem[
    Suppose that $f$ is a measurable function. Then there exists a sequence of simple functions $(phi_k)$ such that
    $ 
    |phi_k(x)| <= |phi_(k+1)(x)|,  quad  lim_(k -> oo) phi_k(x) = f(x)
    $
    for every $x$.
]
#proof[
    Write $f = f_+ - f_-$, where $f_+ = max(f, 0)$ and $f_- = max(-f, 0)$. Then $f_+$ and $f_-$ are nonnegative measurable functions. By the previous theorem, there exist increasing sequences of nonnegative simple functions $(phi_k^+)$ and $(phi_k^-)$ which increase to $f_+$ and $f_-$ pointwise respectively. Define $phi_k = phi_k^+ - phi_k^-$, then $phi_k -> f$ pointwise as $k -> oo$. Moreover, we have
    $ 
    |phi_k| = phi_k^+ + phi_k^- <= phi_(k+1)^+ + phi_(k+1)^- = |phi_(k+1)|.
    $
    $qed$
]

#theorem(id: "thm:step_approx")[
    Suppose that $f$ is a measurable function. Then there exists a sequence of step functions $(psi_k)$ such that $psi_k -> f$ a.e. as $k -> oo$.
]
#proof[
    By the previous theorem, it suffices to show the result for $chi_E$, where $E$ is a measurable set with finite measure. Let $epsilon > 0$. Recall that there exists a finite union $union.big_(n=1)^N Q_n$ of cubes such that
    $ 
    m(E triangle.t union.big_(n=1)^N Q_n) <= epsilon.
    $
    Extend the sides these cubes and obtain a grid, then we can write $union.big_(n=1)^N Q_n$ as a finite union of almost disjoint rectangles $R_1', ..., R_M'$. By taking rectangles $R_j$ slightly smaller than $R_j'$, we can ensure that $R_1, ..., R_M$ are pairwise disjoint rectangles such that
    $ 
    m(E triangle.t union.big_(j=1)^M R_j) <= 2epsilon.
    $
    Hence $f(x) = sum_(j=1)^M chi_(R_j)(x)$ for all $x$ except for a set of measure at most $2epsilon$. Consequently, for each $k$, we can find a step function $psi_k$ such that
    $ 
    m(underbrace({x : psi_k(x) eq.not f(x)}, =:E_k ) <= 2^(-k).
    $
    Note that $f$ converges to $f$ on the complement of $inter_(j=1)^oo union.big_(k=j)^oo E_k$, which has measure zero. Therefore, $psi_k -> f$ a.e. as $k -> oo$.
    $qed$
]

=== Littlewood's Three Principles

+ Every measurable set in $RR$ is nearly a finite union of disjoint intervals.
+ Every measurable function on $RR$ is nearly continuous.
+ Every convergent sequence of measurable functions is nearly uniformly convergent.

#theorem(name: "Egorov")[
    Suppose that $(f_k)$ is a sequence of measurable functions on a measurable set $E$ with finite measure, and $f_k -> f$ almost everywhere on $E$. Then for every $epsilon > 0$, there exists a closed set $A_epsilon subset.eq E$ such that $m(E backslash A_epsilon) <= epsilon$ and $f_k arrows.rr f$ uniformly on $A_epsilon$.
]
#proof[
    Me may assume WLOG that $f_k -> f$ everywhere on $E$. For $n, k >= 1$, define
    $ 
    E_k^n = {x in E : |f_j(x) - f(x)| < 1/n "for all" j >= k}.
    $
    Then $E_k^n arrow.t E$ as $k -> oo$, so by continuity of measure, we have $m(E backslash E_k^n) -> 0$ as $k -> oo$. Therefore, there exists $k_n$ such that $m(E backslash E_(k_n)^n) <= 2^(-n)$ for each $n$. Choose $N$ large enough such that $sum_(n=N)^oo 2^(-n) <= epsilon/2$. Let $A_epsilon' = inter_(n=N)^oo E_(k_n)^n$, then $m(E backslash A_epsilon') <= epsilon/2$. 

    Let $delta > 0$. Choose $n >= N$ such that $1/n < delta$. Then for every $x in A_epsilon'$ and $j >= k_n$, we have $|f_j(x) - f(x)| < 1/n < delta$. Therefore, $f_j arrows.rr f$ uniformly on $A_epsilon'$. Since $A_epsilon'$ is measurable, there exists a closed set $A_epsilon subset.eq A_epsilon'$ such that $m(A_epsilon' backslash A_epsilon) <= epsilon/2$. Then
    $ 
    m(E backslash A_epsilon) <= m(E backslash A_epsilon') + m(A_epsilon' backslash A_epsilon) <= epsilon.
    $
    Moreover, $f_j arrows.rr f$ uniformly on $A_epsilon$ since $A_epsilon subset.eq A_epsilon'$.
    $qed$
]

#theorem(name: "Lusin")[
    Suppose that $f$ is a finite-valued measurable function on a measurable set $E$ with finite measure. Then for every $epsilon > 0$, there exists a closed set $F_epsilon subset.eq E$ such that $m(E backslash F_epsilon) <= epsilon$ and $f|_(F_epsilon)$ is continuous.
]
#proof[
    By @thm:step_approx, there exists a sequence of step functions $(psi_k)$ such that $psi_k -> f$ a.e. as $k -> oo$. Find measurable sets $E_k$ such that $m(E_k) <= 2^(-k)$ and $psi_k$ is continuous outside $E_k$. By Egorov's theorem, there exists a closed set $A_epsilon subset.eq E$ such that $m(E backslash A_epsilon) <= epsilon/3$ and $psi_k arrows.rr f$ uniformly on $A_epsilon$. Pick $N$ large enough such that $sum_(k=N)^oo 2^(-k) <= epsilon/3$, and let
    $ 
    F_epsilon' = A_epsilon backslash union.big_(k=N)^oo E_k.
    $
    Then for all $n >= N$, $psi_n$ is continuous on $F_epsilon'$, so $f$ is the uniform limit of continuous functions on $F_epsilon'$, hence continuous on $F_epsilon'$. Since $F_epsilon'$ is measurable, there exists a closed set $F_epsilon subset.eq F_epsilon'$ such that $m(F_epsilon' backslash F_epsilon) <= epsilon/3$. Then
    $ 
    m(E backslash F_epsilon) <= m(E backslash A_epsilon) + m(A_epsilon backslash F_epsilon') + m(F_epsilon' backslash F_epsilon) <= epsilon.
    $
    Moreover, $f|_(F_epsilon)$ is continuous since $F_epsilon subset.eq F_epsilon'$.
    $qed$
]

= Integration Theory

In this chapter, we will define the Lebesgue integral for integrable functions in a progressive manner. Starting from simple functions, bounded measurable functions on sets of finite measure, nonnegative measurable functions, and finally general integrable functions. 

== The Lebesgue Integral

A simple function is a finite sum
$ 
phi = sum_(k=1)^N a_k chi_(E_k),
$
where $a_k$ are real numbers and $E_k$ are measurable sets with finite measures. There is usually more than one way to write a simple function as a linear combination of characteristic functions. A decomposition of $phi$ is canonical if all $E_k$ are pairwise disjoint and $a_k eq.not 0$ are distinct for each $k$. Every simple function has a unique canonical decomposition.

If $phi$ is a simple function with canonical decomposition $phi = sum_(k=1)^N a_k chi_(E_k)$, then we define the Lebesgue integral of $phi$ to be
$ 
integral_(RR^d) phi(x) d x = sum_(k=1)^N a_k m(E_k).
$
If $E subset.eq RR^d$ is a measurable set, then we define
$ 
integral_E phi(x) d x = integral_(RR^d) phi(x) chi_E(x) d x. 
$

#proposition[
    If $phi = sum_(k=1)^M b_k chi_(F_k)$ is any another decomposition of $phi$, then
    $ 
    integral phi = sum_(k=1)^M b_k m(F_k).
    $
]
#proof[
    Assume that $F_k$ are pairwise disjoint, then for each nonzero value $b$ in ${b_k}$, define $F_b' = union.big_(b_k = b) F_k$. Then clearly $phi = sum_(b) b chi_(F_b')$ is the canonical decomposition of $phi$, and the finite sum equals $integral phi$.

    In general, we can refine $union.big_(k=1)^M F_k$ into a finite union of pairwise disjoint sets $F_1', ..., F_N'$ such that $union.big_(k=1)^M F_k = union.big_(n=1)^N F_n'$ and $F_k = union.big_(n : F_n' subset.eq F_k) F_n'$ for each $k$. For each $n$, let $b_n' = sum_(k : F_n' subset.eq F_k) b_k$, then clearly $phi = sum_(n=1)^N b_n' chi_(F_n')$. This reduces to the previous case, so the finite sum equals $integral phi$.
    $qed$
]

#proposition[
    If $phi, psi$ are simple functions and $a, b in RR$, then
    $ 
    integral (a phi + b psi) = a integral phi + b integral psi.
    $
]
#proof[
    Follows from the previous proposition and the linearity of finite sums.
    $qed$
]

#proposition[
    if $E, F$ are disjoint subsets of $RR^d$ with finite measures, then
    $ 
    integral_(E union F) phi = integral_E phi + integral_F phi.
    $
]
#proof[
    Follows from the previous proposition and the fact that $chi_(E union F) = chi_E + chi_F$.
    $qed$
]

#proposition[
    If $phi <= psi$ are simple functions, then $integral phi <= integral psi$.
]
#proof[
    It suffices to show that if $eta >= 0$ is a simple function, then $integral eta >= 0$. This is clear since the canonical decomposition of $eta$ has nonnegative coefficients, so $integral eta$ is a sum of nonnegative terms.
    $qed$
]

#proposition[
    If $phi$ is a simple function, then so is $|phi|$, and
    $ 
    integral |phi| >= |integral phi|.
    $
]
#proof[
    Write $|phi| = sum_(k=1)^N |a_k| chi_(E_k)$, then
    $ 
    integral |phi| = sum_(k=1)^N |a_k| m(E_k) >= |sum_(k=1)^N a_k m(E_k)| = |integral phi|.
    $
    $qed$
]

#proposition[
    If two simple functions $phi, psi$ are equal a.e., then $integral phi = integral psi$.
]
#proof[
    Let $eta = |phi - psi|$, then $eta$ is nonzero only on a set of measure zero, so $integral eta = 0$.
    $qed$
]

The support of a measurable function $f$ is defined as
$ 
"supp" f = {x : f(x) eq.not 0}.
$
We say that $f$ is supported on a set $E$ if $"supp" f subset.eq E$. If $f$ is measurable, then $"supp" f$ is measurable. We'll consider bounded measurable functions with supports of finite measures. 

Recall that given a measurable function $f$ with $|f| <= M$ and supported on $E$, there exists a sequence of simple functions $(phi_k)$ such that $|phi_k| <= |phi_(k+1)|$ and $phi_k -> f$ pointwise as $k -> oo$. If $f$ is bounded and supported on a set of finite measure, then we can choose $phi_k$ to be bounded and supported on a set of finite measure as well.

#lemma[
    Let $f$ be as above, and assume that $m(E) < oo$. If $(phi_n)$ is any sequence of simple functions with $|phi_n| <= M$ and $"supp" phi_n subset.eq E$ such that $phi_n -> f$ a.e. as $n -> oo$, then

    + $integral phi_n$ converges to a limit as $n -> oo$.
    + If $f = 0$ a.e., then $integral phi_n -> 0$ as $n -> oo$.
]
#proof[
    If $phi_k arrows.rr f$ uniformly on $E$, then both (i) and (ii) hold. 

    In general, by Egorov's theorem, for every $epsilon > 0$, there exists a closed set $A_epsilon subset.eq E$ such that $m(E backslash A_epsilon) <= epsilon$ and $phi_n arrows.rr f$ uniformly on $A_epsilon$. Then for all $m, n >= 1$, we have
    $ 
    |integral phi_n - integral phi_m| &= |integral (phi_n - phi_m)| \
    &<= integral_E |phi_n - phi_m| \
    &<= integral_(A_epsilon) |phi_n - phi_m| + integral_(E backslash A_epsilon) |phi_n - phi_m| \
    &<= m(A_epsilon) sup_(x in A_epsilon) |phi_n(x) - phi_m(x)| + 2M m(E backslash A_epsilon) \
    &<= m(E) sup_(x in A_epsilon) |phi_n(x) - phi_m(x)| + 2M epsilon.
    $
    By uniform convergence of $phi_n$, the first term goes to zero as $n, m -> oo$, so $integral phi_n$ is a Cauchy sequence, hence converges to a limit. 

    Part (ii) follows from the same argument.
    $qed$
]

Define
$ 
integral f = lim_(n -> oo) integral phi_n,
$
where $(phi_n)$ is any sequence of simple functions with $|phi_n| <= M$ and $"supp" phi_n subset.eq "supp" f$ such that $phi_n -> f$ a.e. as $n -> oo$. The previous lemma guarantees that the limit exists and is independent of the choice of $(phi_n)$, so $integral f$ is well-defined.

Since the integral is defined as a limit of integrals of simple functions, it inherits properties such as linearity and monotonicity from the integral of simple functions.

#theorem(name: "Bounded Convergence Theorem")[
    Let $(f_n)$ be a sequence of measurable functions such that $|f_n| <= M$ and $"supp" f_n subset.eq E$ for some $M > 0$ and some measurable set $E$ with finite measure. If $f_n -> f$ a.e. as $n -> oo$, then $f$ is measurable and $integral f_n -> integral f$ as $n -> oo$.
]
#proof[
    Clearly, $f$ is measurable, $|f| <= M$ and $"supp" f subset.eq E$. Let $epsilon > 0$. By Egorov's theorem, there exists a closed set $A_epsilon subset.eq E$ such that $m(E backslash A_epsilon) <= epsilon$ and $f_n arrows.rr f$ uniformly on $A_epsilon$. Then for all $n >= 1$, we have
    $ 
    |integral f_n - integral f| &= |integral (f_n - f)| \
    &<= integral_E |f_n - f| \
    &<= integral_(A_epsilon) |f_n - f| + integral_(E backslash A_epsilon) |f_n - f| \
    &<= m(A_epsilon) sup_(x in A_epsilon) |f_n(x) - f(x)| + 2M m(E backslash A_epsilon) \
    &<= m(E) sup_(x in A_epsilon) |f_n(x) - f(x)| + 2M epsilon.
    $
    By uniform convergence of $f_n$, the first term goes to zero as $n -> oo$, so $integral f_n -> integral f$ as $n -> oo$.
    $qed$
]

#proposition(id: "prop:zero_integral")[
    If $f >= 0$ is bounded and supported on $E$ with $m(E) < oo$, and if $integral f = 0$, then $f = 0$ a.e.
]
#proof[
    For $k >= 1$, define
    $ 
    E_k = {x : f(x) >= 1/k}.
    $
    Then $E_k$ are measurable sets with finite measures and $f >= (1/k) chi_(E_k)$, so by monotonicity, 
    $ 
    1/k m(E_k) <= integral f = 0 => m(E_k) = 0.
    $
    Therefore, ${x : f(x) > 0} = union.big_(k=1)^oo E_k$ has measure zero, so $f = 0$ a.e.
    $qed$
]

In fact, we can show that Lebesgue integral is a generalization of Riemann integral.

Let $(phi_n)$ and $(psi_n)$ be two sequences of step functions such that $(phi_n)$ is increasing, $(psi_n)$ is decreasing, 
$ 
phi_n <= f <= psi_n
$
for every $n$, and
$ 
lim_(n -> oo) integral^(cal(R)) phi_n = lim_(n -> oo) integral^(cal(R)) psi_n.
$
On the other hand, 
$ 
integral^(cal(R)) phi_n = integral^(cal(L)) phi_n,  quad  integral^(cal(R)) psi_n = integral^(cal(L)) psi_n
$
since they are step functions. By monotonicity, 
$ 
phi := lim_(n -> oo) phi_n,  quad  psi := lim_(n -> oo) psi_n
$
exists pointwise and are bounded measurable functions. Also, $phi <= f <= psi$ and $integral^(cal(L)) phi = integral^(cal(L)) psi$. By bounded convergence theorem, 
$ 
integral^(cal(R)) phi = lim_(n -> oo) integral^(cal(R)) phi_n = lim_(n -> oo) integral^(cal(L)) phi_n = integral^(cal(L)) phi, \
integral^(cal(R)) psi = lim_(n -> oo) integral^(cal(R)) psi_n = lim_(n -> oo) integral^(cal(L)) psi_n = integral^(cal(L)) psi. 
$
Since $psi >= phi$ and $integral^(cal(L)) psi = integral^(cal(L)) phi$, we have $psi = phi$ a.e. by @prop:zero_integral, so $f = phi = psi$ a.e. and
$ 
integral^(cal(L)) f = integral^(cal(L)) phi = lim_(n -> oo) integral^(cal(L)) phi_n = integral^(cal(R)) f.
$
So the Lebesgue integral of $f$ equals the Riemann integral of $f$ if $f$ is Riemann integrable.

We now allow the functions to be unbounded and take on $oo$ as values. Define the Lebesgue integral of such a function by
$ 
integral f = sup_g integral g,
$
where the supremum is taken over all bounded measurable functions $g$ with supports of finite measures such that $0 <= g <= f$. When the integral of $f$ is finite, we say that $f$ is Lebesgue integrable. Again, if $E subset.eq RR^d$ is a measurable set, then we define
$ 
integral_E f = integral f chi_E.
$

#proposition[
    If $f, g >= 0$ are measurable and $a, b >= 0$, then
    $ 
    integral (a f + b g) = a integral f + b integral g.
    $
]
#proof[
    First consider the case that $a = b = 1$. If $phi, psi$ are nonnegative bounded measurable functions with supports of finite measures such that $phi <= f$ and $psi <= g$, then $phi + psi <= f + g$, so
    $ 
    integral f + integral g <= integral (f + g).
    $
    On the other hand, suppose that $eta$ is a nonnegative bounded measurable function with support of finite measure such that $eta <= f + g$. Define
    $ 
    phi = min{f, eta},  quad  psi = eta - phi.
    $
    Then $phi <= f$ and
    $ 
    psi = eta - min{f, eta} = max{eta - f, 0} <= g.
    $
    Both $phi$ and $psi$ are bounded measurable functions with supports of finite measures, so
    $ 
    integral (f + g) <= integral f + integral g.
    $
    The general case follows from the case $a = b = 1$ by homogeneity.
    $qed$
]

#proposition[
    If $E, F$ are disjoint measurable sets, and $f >= 0$, then
    $ 
    integral_(E union F) f = integral_E f + integral_F f.
    $
]
#proof[
    Follows from the previous proposition and the fact that $chi_(E union F) = chi_E + chi_F$.
    $qed$
]

#proposition[
    If $0 <= f <= g$ are measurable, then $integral f <= integral g$.
]
#proof[
    If $phi$ is a nonnegative bounded measurable function with support of finite measure such that $phi <= f$, then $phi <= g$ as well, so
    $ 
    integral f <= integral g.
    $
    $qed$
]

#proposition[
    If $g$ is integrable and $0 <= f <= g$, then $f$ is integrable as well. 
]
#proof[
    Since the subset of nonnegative functions that are bounded measurable and supported on sets of finite measures and $<= f$ is a subset of that of $g$, we have $integral f <= integral g < oo$, so $f$ is integrable.
    $qed$
]

#proposition[
    If $f$ is integrable, then $f(x) < oo$ a.e.
]
#proof[
    Let
    $ 
    E_k := {x : f(x) >= k}
    $
    and $E_oo := {x : f(x) = oo}$. Then
    $ 
    integral f >= integral_(E_k) f >= k m(E_k), 
    $
    hence $m(E_k) -> 0$ as $k -> oo$. Since $E_k arrow.b E_oo$ as $k -> oo$, we have $m(E_oo) = 0$, so $f(x) < oo$ a.e.
    $qed$
]

#proposition[
    If $integral f = 0$, then $f = 0$ a.e.
]
#proof[
    Similar to the proof of @prop:zero_integral.
    $qed$
]

#theorem(name: "Fatou's Lemma")[
    Suppose that $(f_n)$ is a sequence of nonnegative measurable functions. Then
    $ 
    integral liminf_(n -> oo) f_n <= liminf_(n -> oo) integral f_n.
    $
]
#proof[
    Let $g$ be a bounded measurable function with support of finite measure such that $0 <= g <= liminf_(n -> oo) f_n$. For $n >= 1$, define
    $ 
    g_n(x) := min{g(x), inf_(k >= n) f_k(x)}.
    $
    Then $g_n$ is a bounded measurable function with support of finite measure and $g_n -> g$ pointwise. By the bounded convergence theorem, we have
    $ 
    integral g = lim_(n -> oo) integral g_n. 
    $
    For each $n$, we have $g_n <= f_k$ for all $k >= n$, so $integral g_n <= integral f_n$, implying that
    $ 
    integral g <= liminf_(n -> oo) integral f_n.
    $
    Taking supremum over all such $g$, we obtain
    $ 
    integral liminf_(n -> oo) f_n <= liminf_(n -> oo) integral f_n.
    $
    $qed$
]

#claim[
    Suppose that $f$ is nonnegative and measurable, and $(f_n)$ is a sequence of nonnegative measurable functions such that $f_n <= f$ and $f_n -> f$ a.e. as $n -> oo$. Then
    $ 
    lim_(n -> oo) integral f_n = integral lim_(n -> oo) f_n = integral f.
    $
]
#proof[
    Since $f_n <= f$, we have $integral f_n <= integral f$ for each $n$, so $limsup_(n -> oo) integral f_n <= integral f$. On the other hand, by Fatou's lemma, we have
    $ 
    integral f = integral liminf_(n -> oo) f_n <= liminf_(n -> oo) integral f_n.
    $
    Therefore, $lim_(n -> oo) integral f_n = integral f$.
    $qed$
]

#theorem(name: "Monotone Convergence Theorem")[
    Suppose that $(f_n)$ is an increasing sequence of nonnegative measurable functions such that $f_n arrow.t f$ a.e. as $n -> oo$. Then
    $ 
    lim_(n -> oo) integral f_n = integral f.
    $
]
#proof[
    Follows from the previous corollary.
    $qed$
]

#claim[
    Consider a series of nonnegative measurable functions $sum_(k=1)^oo a_k$. Then
    $ 
    integral sum_(k=1)^oo a_k = sum_(k=1)^oo integral a_k.
    $
    If the right hand side is finite, then $sum_(k=1)^oo a_k(x)$ converges for a.e. $x$. 
]
#proof[
    Follows from the monotone convergence theorem by considering the sequence of partial sums.
    $qed$
]

Consider
$ 
f(x) = cases(
    1/|x|^(d+1) & "if" x eq.not 0, 
    0 & "if" x = 0,
)
$
We'll show that $f$ is integrable outside any ball ${x : |x| < epsilon}$. Moreover, $exists C > 0$ such that
$ 
integral_(|x| >= epsilon) f(x) d x <= C epsilon^(-1).
$
Define
$ 
A_k = {x : 2^k epsilon <= |x| < 2^(k+1) epsilon}, \
a_k(x) = (1)/((2^k epsilon)^(d+1)) chi_(A_k)(x),  quad  g(x) = sum_(k=0)^oo a_k(x).
$
Then
$ 
f(x) chi_({|x| >= epsilon)}(x) <= g(x) \
=> integral_(|x| >= epsilon) f(x) d x <= integral g(x) d x = sum_(k=0)^oo (m(A_k))/((2^k epsilon)^(d+1)). 
$
Let $A = {x : 1 <= |x| < 2}$, then $A_k = 2^k epsilon A$, so $m(A_k) = (2^k epsilon)^d m(A)$. Therefore, 
$ 
integral_(|x| >= epsilon) f(x) d x <= sum_(k=0)^oo ((2^k epsilon)^d m(A))/((2^k epsilon)^(d+1)) = m(A) epsilon^(-1) sum_(k=0)^oo 2^(-k) = 2 m(A) epsilon^(-1).
$

For general measurable $f$ on $RR^d$, we say that $f$ is Lebesgue integrable if $|f|$ is integrable. In this case, we define
$ 
integral f = integral f^+ - integral f^-,
$
where
$ 
f^+(x) = max{f(x), 0},  quad  f^-(x) = max{-f(x), 0}.
$
Since $f^+ <= |f|$ and $f^- <= |f|$, both $integral f^+$ and $integral f^-$ are finite, so $integral f$ is well-defined. 

#proposition[
    The integral does not depend on the decomposition, i.e. if $f = f_1 - f_2$ is another decomposition of $f$ with $f_1, f_2 >= 0$ and integrable, then $integral f = integral f_1 - integral f_2$.
]
#proof[
    Since $f_1 - f_2 = f^+ - f^-$, we have $f_1 + f^- = f^+ + f_2$, hence
    $ 
    integral f_1 + integral f^- = integral f^+ + integral f_2 \
    => integral f_1 - integral f_2 = integral f^+ - integral f^- = integral f.
    $
    $qed$
]

Note that the integrability of a function and the value of its integral are unchanged if we modify $f$ on a set of measure zero, so sometimes we allow our function to be undefined on sets of measure zero. When we add two integrable functions $f$ and $g$, we might encounter $oo - oo$, but this only happens on a set of measure zero, so it still makes sense to write $f + g$. When we are talking about a function $f$, in many situations we are actually talking about the collection of all functions that are equal to $f$ a.e. 

#proposition[
    Suppose that $f$ is integrable and $epsilon > 0$. Then there exists a set $B$ of finite measure such that
    $ 
    integral_(B^c) |f| < epsilon.
    $
    Also, $exists delta > 0$ such that whenever $m(E) < delta$, we have $integral_E |f| < epsilon$.
]
#proof[
    Replacing $f$ by $|f|$, we may assume that $f >= 0$. Define $f_N = f chi_(B(0, N))$, then $f_N >= 0$ is measurable, $f_N <= f_(N+1)$ and $lim_(N -> oo) f_N = f$ pointwise. By the monotone convergence theorem, we have
    $ 
    lim_(N -> oo) integral f_N = integral f < oo,
    $
    so there exists $N$ such that $integral f_N > integral f - epsilon$. Let $B = B(0, N)$, then
    $ 
    integral_(B^c) f = integral f - integral f_N < epsilon.
    $

    For the second part, define
    $ 
    E_N = {x : f(x) <= N},  quad  f_N = f chi_(E_N).
    $
    Again, $f_N >= 0$ is measurable, $f_N <= f_(N+1)$ and $lim_(N -> oo) f_N = f$ a.e. (except at the points where $f(x) = oo$). By the monotone convergence theorem, we have
    $ 
    lim_(N -> oo) integral f_N = integral f < oo,
    $
    so there exists $N$ such that $integral (f - f_N) < epsilon/2$. Let $delta = epsilon/2N$, then for every measurable set $E$ with $m(E) < delta$, we have
    $ 
    integral_E f = integral_E f_N + integral_E (f - f_N) <= N dot.op m(E) + integral (f - f_N) < epsilon/2 + epsilon/2 = epsilon.
    $
    $qed$
]

#theorem(name: "Lebesgue Dominated Convergence Theorem")[
    Suppose that $(f_n)$ is a sequence of measurable functions such that $f_n -> f$ a.e. as $n -> oo$. If $|f_n(x)| <= g(x)$ for some integrable function $g$, then
    $ 
    lim_(n -> oo) integral |f_n - f| = 0, 
    $
    hence $integral f_n -> integral f$ as $n -> oo$.
]
#proof[
    For each $N >= 0$, define
    $ 
    E_N := {x : |x| <= N, g(x) <= N}.
    $
    Let $epsilon > 0$. Similar to the previous proposition, we can find $N$ such that $integral_(E_N^c) g < epsilon/4$. Note that $|f_n chi_(E_N)| <= g chi_(E_N) <= N$ and $f_n chi_(E_N) -> f chi_(E_N)$ a.e., so by the bounded convergence theorem, we have
    $ 
    integral_(E_N) |f_n - f| < epsilon/2
    $
    for all sufficiently large $n$. Therefore, 
    $ 
    integral |f_n - f| = integral_(E_N) |f_n - f| + integral_(E_N^c) |f_n - f| <= integral_(E_N) |f_n - f| + 2integral_(E_N^c) g < epsilon
    $
    for all sufficiently large $n$, so $integral |f_n - f| -> 0$ as $n -> oo$. The convergence of $integral f_n$ follows from the triangle inequality:
    $ 
    |integral f_n - integral f| = |integral (f_n - f)| <= integral |f_n - f| -> 0.
    $
    $qed$
]

Let $f = u + i v$ be a complex-valued function, where $u, v$ are real-valued functions. We say that $f$ is measurable if both $u$ and $v$ are measurable. We say that $f$ is Lebesgue integrable if
$ 
|f(x)| = sqrt(u(x)^2 + v(x)^2)
$
is Lebesgue integrable. Note that
$ 
|u(x)|, |v(x)| <= |f(x)| <= |u(x)| + |v(x)|,
$
so $f$ is integrable iff both $u$ and $v$ are integrable. In this case, we define
$ 
integral f = integral u + i integral v.
$
Define $integral_E f = integral f chi_E$ for every measurable set $E$. It's easy to see that
$ 
{f: E -> CC mid(|) f "is integrable"}
$
forms a vector space over $CC$. 

== $L^p$-spaces

For any measurable function $f$ on $RR^d$ and $p in [1, oo)$, we define the $L^p$-norm of $f$ by
$ 
|f|_p = ( integral |f|^p )^(1/p).
$
provided that $|f|^p$ is integrable. 

#definition[
    Let $f: RR^d -> [0, oo]$ be measurable. Set
    $ 
    A = {alpha in RR : m ({x : f(x) in (alpha, oo]} ) = 0}.
     $
    Define $s = inf A$. $s$ is called the essential supremum of $f$, denoted by $|f|_oo$. In general, if $f: RR^d -> CC$ is measurable, we define $|f|_oo = ||f||_oo$.
]

It's easy to check that for all $p in [1, oo]$, we have $|f|_p >= 0$, $|a f|_p = |a| |f|_p$ for all $a in CC$, and $|f + g|_p <= |f|_p + |g|_p$. However, $|f|_p = 0$ only implies that $f = 0$ a.e. By considering equivalence classes of functions that are equal a.e., we can turn
$ 
{f: RR^d -> CC mid(|) f "is measurable", |f|_p < oo} $
into a normed vector space, denoted by $L^p(RR^d)$.

#proposition[
    If $1/p + 1/q = 1$ with $p, q in [1, oo]$, then for every $f in L^p(RR^d)$ and $g in L^q(RR^d)$, we have $f g in L^1(RR^d)$ and
    $ 
    |f g|_1 <= |f|_p |g|_q.
    $
]

#theorem[
    $L^p(RR^d)$ is a Banach space for every $p in [1, oo]$.
]
#proof[
    Let $(f_n)$ be a Cauchy sequence in $L^p(RR^d)$. Choose a subsequence $(f_(n_k))$ such that
    $ 
    |f_(n_k) - f_(n_{k+1)}|_p < 2^(-k)
    $
    for every $k >= 1$. Consider
    $ 
    f(x) = f_(n_1)(x) + sum_(k=1)^oo (f_(n_{k+1)}(x) - f_(n_k)(x)), \
    g(x) = |f_(n_1)(x)| + sum_(k=1)^oo |f_(n_{k+1)}(x) - f_(n_k)(x)|.
    $
    Note that
    $ 
    |g|_p <= |f_(n_1)|_p + sum_(k=1)^oo |f_(n_{k+1)} - f_(n_k)|_p <= |f_(n_1)|_p + 1 < oo,
    $
    so $g^p$ is integrable, hence $g(x) < oo$ a.e. Since $|f(x)| <= g(x)$, the series defining $f(x)$ converges absolutely for a.e. $x$, so $f$ is finite a.e. The partial sums of the series defining $f$ are exactly $f_(n_k)$, so $f_(n_k) -> f$ a.e. as $k -> oo$. Since $|f_(n_k) - f| <= g$ and $g$ is integrable, by the dominated convergence theorem, we have $|f_(n_k) - f|_p -> 0$ as $k -> oo$. Finally, since $(f_n)$ is a Cauchy sequence, we have $|f_n - f|_p -> 0$ as $n -> oo$, so $f_n -> f$ in $L^p(RR^d)$ as $n -> oo$.

    If $p = oo$, let
    $ 
    A_k := {x in RR^d : |f_k(x)| > |f_k|_oo}, \
    B_(m, n) := {x in RR^d : |f_m(x) - f_n(x)| > |f_m - f_n|_oo}.
    $
    Write $E = union.big_(k=1)^oo A_k union union.big_(m, n=1)^oo B_(m, n)$, then $m(E) = 0$. On $E^c$, the sequence $(f_n)$ converges uniformly to a bounded function $f$. Here, we use the fact that the space of bounded functions is complete under the supremum norm. Define $f(x) = 0$ for $x in E$, then $f in L^oo(RR^d)$ and $|f_n - f|_oo -> 0$ as $n -> oo$.
    $qed$
]

#claim[
    If $(f_n)$ converges to $f$ in $L^p(RR^d)$ for some $p in [1, oo]$, then there exists a subsequence $(f_(n_k))$ such that $f_(n_k) -> f$ a.e. as $k -> oo$.
]
#proof[
    Follows from the proof of the previous theorem by considering a subsequence of $(f_n)$ that satisfies the condition in the proof.
    $qed$
]

#theorem[
    Suppose that $p in [1, oo)$. The following families are dense in $L^p(RR^d)$:

    + The simple functions;
    + The step functions;
    + The continuous functions with compact supports.
]
#proof[
    Let $f in L^p(RR^d)$. We may assume that $f$ is nonnegative, since we may approximate its real and imaginary parts, and their positive and negative parts separately. Recall that there exists $(phi_k)$ nonnegative simple functions such that $phi_k arrow.t f$ pointwise. By the monotone convergence theorem, we have $|phi_k - f|_p -> 0$ as $k -> oo$, so (a) holds.

    For part (b), it suffices to approximate $chi_E$ by step functions where $m(E) < oo$. Recall that for every $epsilon > 0$, there exists almost disjoint closed rectangles $(R_j)$ such that
    $ 
    m(E triangle.t union.big_(j=1)^M R_j) < epsilon^p.
    $
    Then $chi_E$ and $sum_(j=1)^M chi_(R_j)$ differ only on a set of measure less than $epsilon^p$, so $|chi_E - sum_(j=1)^M chi_(R_j)|_p < epsilon$.

    For part (c), it suffices to approximate $chi_R$ by continuous functions with compact supports where $R$ is a rectangle. Consider $d = 1$, then $R = [a, b]$ for some $a < b$. Define
    $ 
    f_epsilon(x) = cases(
        0 & "if" x <= a - epsilon,
        (x - (a - epsilon))/(epsilon) & "if" a - epsilon < x < a,
        1 & "if" a <= x <= b,
        ((b + epsilon) - x)/(epsilon) & "if" b < x < b + epsilon,
        0 & "if" x >= b + epsilon,
    )
    $
    Then $f_epsilon$ is continuous with compact support and $|f_epsilon - chi_R|_p < 2epsilon$. For general $d$, we can approximate $chi_R$ by the product of $d$ such functions, which is also continuous with compact support.
    $qed$
]

#remark[
    The completeness and denseness results hold for $L^p(E)$ where $E subset.eq RR^d$ is a measurable set and $m(E) > 0$. 
]

For all $p in [1, oo)$, $|dot.op|_p$ is a norm on $C_c(RR^d)$, the space of continuous functions with compact supports. Also, the essential supremum is the same as the actual supremum for functions in $C_c(RR^d)$. Since $C_c(RR^d)$ is dense in $L^p(RR^d)$, we can identify $L^p(RR^d)$ with the completion of $C_c(RR^d)$ under the $L^p$-norm. 

Therefore, Lebesgue integration is the "correct" generalization of Riemann integration in the sense that it allows us to complete the space of continuous functions with compact supports under the $L^p$-norm. 

$L^1(RR^d)$ is the completion of the set of integrable functions under the $L^1$-norm. For $p = oo$, the $L^oo$-completion of $C_c(RR^d)$ is not $L^oo(RR^d)$, but $C_0(RR^d)$, the space of continuous functions that vanish at infinity. 

=== Invariance Properties

#definition[
    Let $f$ be a measurable function on $RR^d$. The translation of $f$ by a vector $h in RR^d$ is the function $f_h$ defined by
    $ 
    f_h(x) = f(x - h).
    $
]

#proposition[
    If $f$ is integrable, then $f_h$ is integrable and $integral f_h = integral f$ for every $h in RR^d$.
]
#proof[
    We first prove this for $f = chi_E$ where $E$ is a measurable set with finite measure. By translation invariance of Lebesgue measure, we have $m(E + h) = m(E)$, so $integral chi_E = integral chi_(E + h)$. By linearity, the result holds for simple functions. 

    If $f$ is nonnegative and integrable, then there exists a sequence of nonnegative simple functions $(phi_n)$ such that $phi_n arrow.t f$ pointwise. Then $((phi_n)_h) arrow.t f_h$ pointwise as well, so by the monotone convergence theorem, we have
    $ 
    integral f_h = lim_(n -> oo) integral (phi_n)_h = lim_(n -> oo) integral phi_n = integral f.
    $
    Finally, if $f$ is complex-valued and integrable, then $integral |f_h| = integral |f| arrow.r.squiggly f$ is integrable. By linearity again $integral f_h = integral f$.
    $qed$
]

Similarly, we can show that the Lebesgue integral is invariant under dilations: for all $a in RR backslash {0}$, we have $|a|^(d) integral f(a x) = integral f$.

A consequence of the invariance properties is the commutativity of convolution: if $f, g$ are measurable and $f(x - y)g(y)$ is integrable in $y$, then by replacing $y$ by $x - y$, we have
$ 
integral f(x - y)g(y) d y = integral f(y)g(x - y) d y.
$

By dilation invariance, for all $epsilon > 0$, 
$ 
integral_(|x| >= epsilon) 1/|x|^a  d x = epsilon^(-a + d) integral_(|x| >= 1) 1/|x|^a  d x, < oo "if" a > d, \
integral_(|x| <= epsilon) 1/|x|^a  d x = epsilon^(-a + d) integral_(|x| <= 1) 1/|x|^a  d x < oo "if" a < d.
$

#proposition[
    Let $f in L^1(RR^d)$, then $|f_h - f|_1 -> 0$ as $h -> 0$.
]
#proof[
    Let $f in L^1(RR^d)$ and $epsilon > 0$. Sine $C_c(RR^d)$ is dense in $L^1(RR^d)$, there exists $g in C_c(RR^d)$ such that $|f - g|_1 < epsilon/3$, then $|f_h - g_h|_1 < epsilon/3$ for every $h$. Since $g$ is uniformly continuous, there exists $delta > 0$ such that $|g_h - g|_1 < epsilon/3$ for every $|h| < delta$. Therefore, 
    $ 
    |f_h - f|_1 <= |f_h - g_h|_1 + |g_h - g|_1 + |g - f|_1 < epsilon
        $
    for every $|h| < delta$, so $|f_h - f|_1 -> 0$ as $h -> 0$.
    $qed$
]

== Fubini's Theorem

Let $f$ be a function on $RR^(d_1) times RR^(d_2) = RR^d$, then for fixed $y$, define $f^y(x) = f(x, y)$, and for fixed $x$, define $f_x(y) = f(x, y)$. For $E subset.eq RR^(d_1) times RR^(d_2)$, define the slices by
$ 
E^y = {x in RR^(d_1) : (x, y) in E},  quad  E_x = {y in RR^(d_2) : (x, y) in E}.
$

#theorem(name: "Fubini's Theorem")[
    Suppose that $f(x, y)$ is integrable on $RR^(d_1) times RR^(d_2)$. Then for a.e. $y in RR^(d_2)$, 
    + The slice $f^y$ is integrable on $RR^(d_1)$;
    + The function defined by $y |->^F integral_(RR^(d_1)) f^y(x)  d x$ is integrable on $RR^(d_2)$;
    + 
    $ 
    integral_(RR^(d_2)) F(y)  d y = integral_(RR^(d_2)) ( integral_(RR^(d_1)) f(x, y)  d x ) d y = integral_(RR^d) f.
    $
]
#proof[
    We assume that $f$ is real-valued, since the complex-valued case can be reduced to the real-valued case by considering the real and imaginary parts separately. 

    Let $cal(F)$ be the set of intergrable functions that satisfy all 3 conclusions in the theorem. It suffices to show that $L^1(RR^d) subset.eq cal(F)$. 

    First, we show that $cal(F)$ is a vector space. Let $f, g in cal(F)$ and $a, b in RR$. Since union of two null sets is still a null set, the conclusions holds for $a f + b g$ by linearity of the integral.

    #claim[
        If $(f_n) subset.eq cal(F)$ and $f_n arrow.t f$ or $f_n arrow.b f$ pointwise where $f$ is integrable, then $f in cal(F)$.
    ]
    #proof[
        We only prove the case $f_n arrow.t f$. Replace $f_n$ by $f_n - f_1$ so that the sequence is nonnegative. By the monotone convergence theorem, $lim_(n -> oo) integral f_n = integral f$. By assumption, for each $n$, there exists a null set $E_n$ such that $f_n^y$ is integrable for every $y in E_n^c$. Let $E = union.big_(n=1)^oo E_n$, then $m(E) = 0$. If $y in.not E$, then $f_n^y$ is integrable for every $n$. Note that
        $ 
        underbrace(integral_(RR^(d_1)) f_n^y(x)  d x}, =: g_n(y) ) arrow.t underbrace(integral_(RR^(d_1)) f^y(x)  d x, =: g(y))
        $
        as $n -> oo$ for all $y in.not E$, so by the monotone convergence theorem again, we have
        $ 
        integral_(RR^(d_2)) g(y)  d y = lim_(n -> oo) integral_(RR^(d_2)) g_n(y)  d y = lim_(n -> oo) integral f_n = integral f.
        $
        Since $f$ is integrable, $g$ is finite a.e., hence $f^y$ is integrable for a.e. $y$ and
        $ 
        integral_(RR^(d_2)) ( integral_(RR^(d_1)) f(x, y)  d x ) d y = integral f,
        $
        thus $f in cal(F)$. 
    ]

    #claim[
        If $E$ is a $G_delta$ set such that $m(E) < oo$, then $chi_E in cal(F)$.
    ]
    #proof[
        If $E$ is a bounded open cube, then write $E = I times J$, where $I, J$ are open cubes in $RR^(d_1), RR^(d_2)$ respectively. Then for each $y$, the function $chi_E(x, y)$ is measurable in $x$ and integrable with
        $ 
        g(y) := integral_(RR^(d_1)) chi_E(x, y)  d x = cases(
        m(I) & "if" y in J, 
        0 & "if" y in.not J,
        )
        $
        Therefore, $g = |I| chi_J$ is integrable, and
        $ 
        integral_(RR^(d_2)) g(y)  d y = m(I) m(J) = m(E) = integral chi_E,
        $
        so $chi_E in cal(F)$.

        If $E$ is a subset of the boundary of some closed cubes, then since $m(E) = 0$, $integral_(RR^d) chi_E = 0$. It's also easy to see that for almost every $y$, the slice $E^y$ has measure zero in $RR$, hence $integral_(RR^(d_1)) chi_E(x, y)  d x = 0$ for a.e. $y$. Therefore, $integral_(RR^(d_2)) ( integral_(RR^(d_1)) chi_E(x, y)  d x ) d y = 0$, so $chi_E in cal(F)$.

        If $E$ is a finite union of almost disjoint closed cubes, then $chi_E$ can be written as a finite linear combination of the characteristic functions of open cubes and subsets of boundaries of closed cubes, so $chi_E in cal(F)$.

        If $E$ is open and $m(E) < oo$, then $E = union.big_(j=1)^oo Q_j$, where $(Q_j)$ are almost disjoint closed cubes. Define $f_k = sum_(j=1)^k chi_(Q_j)$, then $f_k arrow.t chi_E$ pointwise, hence by the previous claim, $chi_E in cal(F)$.

        If $E$ is a $G_delta$ set such that $m(E) < oo$, then exitst open sets $(U_k)$ such that $E = inter_(k=1)^oo U_k$. Since $m(E) < oo$, there exists an open set $U_0$ of finite measure such that $E subset.eq U_0$. Define $V_k = inter_(j=0)^k U_j$, then $V_k arrow.b E arrow.r.squiggly chi_(V_k) arrow.b chi_E$ and each $V_k$ has finite measure. By the previous paragraph, $chi_(V_k) in cal(F)$ for every $k$, so by the previous claim again, $chi_E in cal(F)$.
    ]

    #claim[
        If $E$ has measure zero, then $chi_E in cal(F)$.
    ]
    #proof[
        Since $m(E) = 0$, there exists a $G_delta$ set $G$ such that $E subset.eq G$ and $m(G) = 0$. By the previous claim, $chi_G in cal(F)$ and
        $ 
        integral_(RR^(d_2)) ( integral_(RR^(d_1)) chi_G(x, y)  d x ) d y = integral chi_G = 0,
        $
        so $integral_(RR^(d_1)) chi_G(x, y)  d x = 0$ for a.e. $y$, i.e. the slice $G^y$ has measure zero for a.e. $y$. Since $E^y subset.eq G^y$, $E^y$ also has measure zero for a.e. $y$, so
        $ 
        integral_(RR^(d_2)) ( integral_(RR^(d_1)) chi_E(x, y)  d x ) d y = 0 = integral chi_E,
        $
        hence $chi_E in cal(F)$.
    ]

    #claim[
        If $E$ has finite measure, then $chi_E in cal(F)$. 
    ]
    #proof[
        Exists a $G_delta$ set $G$ of finite measure such that $E subset.eq G$ and $m(G backslash E) = 0$, so $chi_E = chi_G - chi_(G backslash E) in cal(F)$. 
    ]
    By Claim 4 and linearity, simple functions with finite measure supports are in $cal(F)$. By the monotone convergence theorem and Claim 1, every nonnegative integrable function is in $cal(F)$. Finally, by linearity again, every integrable function is in $cal(F)$.
    $qed$
]


#theorem(name: "Tonelli")[
    Suppose that $f$ is nonnegative and measurable on $RR^d = RR^(d_1) times RR^(d_2)$. Then for a.e. $y in RR^(d_2)$, 
    + The slice $f^y$ is measurable on $RR^(d_1)$;
    + The function defined by $y |->^F integral_(RR^(d_1)) f^y(x)  d x$ is measurable on $RR^(d_2)$;
    + 
    $ 
    integral_(RR^(d_2)) F(y)  d y = integral_(RR^(d_2)) ( integral_(RR^(d_1)) f(x, y)  d x ) d y = integral_(RR^d) f
    $
    where the integrals can be infinite. 
]
#proof[
    Consider the truncations
    $ 
    f_k(x, y) = cases(
        f(x, y) & "if" |(x, y)| < k "and" |f(x, y)| < k,
        0 & "otherwise",
    )
    $
    then each $f_k$ is integrable, so by Fubini's theorem, for each $k$, there exists a measure zero set $E_k subset.eq RR^(d_2)$ such that the slice $(f_k)^y$ is measurable for every $y in E_k^c$. Let $E = union.big_(k=1)^oo E_k$, then $m(E) = 0$. Since $(f_k)^y arrow.t f^y$, $f^y$ is measurable for every $y in.not E$, proving part (i). By the monotone convergence theorem, for every $y in.not E$, we have
    $ 
    integral_(RR^(d_1)) f^y(x)  d x = lim_(k -> oo) integral_(RR^(d_1)) (f_k)^y(x)  d x,
    $
    so by Fubini's theorem again, the function $F$ defined by $y |->^F integral_(RR^(d_1)) f^y(x)  d x$ is measurable, proving part (ii). Finally, by the monotone convergence theorem once more, we have
    $ 
    integral_(RR^(d_2)) F(y)  d y = lim_(k -> oo) integral_(RR^(d_2)) (integral_(RR^(d_1)) (f_k)^y(x)  d x ) d y = lim_(k -> oo) integral f_k = integral f,
    $
    proving part (iii).
    $qed$
]

Given a measurable function $f$ on $RR^d$ and we want to compute $integral f$. We can first apply Tonelli's theorem to $|f|$, then compute or estimate the iterated integrals of $|f|$ to check whether $f$ is integrable. If $f$ is integrable, then by Tonelli $integral |f| < oo$, hence $f$ is integrable, thus we can apply Fubini's theorem to complete the calculation of $integral f$.

#claim(id: "cl:slice-measurable")[
    Let $E subset.eq RR^d = RR^(d_1) times RR^(d_2)$ be a measurable set. Then for a.e. $y in RR^(d_2)$, the slice $E^y$ is measurable in $RR^(d_1)$. Also, $m(E^y)$ is a measurable function of $y$ and
    $ 
    m(E) = integral_(RR^(d_2)) m(E^y)  d y.
    $
]
#proof[
    Follows by applying Tonelli's theorem to $chi_E$.
    $qed$
]

#remark[
    The converse of the previous corollary is not true: let $N subset.eq RR$ be a nonmeasurable set and consider $E = [0, 1] times N$, then
    $ 
    E^y = cases(
        [0, 1] & "if" y in N, 
        emptyset & "if" y in.not N,
    )
    $
    so $E^y$ is measurable for every $y$. But if $E$ were measurable, then by Tonelli's theorem $E_x$ would be measurable for a.e. $x$, which is not the case since $E_x = N$ for every $x in [0, 1]$.
]

#proposition[
    If $E = E_1 times E_2$ is measurable and $m_*(E_2) > 0$, then $E_1$ is measurable. Note that $E_2$ can be nonmeasurable. 
]
#proof[
    By @cl:slice-measurable, for a.e. $y in RR^(d_2)$, 
    $ 
    (chi_E)^y(x) = chi_(E_1)(x) dot.op chi_(E_2)(y)
    $
    is measurable in $x$. If exists $y in E_2$ such that $(chi_E)^y$ is measurable, then $chi_(E_1)$ is measurable, so $E_1$ is measurable. Otherwise, for a.e. $y in E_2$, $(chi_E)^y$ is not measurable, which implies that $E_2$ is contained in a null set, contradicting the assumption that $m_*(E_2) > 0$.
    $qed$
]

#lemma[
    If $E_1 subset.eq RR^(d_1)$ and $E_2 subset.eq RR^(d_2)$, then
    $ 
    m_*(E_1 times E_2) <= m_*(E_1) m_*(E_2),
    $
    with the convention that $0 dot.op oo = 0$ and $oo dot.op oo = oo$. 
]
#proof[
    Let $epsilon > 0$. By definition of outer measure, there exists countable collections of closed cubes $(Q_j^1)$ and $(Q_k^2)$ such that $E_1 subset.eq union.big_(j=1)^oo Q_j^1$, $E_2 subset.eq union.big_(k=1)^oo Q_k^2$, and
    $ 
    sum_(j=1)^oo m(Q_j^1) <= m_*(E_1) + epsilon,  quad  sum_(k=1)^oo m(Q_k^2) <= m_*(E_2) + epsilon.
    $
    Then $E_1 times E_2 subset.eq union.big_(j, k=1)^oo Q_j^1 times Q_k^2$, so
    $
    m_*(E_1 times E_2) &<= sum_(j, k=1)^oo m(Q_j^1) m(Q_k^2) \
    &= ( sum_(j=1)^oo m(Q_j^1) ) ( sum_(k=1)^oo m(Q_k^2) ) \
    &<= (m_*(E_1) + epsilon)(m_*(E_2) + epsilon).
    $
    If both $E_1$ and $E_2$ have positive outer measures, then by letting $epsilon -> 0$, we have $m_*(E_1 times E_2) <= m_*(E_1) m_*(E_2)$. 

    Otherwise, suppose that $m_*(E_1) = 0$, then define $E_2^j = E_2 inter B(0, j)$ for each $j >= 1$. Since $E_2^j$ is now bounded, by the above argument $m_*(E_1 times E_2^j) <= m_*(E_1) m_*(E_2^j) = 0$ for every $j$. Since $E_1 times E_2^j arrow.t E_1 times E_2$, by the continuity of measure, we have $m_*(E_1 times E_2) = lim_(j -> oo) m_*(E_1 times E_2^j) = 0$.
    $qed$
]

#proposition[
    Suppose that $E_1, E_2$ are measurable, then $E = E_1 times E_2$ is measurable and $m(E) = m(E_1) m(E_2)$.
]
#proof[
    We can find $G_delta$ sets $G_1, G_2$ such that $E_j subset.eq G_j$ and $m(G_j backslash E_j) = 0$ for $j = 1, 2$. Then $G = G_1 times G_2$ is measurable. Note that
    $ 
    (G_1 times G_2) backslash (E_1 times E_2) subset.eq ((G_1 backslash E_1) times G_2) union (E_1 times (G_2 backslash E_2)).
    $
    By the previous lemma, 
    $ 
    m_*((G_1 backslash E_1) times G_2) <= m_*(G_1 backslash E_1) m_*(G_2) = 0, \
    m_*(E_1 times (G_2 backslash E_2)) <= m_*(E_1) m_*(G_2 backslash E_2) = 0,
    $
    so $m((G_1 times G_2) backslash (E_1 times E_2)) = 0$, hence $E$ is measurable. By @cl:slice-measurable, 
    $ 
    m(E) = integral_(RR^(d_2)) m(E^y)  d y = m(E_1) m(E_2).
    $
    $qed$
]

#claim[
    Suppose that $f$ is measurable on $RR^(d_1)$, then the function defined by $g(x, y) = f(x)$ is measurable on $RR^(d_1) times RR^(d_2)$. 
]
#proof[
    We may assume that $f$ is real-valued. If $a in RR$, then ${x : f(x) < a}$ is measurable, so ${(x, y) : g(x, y) < a} = {x : f(x) < a} times RR^(d_2)$ is measurable as well, hence $g$ is measurable.
    $qed$
]

#claim[
    Suppose that $f$ is nonnegative on $RR^d$. Let
    $ 
    cal(A) = {(x, y) in RR^d times RR : 0 <= y <= f(x)}.
    $
    Then $f$ is measurable if and only if $cal(A)$ is measurable, and in this case, $integral f = m(cal(A))$.
]
#proof[
    If $f$ is measurable, consider $F(x, y) = y - f(x)$, which by the previous corollary is the difference of two measurable functions hence measurable, hence $cal(A) = {y >= 0} inter {F <= 0}$ is measurable. Conversely, if $cal(A)$ is measurable, then for each $a in RR$, the slice $A_x = [0, f(x)]$ is a closed internal, hence $m(A_x) = f(x)$. By Tonelli's theorem, $x |-> m(A_x)$ is measurable, so $f$ is measurable. Finally, by Tonelli's theorem again, we have
    $ 
    integral_(RR^d) f = integral_(RR^d) m(A_x)  d x = m(cal(A)).
    $
    $qed$
]

#proposition[
    If $f$ is measurable on $RR^d$, then $g(x, y) = f(x - y)$ is measurable on $RR^d times RR^d$.
]
#proof[
    We need to show that for each $a in RR$, the set $E = {(x, y) : f(x - y) < a}$ is measurable. 
    #claim[
        If $G subset.eq RR^d$ is measurable, then $G' = {(x, y) : x - y in G}$ is measurable.
    ]
    #proof[
        If $cal(U)$ is open, then $cal(U)'$ is also open. Taking countable intersection, if $cal(U)$ is $G_delta$, then $cal(U)'$ is also $G_delta$. Define $B_k = {(x, y) : |y| <= k}$, then
        $ 
        chi_(cal(U)' inter B_k)(x, y) = chi_(cal(U))(x - y) dot.op chi_(B(0, k))(y),
        $
        hence by Tonelli's theorem, 
        $ 
        m(cal(U)' inter B_k) = integral_(RR^d) ( integral_(RR^d) chi_(cal(U))(x - y) dot.op chi_(B(0, k))(y)  d x ) d y = m(cal(U)) m(B(0, k)). 
        $
        If $m(G) = 0$, then there exists a sequence of open sets $(cal(U)_j)$ such that $G subset.eq cal(U)_j$ and $m(cal(U)_j) -> 0$ as $j -> oo$, so $m(cal(U)_j' inter B_k) -> 0$ as well, hence $m(G' inter B_k) = 0$ for every $k$. Since $G' inter B_k arrow.t G'$, by the continuity of measure, we have $m(G') = lim_(k -> oo) m(G' inter B_k) = 0$. Since every measurable set can be written as the difference of a $G_delta$ set and a null set, the result follows. 
        $qed$
    ]
    By the claim, let $F = {x : f(x) < a}$, then $E = F'$, so $E$ is measurable, hence $g$ is measurable.
    $qed$
]

=== Convolution

Recall that the convolution of two functions $f, g$ defined by
$ 
(f * g)(x) = integral_(RR^d) f(x - y) g(y)  d y,
$
which makes sense only when $f(x - y) g(y)$ is integrable in $y$. 

#proposition[
    If $f, g in L^1(RR^d)$, then $f * g in L^1(RR^d)$. Moreover, $|f * g|_1 <= |f|_1 |g|_1$. 
]
#proof[
    Define $h(x, y) = f(x - y) g(y)$, then $h$ is measurable on $RR^d times RR^d$. By Tonelli's theorem,
    $
    integral_(RR^d times RR^d) |h(x, y)|  d x d y &= integral_(RR^d) ( integral_(RR^d) |f(x - y) g(y)|  d x ) d y \
    &= integral_(RR^d) |g(y)| ( integral_(RR^d) |f(x - y)|  d x ) d y = |f|_1 |g|_1 < oo,
    $
    so $h$ is integrable. By Fubini's theorem, $integral_(RR^d) |f(x - y) g(y)|  d y < oo$ for a.e. $x$, so $f * g$ is well-defined a.e. and
    $
    |f * g|_1 &= integral_(RR^d) | integral_(RR^d) f(x - y) g(y)  d y | d x \
    &<= integral_(RR^d) integral_(RR^d) |f(x - y) g(y)|  d y d x = |f|_1 |g|_1.
    $
    $qed$
]

#proposition[
    Suppose that $f, g in L^1(RR)$ such that $g$ is differentiable and $g'$ is uniformly bounded. Then $f * g$ is differentiable and $(f * g)' = f * g'$.
]
#proof[
    For $h eq.not 0$, we have
    $ 
    ((f * g)(x + h) - (f * g)(x))/(h) = integral_(RR) f(y) (g(x + h - y) - g(x - y))/(h)  d y.
    $
    Let $M > 0$ be a bound for $|g'|$. By the mean value theorem, there exists $xi$ between $x + h - y$ and $x - y$ such that
    $ 
    |(g(x + h - y) - g(x - y))/(h)| = |g'(xi)| <= M \
    => |f(y) (g(x + h - y) - g(x - y))/(h)| <= M |f(y)|. 
    $
    By the dominated convergence theorem, 
    $ 
    (f * g)'(x) = lim_(h -> 0) ((f * g)(x + h) - (f * g)(x))/(h) = integral_(RR) f(y) g'(x - y)  d y = (f * g')(x).
    $
    $qed$
]

= Differentiation and Integration

In this chapter, we will study the relationship between differentiation and integration. We will see that under some mild assumptions, differentiation and integration are inverse operations of each other.

== Differentiation of the Integral

If $f$ is integrable on $[a, b]$, we define
$ 
F(x) = integral_a^x f(y) d y
$
Consider the derivative
$ 
lim_(h -> 0) (F(x + h) - F(x))/(h). 
$
For simplicity, assume that $h > 0$. The difference quotient can be written as
$ 
(F(x + h) - F(x))/(h) = 1/h integral_x^(x + h) f(t)  d t = 1/|I| integral_I f(y) d y,
$
where $I = [x, x + h]$. As $|I| -> 0$, we expect that the average tends to $f(x)$, but this is not always the case. We generalize this to higher dimensions. Suppose $f$ is integrable on $RR^d$, then we want to know that whether
$ 
lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B f(y)  d y = f(x)
$
for a.e. $x$, where $B$ ranges over all open balls containing $x$.

=== The hardy-Littlewood Maximal Function

#definition[
    If $f in L^1(RR^d)$, define the (Hardy-Littlewood) maximal function of $f$ by
    $ 
    f^*(x) = sup_(B in.rev x) (1)/(m(B)) integral_B |f(y)|  d y,
    $
    where $B$ ranges over all open balls containing $x$.
]

#proposition[
    $f^*$ is measurable. 
]
#proof[
    Let $alpha > 0$ and let $E_alpha = {x : f^*(x) > alpha}$. Let $y in E_alpha$, then there exists an open ball $B$ containing $y$ such that
    $ 
    (1)/(m(B)) integral_B |f| > alpha.
    $
    Since $B$ is open, there exists $epsilon > 0$ such that $B(y, epsilon) subset.eq B$, so for every $x in B(y, epsilon)$, we have
    $ 
    (1)/(m(B)) integral_B |f| > alpha,
    $
    hence $B(y, epsilon) subset.eq E_alpha$. Therefore, $E_alpha$ is open, so $f^*$ is measurable.
    $qed$
]

#lemma(name: "Vitali Covering Lemma")[
    Suppose that $cal(B) = {B_1, ..., B_N}$ is a finite collection of open balls in $RR^d$. Then there exists a disjoint subcollection ${B_(i_1), ..., B_(i_k)}$ of $cal(B)$ such that
    $ 
    m( union.big_(l=1)^N B_l ) <= 3^d sum_(j=1)^k m(B_(i_j)).
    $
]
#proof[
    We adopt the notation that $c B(x, r) = B(x, c r)$ throughout this proof. 

    Suppose $B$ and $B'$ are two open balls that intersect with the radius of $B'$ not larger than that of $B$, then clearly $B' subset.eq 3 B$. 

    We construct the desired subcollection by induction. Let $B_(i_1)$ be a ball in $cal(B)$ with the largest radius, then delete all the balls that intersect with $B_(i_1)$ from $cal(B)$. Let $B_(i_2)$ be a ball in the remaining collection with the largest radius, then delete all the balls that intersect with $B_(i_2)$ from the remaining collection. We repeat this process until there is no ball left. Since the collection is finite, the process will terminate after finitely many steps, and we end up with a disjoint subcollection ${B_(i_1), ..., B_(i_k)}$. By the above observation, every ball in $cal(B)$ is contained in $3 B_(i_j)$ for some $j$, so
    $ 
    m( union.big_(l=1)^N B_l ) <= m( union.big_(j=1)^k 3 B_(i_j) ) <= 3^d sum_(j=1)^k m(B_(i_j)).
    $
    $qed$
]

#theorem[
    Suppose $f$ is integrable on $RR^d$, then
    $ 
    m({x : f^*(x) > alpha}) <= 3^d/alpha |f|_1,
    $
    for every $alpha > 0$.
]
#proof[
    Write $E_alpha = {x : f^*(x) > alpha}$. If $x in E_alpha$, then there exists an open ball $B_x$ containing $x$ such that
    $ 
    (1)/(m(B_x)) integral_(B_x) |f(y)|  d y > alpha <=> m(B_x) < 1/alpha integral_(B_x) |f(y)| d y.
    $
    Let $K subset.eq E_alpha$ be a compact set, then ${B_x : x in E_alpha}$ is an open cover of $K$, so there exists a finite subcover, say ${B_(x_1), ..., B_(x_N)}$. By the Vitali covering lemma, there exists a disjoint subcollection ${B_(x_(i_1)), ..., B_(x_(i_k))}$ such that
    $ 
    m(K) &<= m( union.big_(l=1)^N B_(x_l) ) <= 3^d sum_(j=1)^k m(B_(x_(i_j))) \
    &< 3^d/alpha sum_(j=1)^k integral_(B_(x_(i_j))) |f(y)|  d y = 3^d/alpha integral_(union.big_(j=1)^k B_(x_(i_j))) |f(y)|  d y <= 3^d/alpha |f|_1.
    $
    By inner regularity of Lebesgue measure, we have
    $ 
    m(E_alpha) = sup{m(K) : K subset.eq E_alpha "is compact"} <= 3^d/alpha |f|_1.
    $
]

#theorem(name: "Lebesgue Differentiation Theorem")[
    If $f in L^1(RR^d)$, then for a.e. $x in RR^d$,
    $ 
    lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B f(y)  d y = f(x).
    $
]
#proof[
    For $alpha > 0$, define
    $ 
    E_alpha = {x : limsup_(m(B) -> 0 \ B in.rev x) |(1)/(m(B)) integral_B f(y)  d y - f(x)| > alpha}.
    $
    We claim that $m(E_alpha) = 0$ for all $alpha > 0$. 

    Fix $alpha, epsilon > 0$. Recall that there exists $g in C_c(RR^d)$ such that $|f - g|_1 < epsilon$. By continuity, 
    $ 
    lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B g(y)  d y = g(x)
    $
    for every $x$. Write
    $ 
    (1)/(m(B)) integral_B f(y)  d y - f(x) \
    = (1)/(m(B)) integral_B (f(y) - g(y))  d y + (1)/(m(B)) integral_B g(y)  d y - g(x) + g(x) - f(x) \
    => limsup_(m(B) -> 0 \ B in.rev x) |(1)/(m(B)) integral_B f(y)  d y - f(x)| <= (f - g)^*(x) + |g(x) - f(x)|. 
    $
    Define
    $ 
    F_alpha = {x : (f - g)^*(x) > alpha/2},  quad  G_alpha = {x : |g(x) - f(x)| > alpha/2},
    $
    then $E_alpha subset.eq F_alpha union G_alpha$. Note that
    $ 
    m(G_alpha) <= 2/alpha |f - g|_1 <= 2/alpha epsilon
    $
    by Markov's inequality, and
    $ 
    m(F_alpha) <= 3^d/alpha/2 |f - g|_1 <= 2 dot.op 3^d/alpha epsilon,
    $
    by the previous theorem, so $m(E_alpha) <= m(F_alpha) + m(G_alpha) <= (2(3^d + 1))/(alpha) epsilon$. Since $epsilon$ is arbitrary, we have $m(E_alpha) = 0$ for every $alpha > 0$, hence
    $union.big_(n=1)^oo E_(1/n)$ has measure zero, i.e. for a.e. $x$,
    $ 
    limsup_(m(B) -> 0 \ B in.rev x) |(1)/(m(B)) integral_B f(y) d y - f(x)| = 0,
    $
    which is equivalent to the desired conclusion.
    $qed$
]

#claim[
    $f^*(x) >= |f(x)|$ for a.e. $x$.
    
]
#proof[
    By applying the Lebesgue differentiation theorem to $|f|$, we have
    $ 
    |f(x)| = lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B |f(y)|  d y <= f^*(x)
    $
    for a.e. $x$.
    $qed$
]

The class $L^1(RR^d)$ is the globally integrable functions, but since differentiation is a local property, we expect that the Lebesgue differentiation theorem should hold for functions that are locally integrable. 

#definition[
    A measurable function $f$ on $RR^d$ is locally integrable if for every ball $B$, the function $f dot.op chi_B$ is integrable. The space of all locally integrable functions on $RR^d$ is denoted by $L^1_("loc")(RR^d)$.
]

#example[
    $f(x) = x$ is locally integrable on $RR$, but not integrable. 
]

Clearly, the Lebesgue differentiation theorem also holds for locally integrable functions, since the average of $f$ over a ball $B$ is the same as the average of $f dot.op chi_B$ over $B$.

#definition[
    If $E subset.eq RR^d$ is measurable and $x in RR^d$, we say that $x$ is a density point of $E$ if
    $ 
    lim_(m(B) -> 0 \ B in.rev x) (m(E inter B))/(m(B)) = 1.
    $
]

#claim[
    If $E subset.eq RR^d$ is measurable, then for a.e. $x in E$, $x$ is a density point of $E$, and for a.e. $x in E^c$, $x$ is not a density point of $E$.
]
#proof[
    Apply the Lebesgue differentiation theorem to $chi_E$.
    $qed$
]

#definition[
    Let $f in L^1_("loc")(RR^d)$. The Lebesgue set of $f$ is the set of all points $x in RR^d$ such that $|f(x)| < oo$ and
    $ 
    lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B |f(y) - f(x)|  d y = 0.
    $
]

If $f$ is continuous at $x$, then $x$ belongs to the Lebesgue set of $f$. If $x$ belongs to the Lebesgue set of $f$, then by the triangle inequality, we have
$ 
lim_(m(B) -> 0 \ B in.rev x) integral_B f(y)  d y = f(x).
$

#claim[
    If $f in L^1_("loc")(RR^d)$, then for a.e. $x$, $x$ belongs to the Lebesgue set of $f$.
]
#proof[
    For each $r in QQ$, by the Lebesgue differentiation theorem, exists a set $E_r$ of measure zero such that for every $x in.not E_r$,
    $ 
    lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B |f(y) - r|  d y = |f(x) - r|.
    $
    Let $E = union.big_(r in QQ) E_r$, then $m(E) = 0$. Suppose that $x in.not E$ and $|f(x)| < oo$. Let $epsilon > 0$ and choose $r in QQ$ such that $|f(x) - r| < epsilon/2$, then
    $
    & (1)/(m(B)) integral_B |f(y) - f(x)|  d y <= (1)/(m(B)) integral_B |f(y) - r|  d y + |r - f(x)| \
    => & limsup_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B |f(y) - f(x)|  d y <= 2 |f(x) - r| < epsilon.
    $
    Since $epsilon$ is arbitrary, we have
    $ 
    lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B |f(y) - f(x)|  d y = 0,
    $
    so $x$ belongs to the Lebesgue set of $f$.
    $qed$
]

#remark[
    Recall that elements of $L^1(RR^d)$ are equivalence classes of functions that may differ on a measure zero set, but the set
    $ 
    {x in RR^d : "the limit" lim_(m(B) -> 0 \ B in.rev x) (1)/(m(B)) integral_B f(y)  d y "exists" }
    $
    is independent of the choice of representatives. Nevertheless, the Lebesgue set of $f$ may depend on the choice of representatives. 
]

== Approximation to the Identity

#definition[
    A family of functions $(K_delta)_(delta > 0)$ on $RR^d$ is an approximation to the identity if they are integrable and exists a constant $A > 0$ such that
    
    + $integral_(RR^d) K_delta(x)  d x = 1$ for every $delta > 0$;
    + $|K_delta(x)| <= A delta^(-d)$ for all $delta > 0$ and $x in RR^d$;
    + $|K_delta(x)| <= A delta |x|^(-d - 1)$ for all $delta > 0$ and $x in RR^d$. 
]

#proposition[
    If $(K_delta)_(delta > 0)$ is an approximation to the identity, then exists a constant $C > 0$ such that
    $ 
    integral_(RR^d) |K_delta(x)|  d x <= C
    $
    for every $delta > 0$.
]
#proof[
    Recall that
    $ 
    integral_(|x| >= epsilon) (d x)/(|x|^(d + 1)) <= C'/epsilon
    $
    for some constant $C' > 0$. By the properties of $K_delta$, we have
    $ 
    integral_(RR^d) |K_delta(x)|  d x &= integral_(|x| < delta) |K_delta(x)|  d x + integral_(|x| >= delta) |K_delta(x)|  d x \
    &<= A integral_(|x| < delta) delta^(-d)  d x + A integral_(|x| >= delta)delta |x|^(-d - 1)  d x \
    &<= A m(B(0, 1)) + A C' = C.
    $
    $qed$
]

#proposition[
    If $(K_delta)_(delta > 0)$ is an approximation to the identity, then for every $eta > 0$, 
    $ 
    lim_(delta -> 0) integral_(|x| >= eta) |K_delta(x)|  d x = 0.
    $
]
#proof[
    By the properties of $K_delta$, we have
    $ 
    integral_(|x| >= eta) |K_delta(x)|  d x <= A integral_(|x| >= eta) delta |x|^(-d - 1)  d x <= A C' delta/eta -> 0
    $
    as $delta -> 0$.
    $qed$
]

#lemma[
    Suppose that $f in L^1(RR^d)$ and $x$ belongs to the Lebesgue set of $f$. For $r > 0$, define
    $ 
    A(r) = 1/r^d integral_(|y| <= r) |f(x - y) - f(x)|  d y.
    $
    Then $A$ is continuous on $(0, oo)$, $lim_(r -> 0) A(r) = 0$ and exists $M > 0$ such that $A(r) <= M$ for every $r > 0$.
]
#proof[
    Recall that if $f in L^1(RR^d)$ and $epsilon > 0$, then exists $delta > 0$ such that for every measurable set $E$ with $m(E) < delta$, we have $integral_E |f| < epsilon$. Clearly $f(x - y) - f(x)$ is integrable in $y$, so by absolute continuity of the integral, $A$ is continuous on $(0, oo)$.

    Since $x$ belongs to the Lebesgue set of $f$, $A(r) -> 0$ as $r -> 0$ by definition. Since $A$ is continuous, it implies that $A$ is bounded on $(0, 1]$. On the other hand, for $r > 1$, we have
    $ 
    A(r) &<= 1/r^d integral_(|y| <= r) |f(x - y)|  d y + 1/r^d integral_(|y| <= r) |f(x)|  d y \
    &<= 1/r^d |f|_1 + m(B(0, 1)) |f(x)| < oo.
    $
    $qed$
]

#theorem[
    If $(K_delta)_(delta > 0)$ is an approximation to the identity and $f in L^1(RR^d)$, then
    $ 
    lim_(delta -> 0) (f * K_delta)(x) = f(x)
    $
    for all $x$ in the Lebesgue set of $f$. In particular, the limit holds for a.e. $x$.
]
#proof[
    Write
    $ 
    (f * K_delta)(x) - f(x) = & integral_(RR^d) f(x - y)K_delta(y)  d y - f(x) \
    = & integral_(RR^d) (f(x - y) - f(x)) K_delta(y)  d y, \
    => |(f * K_delta)(x) - f(x)| &<= integral_(RR^d) |f(x - y) - f(x)| |K_delta(y)|  d y \
    = & integral_(|y| < delta) |f(x - y) - f(x)| |K_delta(y)|  d y \
    & + sum_(k=0)^oo integral_(2^k delta <= |y| < 2^(k + 1) delta) |f(x - y) - f(x)| |K_delta(y)|  d y. 
    $
    By the previous lemma, we have
    $ 
    integral_(|y| < delta) |f(x - y) - f(x)| |K_delta(y)|  d y &<= C/delta^d integral_(|y| < delta) |f(x - y) - f(x)|  d y = C A(delta). 
    $
    For $k >= 0$, we have
    $ 
    integral_(2^k delta <= |y| < 2^(k + 1) delta) |f(x - y) - f(x)| |K_delta(y)|  d y &<= (C delta)/((2^k delta)^(d + 1)) integral_(|y| < 2^(k + 1) delta) |f(x - y) - f(x)|  d y \
    &<= C'/2^k A(2^(k + 1) delta).
    $
    Therefore,
    $ 
    |(f * K_delta)(x) - f(x)| <= C A(delta) + C' sum_(k=0)^oo 1/2^k A(2^(k + 1) delta).
    $
    Let $epsilon > 0$. Choose $N$ large such that $sum_(k=N)^oo 1/2^k < epsilon$, then choose $delta$ small enough such that $A(2^(k + 1) delta) < epsilon/N$ for every $0 <= k < N$. Since $A$ is bounded, we have
    $ 
    |(f * K_delta)(x) - f(x)| &<= C epsilon + C' sum_(k=0)^(N - 1) 1/2^k dot.op epsilon/N + C' sum_(k=N)^oo 1/2^k dot.op M \
    &< (C + C' + C' M) epsilon,
    $
    so $lim_(delta -> 0) (f * K_delta)(x) = f(x)$.
    $qed$
]

#theorem[
    Suppose that $f in L^1(RR^d)$ and $(K_delta)_(delta > 0)$ is an approximation to the identity, then $f * K_delta in L^1(RR^d)$ and $|f * K_delta - f|_1 -> 0$ as $delta -> 0$.
]
#proof[
    Write $f_h(x) = f(x + h)$, then
    $ 
    |(f * K_delta)(x) - f(x)| &<= integral_(RR^d) |f(x - y) - f(x)| |K_delta(y)|  d y \
    &= integral_(RR^d) |f_(-y)(x) - f(x)| |K_delta(y)|  d y.
    $
    By Tonelli's theorem,
    $ 
    |f * K_delta - f|_1 &<= integral_(RR^d) integral_(RR^d) |f_(-y)(x) - f(x)| |K_delta(y)|  d y  d x \
    &= integral_(RR^d) |f_(-y) - f|_1 |K_delta(y)|  d y.
    $
    Recall that if $f in L^1(RR^d)$, then $|f_h - f|_1 -> 0$ as $h -> 0$. Let $epsilon > 0$, then exists $eta > 0$ such that $|f_h - f|_1 < epsilon$ for every $|h| < eta$. By the properties of $K_delta$, we have
    $ 
    |f * K_delta - f|_1 &<= integral_(|y| < eta) |f_(-y) - f|_1 |K_delta(y)|  d y + integral_(|y| >= eta) |f_(-y) - f|_1 |K_delta(y)|  d y \
    &<= C epsilon + 2 |f|_1 integral_(|y| >= eta) |K_delta(y)|  d y -> C epsilon
    $
    as $delta -> 0$, so $|f * K_delta - f|_1 -> 0$ as $delta -> 0$.
    $qed$
]

== Differentiability of functions

We want to find a class of functions that satisfies the fundamental theorem of calculus:
$ 
F(b) - F(a) = integral_a^b F'(x)  d x.
$

#definition[
    Let $F: [a, b] -> CC$ be a function, and let $a = t_0 < t_1 < dots.c < t_N = b$ be a partition of $[a, b]$. The variation of $F$ on this partition is
    $ 
    sum_(j=1)^N |F(t_j) - F(t_(j - 1))|.
    $
    $F$ is of bounded variation if the variations of $F$ on all partitions are uniformly bounded, i.e. 
    $ 
    sup sum_(j=1)^N |F(t_j) - F(t_(j - 1))| < oo. 
    $
]

If $cal(P)$ is a partition of $[a, b]$ and $cal(P)'$ is a refinement of $cal(P)$, then the variation of $F$ on $cal(P)'$ is at least that of $F$ on $cal(P)$. 

#definition[
    The total variation of $F$ on $[a, x]$ (where $a <= x <= b$) is defined by
    $ 
    T_F(a, x) = sup sum_(j=1)^N |F(t_j) - F(t_(j - 1))|,
    $
    where the supremum is taken over all partitions of $[a, x]$. If $F$ is real-valued, the positive variation of $F$ on $[a, x]$ is
    $ 
    P_F(a, x) = sup sum_((+)) (F(t_j) - F(t_(j - 1))),
    $
    where the supremum is taken over all partitions of $[a, x]$ and the sum is taken over all $j$ such that $F(t_j) - F(t_(j - 1)) >= 0$. Similarly, the negative variation of $F$ on $[a, x]$ is
    $ 
    N_F(a, x) = sup sum_((-)) (F(t_(j - 1)) - F(t_j)),
    $
    where the supremum is taken over all partitions of $[a, x]$ and the sum is taken over all $j$ such that $F(t_j) - F(t_(j - 1)) <= 0$.
]

#lemma[
    Suppose that $F$ is real-valued and of bounded variation on $[a, b]$, then for all $x in [a, b]$, 
    $ 
    F(x) - F(a) = P_F(a, x) - N_F(a, x),  quad  T_F(a, x) = P_F(a, x) + N_F(a, x).
    $
]
#proof[
    Let $epsilon > 0$, then exists a partition $cal(P)$ of $[a, x]$ such that
    $ 
    |P_F(a, x) - sum_((+)) (F(t_j) - F(t_(j - 1)))| < epsilon/2,  quad  |N_F(a, x) - sum_((-)) (F(t_(j - 1)) - F(t_j))| < epsilon/2.
    $
    Therefore,
    $ 
    F(x) - F(a) = sum_(j=1)^N (F(t_j) - F(t_(j - 1))) = sum_((+)) (F(t_j) - F(t_(j - 1))) - sum_((-)) (F(t_(j - 1)) - F(t_j)) \
    => |F(x) - F(a) - (P_F(a, x) - N_F(a, x))| < epsilon.
    $

    For the second identity, we have
    $ 
    sum_(j=1)^N |F(t_j) - F(t_(j - 1))| = sum_((+)) (F(t_j) - F(t_(j - 1))) + sum_((-)) (F(t_(j - 1)) - F(t_j))
    $
    for every partition $cal(P)$ of $[a, x]$, so
    $ 
    T_F(a, x) <= P_F(a, x) + N_F(a, x).
    $
    On the other hand, let $epsilon > 0$, then exists a partition $cal(P)$ of $[a, x]$ such that
    $ 
    |T_F(a, x) - sum_(j=1)^N |F(t_j) - F(t_(j - 1))|| < epsilon.
    $ Since
    $ 
    sum_(j=1)^N |F(t_j) - F(t_(j - 1))| = P_F(a, x) + N_F(a, x),
    $
    we have $T_F(a, x) <= P_F(a, x) + N_F(a, x) + epsilon$. Since $epsilon$ is arbitrary, we have
    $T_F(a, x) <= P_F(a, x) + N_F(a, x)$, hence $T_F(a, x) = P_F(a, x) + N_F(a, x)$.
    $qed$
]

#claim[
    A real-valued function $F$ on $[a, b]$ is of bounded variation if and only if $F$ is a difference of two increasing bounded functions.
]
#proof[
    Since increasing functions are of bounded variation, the difference of two increasing bounded functions is also of bounded variation. Conversely, if $F$ is of bounded variation, then we can set $F_1(x) = P_F(a, x) + F(a)$ and $F_2(x) = N_F(a, x)$, then $F_1$ and $F_2$ are increasing bounded functions and $F = F_1 - F_2$.
    $qed$
]

As a consequence, any complex-valued function of bounded variation can be written as a linear combination of four increasing bounded functions.

#lemma(id: "lm:rising_sun", name: "Rising Sun Lemma")[
    Suppose that $G$ is real-valued and continuous on $RR$. Let
    $ 
    E = {x : G(x + h) > G(x) "for some" h > 0}. 
    $
    If $E eq.not emptyset$, then it is open, and we can write $E = union.big_(n=1)^oo (a_n, b_n)$, where $(a_n, b_n)$ are disjoint open intervals. Moreover, if $(a_k, b_k)$ is a finite interval, then $G(a_k) = G(b_k)$. 
]
#proof[
    Since $G$ is continuous, we can easily see that $E$ is open. If $(a_k, b_k)$ is a finite interval, then $a_k in.not E$ hence we cannot have $G(b_k) > G(a_k)$. Suppose that $G(a_k) > G(b_k)$. By continuity, there exists $c in (a_k, b_k)$ such that
    $ 
    G(c) = (G(a_k) + G(b_k))/(2). 
    $
    We may choose $c$ to be the rightmost such point, then $c in E$, so there exists some $d > c$ such that $G(d) > G(c)$. Since $b_k in.not E$, we have $G(x) <= G(b_k)$ for every $x >= b_k$, so
    $
    G(d) > G(c) = (G(a_k) + G(b_k))/(2) > G(b_k) arrow.r.squiggly d < b_k. 
    $
    By continuity, there exists $c' in (d, b_k)$ such that $G(c') = G(c) = (G(a_k) + G(b_k))/(2)$, which contradicts the choice of $c$.
    $qed$
]

#remark[
    If $G: [a, b] -> RR$ is continuous and
    $ 
    E = {x in (a, b) : G(x + h) > G(x) "for some" h > 0},
    $
    then the above lemma still holds, with the exception that if $a_k = a$, then we can only conclude that $G(a_k) <= G(b_k)$. 
]

#theorem[
  If $F$ is of bounded variation, then $F$ is differentiable a.e. 
]
#proof[
    It suffices to show that an increasing bounded function is differentiable a.e., and since increasing functions only have countably many discontinuities, we can assume that $F$ is continuous. 

    Define the difference quotient of $F$ at $x$ by
    $ 
    Delta_h (F)(x) = (F(x + h) - F(x))/(h).
    $
    The Dini derivatives of $F$ at $x$ are defined by
    $ 
    D^+ (F)(x) = limsup_(h -> 0^+) Delta_h(F)(x),  quad  D_+ (F)(x) = liminf_(h -> 0^+) Delta_h(F)(x), \
    D^- (F)(x) = limsup_(h -> 0^-) Delta_h(F)(x),  quad  D_- (F)(x) = liminf_(h -> 0^-) Delta_h(F)(x).
    $
    Our goal is to show that the Dini derivatives are finite and equal for a.e. $x$. Clearly $D_+ (F)(x) <= D^+ (F)(x)$ and $D_- (F)(x) <= D^- (F)(x)$ for every $x$. It suffices to show that

    + $D^+ (F)(x) < oo$ for a.e. $x$;
    + $D^+ (F)(x) <= D_- (F)(x)$ for a.e. $x$.

    Indeed, by applying (ii) to $-F(-x)$, we get $D^-(F)(x) <= D_+(F)(x)$ for a.e. $x$, hence
    $ 
    D_+(F)(x) <= D^+(F)(x) <= D_-(F)(x) <= D^-(F)(x) <= D_+(F)(x) < oo
    $
    for a.e. $x$, so $F$ is differentiable a.e.

    For (i), let
    $ 
    E_gamma = {x in [a, b): D^+(F)(x) > gamma}
    $
    for $gamma > 0$. Let $G(x) = F(x) - gamma x$, then by @lm:rising_sun, we have
    $ 
    E := {x in (a, b) : G(x + h) > G(x) "for some" h > 0} \
    = {x in (a, b) : (F(x + h) - F(x))/(h) > gamma "for some" h > 0} \
    => E_gamma backslash {a} subset.eq E = union.big_(n=1)^oo (a_n, b_n).
    $
    We have $G(a_n) <= G(b_n) arrow.r.squiggly F(b_n) - F(a_n) >= gamma (b_n - a_n)$ for every $n$, so
    $
    m(E_gamma) &<= sum_(n=1)^oo (b_n - a_n) <= 1/gamma sum_(n=1)^oo (F(b_n) - F(a_n)) \
    &<= 1/gamma (F(b) - F(a)). 
    $
    As $gamma -> oo$, we have $m(E_gamma) -> 0$, so $D^+(F)(x) < oo$ for a.e. $x$.

    For (ii), fix rational numbers $r < R$ and let
    $ 
    H = {x in (a, b) : D_-(F)(x) < r < R < D^+(F)(x)}.
    $
    If we can show that $m(H) = 0$, then taking union over all rational numbers $r < R$ gives
    $ 
    {x in (a, b) : D_-(F)(x) < D^+(F)(x)} = union.big_(r < R) H
    $
    has measure zero, hence $D^+(F)(x) <= D_-(F)(x)$ for a.e. $x$.

    Assume $m(H) > 0$ and $R/r > 1$. By outer regularity, there exists an open set $cal(U)$ such that $H subset.eq cal(U) subset.eq (a, b)$ such that $m(cal(U)) < m(H) dot.op R/r$. Write $cal(U) = union.big_(n=1)^oo I_n$, where $I_n$ are disjoint open intervals. We may assume that $I_n inter H eq.not emptyset$ for every $n$, otherwise we can just remove those intervals. Fix $n$ and define
    $ 
    E_n = {x in -I_n : G(x + h) > G(x) "for some" h > 0}.
    $
    Note that if $x in (-I_n) inter (-F)$, then
    $ 
    (F(-x + h) - F(-x))/(h) < r "for some" h > 0 => G(x + h) > G(x) => x in E_n,
    $
    so $(-I_n) inter (-F) subset.eq E_n$, in particular $E_n$ is nonempty. By @lm:rising_sun, we can write $-E_n = union.big_(k=1)^oo (a_k, b_k)$ so that
    $ 
    G(b_k) <= G(a_k) arrow.r.squiggly F(b_k) - F(a_k) <= r (b_k - a_k)
    $
    We then apply @lm:rising_sun to each interval $(a_k, b_k)$ again to $G(x) = F(x) - R x$, we then obtain a family of disjoint open intervals $cal(O)_n = union.big_(k, j) (a_(k, j), b_(k, j))$ such that
    $ 
    G(a_(k, j)) <= G(b_(k, j)) arrow.r.squiggly F(b_(k, j)) - F(a_(k, j)) >= R (b_(k, j) - a_(k, j))
    $
    for every $j$. Using the fact that $F$ is increasing, we have
    $ 
    m(cal(O)_n) &= sum_(k, j) (b_(k, j) - a_(k, j)) <= 1/R sum_(k, j) (F(b_(k, j)) - F(a_(k, j))) \
    &<= 1/R sum_k (F(b_k) - F(a_k)) <= r/R sum_k (b_k - a_k) <= r/R m(I_n).
    $
    Note that $cal(O)_n supset H inter I_n$ since $D^+(F)(x) > R$ and $D_-(F)(x) < r$ for every $x in H inter I_n$. Therefore,
    $ 
    m(H) = sum_n m(H inter I_n) <= sum_n m(cal(O)_n) <= r/R sum_n m(I_n) = r/R m(cal(U)) < m(H),
    $
    which is a contradiction. Hence $m(H) = 0$.
    $qed$
]

#claim(id: "cl:bound_integral_derivative")[
    If $F$ is increasing and continuous on $[a, b]$, then $F'$ exists a.e. Moreover, $F'$ is measurable, nonnegative and
    $ 
    integral_a^b F'(x)  d x <= F(b) - F(a).
    $
    In particular, if $F$ is bounded on $RR$, then $F' in L^1(RR)$.
]
#proof[
    Since $F'(x) = lim_(n -> oo) (f(x + 1/n) - f(x)) n$ for every $x$ such that $F'(x)$ exists, $F'$ is measurable. By Fatou's lemma, we have
    $ 
    integral_a^b F'(x)  d x &<= liminf_(n -> oo) integral_a^b (F(x + 1/n) - F(x)) n  d x \
    &= liminf_(n -> oo) ( n integral_a^b F(x + 1/n)  d x - n integral_a^b F(x)  d x ) \
    &= liminf_(n -> oo) ( n integral_(a + 1/n)^(b + 1/n) F(x)  d x - n integral_a^b F(x)  d x ) \
    &= liminf_(n -> oo) ( n integral_b^(b + 1/n) F(x)  d x - n integral_a^(a + 1/n) F(x)  d x ) = F(b) - F(a).
    $
    $qed$
]

In general, the inequality $integral_a^b F'(x)  d x <= F(b) - F(a)$ can be strict. For example, if $F$ is the Cantor function, then $F' = 0$ a.e. but $F(1) - F(0) = 1$.

=== Absolutely Continuous Functions

#definition[
    A function $F: [a, b] -> RR$ is absolutely continuous if for every $epsilon > 0$, exists $delta > 0$ such that
    $ 
    sum_(j=1)^N (b_j - a_j) < delta => sum_(j=1)^N |F(b_j) - F(a_j)| < epsilon
    $
    for every finite collection of disjoint intervals ${(a_j, b_j)}_(j=1)^N$ in $[a, b]$.
]

Clearly, absolute continuity implies uniform continuity and bounded variation. 

#proposition[
    If $F(x) = integral_a^x f(t)  d t$ for some $f in L^1([a, b])$, then $F$ is absolutely continuous.
]
#proof[
    Follows from the absolute continuity of the integral.
    $qed$
]

Absolute continuity is a necessary condition for the fundamental theorem of calculus to hold. In fact, it is also sufficient.

#definition[
    A collection $cal(B)$ is said to be a Vitali covering of a set $E$ if for every $x in E$ and $eta > 0$, there exists some $B in cal(B)$ such that $x in B$ and $m(B) < eta$.
]

#lemma(name: "Actual Vitali Covering Lemma")[
    Suppose that $E$ is a set of finite measure and $cal(B)$ is a Vitali covering of $E$, then for any $delta > 0$, exists a finite collection of disjoint sets $B_1, ..., B_N$ in $cal(B)$ such that
    $ 
    m(E) <= sum_(i=1)^N m(B_i) + delta.
    $
]
#proof[
    Assume that $m(E) > delta$. Take a compact $E' subset.eq E$ such that $m(E') >= delta$. We can cover $E'$ by finitely many balls from $cal(B)$. From the baby Vitali covering lemma, we can find a disjoint subcollection of these balls ${B_1, ..., B_N}$ such that
    $ 
    delta <= m(E') <= 3^d sum_(i=1)^N m(B_i). 
    $
    If $m(E) <= sum_(i=1)^N m(B_i) + delta$, we are done. Otherwise, consider $E_2 = E backslash union.big_(i=1)^N overline(B_i)$, then $m(E_2) > delta$. Also, the balls in $cal(B)$ that that are disjoint from $union.big_(i=1)^N overline(B_i)$ form a Vitali covering of $E_2$, so we can repeat the argument to find a finite collection of disjoint balls ${B_(N + 1), ..., B_(N_2)}$ such that
    $ 
    delta <= m(E_2) <= 3^d sum_(i=N + 1)^(N_2) m(B_i), 
    $
    then $sum_(i=1)^(N_2) m(B_i) >= 2 dot.op 3^(-d) delta$. If this process continues indefinitely, the sum of the measures of the disjoint balls we have found will exceed $m(E) < oo$, which is a contradiction. Hence the process must terminate after finitely many steps, so we can find a finite collection of disjoint balls ${B_1, ..., B_N}$ such that $m(E) <= sum_(i=1)^N m(B_i) + delta$.
    $qed$
]

#theorem[
    If $F$ is absolutely continuous on $[a, b]$, then $F'$ exists a.e. Moreover, if $F' = 0$ a.e., then $F$ is constant.
]
#proof[
    Since $F$ is absolutely continuous, it is of bounded variation, so $F'$ exists a.e. For the second part, it suffices to show that $F(b) - F(a) = 0$ since the same argument can be applied to any subinterval of $[a, b]$. Let
    $ 
    E = {x in (a, b) : F'(x) = 0}.
    $
    By assumption, $m(E) = b - a$. For $x in E$, we have
    $ 
    lim_(h -> 0) abs((F(x + h) - F(x))/(h)) = 0. 
    $
    For each $eta > 0$, exists an open interval (depending on $eta, x, epsilon$) $I = (a_x, b_x) subset.eq [a, b]$ containing $x$ such that
    $ 
    |F(b_x) - F(a_x)| <= epsilon (b_x - a_x).
    $
    The collection of all such intervals forms a Vitali covering of $E$, so by the Vitali covering lemma, for all $delta > 0$, exists a finite collection of disjoint intervals ${I_1, ..., I_N}$ where $I_i = (a_i, b_i)$ such that
    $ 
    m(E) <= sum_(i=1)^N (b_i - a_i) + delta.
    $
    By the inequality above, the complement $[a, b] backslash union.big_(i=1)^N I_i$ can be written as a union of finitely many closed intervals $union.big_(j=1)^M [alpha_j, beta_j]$ such that the total length does not exceed $delta$. By absolute continuity of $F$, we can choose $delta$ small enough such that
    $ 
    sum_(j=1)^M |F(beta_j) - F(alpha_j)| <= epsilon.
    $
    Also, we have
    $ 
    sum_(i=1)^N |F(b_i) - F(a_i)| <= epsilon sum_(i=1)^N (b_i - a_i) <= epsilon (b - a).
    $
    Therefore,
    $ 
    F(b) - F(a) &= sum_(i=1)^N (F(b_i) - F(a_i)) + sum_(j=1)^M (F(beta_j) - F(alpha_j)) \
    &<= epsilon (b - a) + epsilon = (b - a + 1) epsilon.
    $
    Taking $epsilon -> 0$ gives $F(b) - F(a) = 0$, so $F$ is constant.
    $qed$
]

#claim[
    Suppose that $F$ is absolutely continuous on $[a, b]$, then $F'$ exists a.e. and is integrable. Moreover, we have
    $ 
    F(x) = F(a) + integral_a^x F'(t)  d t
    $
    for every $x in [a, b]$. Conversely, if $f in L^1([a, b])$, then $F(x) = integral_a^x f(t)  d t$ is absolutely continuous on $[a, b]$ and $F' = f$ a.e.
]
#proof[
    From @cl:bound_integral_derivative, we have
    $ 
    integral_a^x F'(t)  d t <= F(x) - F(a) < oo,
    $
    so $F'$ is integrable. Set $G(x) = integral_a^x F'(t)  d t$, then $G$ is absolutely continuous and so is the difference $G - F$. By Lebesgue differentiation theorem, we have $G' = F'$ a.e., so $(G - F)' = 0$ a.e. By the previous theorem, $G - F$ is constant, thus
    $ 
    F(x) = F(a) + integral_a^x F'(t)  d t
    $
    for every $x in [a, b]$. The converse direction follows from the first part and the absolute continuity of the integral.
    $qed$
]

=== Jump functions

We know that a bounded increasing function $F$ on $[a, b]$ has countably many discontinuities: since $F$ must be bounded, say $|F| <= 2M$, then there are at most $2M/epsilon$ points where $F$ has a jump of size at least $epsilon$, hence the total number of discontinuities must be countable. Let $(x_n)$ be the sequence of discontinuities of $F$. Define
$ 
f(x_n^+) = lim_(x -> x_n^+) F(x),  quad  f(x_n^-) = lim_(x -> x_n^-) F(x),  quad  alpha_n = f(x_n^+) - f(x_n^-).
$
Since $F$ is increasing, exists $theta_n in [0, 1]$ such that
$ 
F(x_n) = F(x_n^-) + theta_n alpha_n.
$
Define
$ 
j_n(x) = cases(
    0 & quad x < x_n, 
    theta_n & quad x = x_n, 
    1 & quad x > x_n,
)
$
and define the jump function of $F$ by
$ 
J_F(x) = sum_(n=1)^oo alpha_n j_n(x). 
$
Note that $sum_(n=1)^oo alpha_n <= F(b) - F(a) < oo$, so the series defining $J_F$ converges absolutely and uniformly on $[a, b]$. 

#lemma[
    Suppose that $F$ is increasing and bounded on $[a, b]$, then $J_F$ is discontinuous precisely at $(x_n)$. Moreover, the difference $F - J_F$ is continuous and increasing on $[a, b]$.
]
#proof[
    If $x eq.not x_n$ for every $n$, then $j_n$ is continuous at $x$ for every $n$, and since the series converges uniformly, $J_F$ is continuous at $x$. If $x = x_N$ for some $N$, then we write
    $ 
    J(x) = sum_(n=1)^N alpha_n j_n(x) + sum_(n=N + 1)^oo alpha_n j_n(x).
    $
    By the same argument as above, the second series is continuous at $x_N$, while the first series has a jump of $alpha_N$ at $x_N$, so $J_F$ has a jump of $alpha_N$ at $x_N$. By definition of $J_F$, $F - J_F$ is continuous. For $x < y$, we have
    $ 
    J(y) - J(x) <= sum_(x < x_n <= y) alpha_n <= F(y) - F(x),
    $
    so $F - J_F$ is increasing.
    $qed$
]

#theorem[
    If $J$ is the jump function considered above, then $J'$ exists a.e. and $J' = 0$ a.e.
]
#proof[
    Given any $epsilon > 0$, let $E$ be the set of those $x$ where
    $ 
    limsup_(h -> 0) abs((J(x + h) - J(x))/(h)) > epsilon
    $
    is measurable. Suppose $delta = m(E)$. We want to show that $delta = 0$. Since the series $sum alpha_n$ converges, for any $eta > 0$, exists $N$ such that $sum_(n>N) alpha_n < eta$. Write
    $ 
    J_0(x) = sum_(n>N) alpha_n j_n(x), 
    $
    then we have $J_0(b) - J_0(a) < eta$. Let $E_0$ be the set of those $x$ where
    $ 
    limsup_(h -> 0) abs((J_0(x + h) - J_0(x))/(h)) > epsilon,
    $
    then $E_0 subset.eq E$ and $E_0$ differs from $E$ by at most a finite set, namely ${x_1, ..., x_N}$, so $m(E_0) = m(E) = delta$. By inner regularity, there exists a compact set $K subset.eq E_0$ such that $m(K) > delta/2$. For each $x in K$, there exists an interval $(a_x, b_x) in.rev x$ such that
    $ 
    J_0(b_x) - J_0(a_x) > epsilon (b_x - a_x).
    $
    By compactness, exists a finite collection of disjoint intervals that covers $K$, and by Vitali covering lemma, we can find a finite collection of disjoint intervals ${(a_(i_k), b_(i_k))}_(k=1)^N$ such that
    $ 
    sum_(k=1)^N (b_(i_k) - a_(i_k)) > 1/3 m(K). 
    $
    Therefore,
    $ 
    J_0(b) - J_0(a) >= sum_(k=1)^N (J_0(b_(i_k)) - J_0(a_(i_k))) > epsilon sum_(k=1)^N (b_(i_k) - a_(i_k)) > epsilon/3 m(K) > epsilon/6 delta.
    $
    Since $eta$ is arbitrary, we can choose $eta < epsilon/6 delta$, which is a contradiction. Hence $delta = 0$, so $J' = 0$ a.e.
    $qed$
]

== Rectifiable curves

#definition[
    Let $gamma$ be a parametrized curve in the plane given by $z(t) = (x(t), y(t))$ for $t in [a, b]$, where $x, y$ are continuous real-valued functions. $gamma$ is rectifiable if there exists $M < oo$ such that for all partitions $a = t_0 < t_1 < dots.c < t_N = b$ of $[a, b]$, we have
    $ 
    sum_(j=1)^N |z(t_j) - z(t_(j - 1))| <= M.
    $ 
    The length of $gamma$ is defined by
    $ 
    L(gamma) = sup sum_(j=1)^N |z(t_j) - z(t_(j - 1))|,
    $
    where the supremum is taken over all partitions of $[a, b]$.
]

#proposition[
    $gamma$ is rectifiable if and only if $x$ and $y$ are of bounded variation. 
]
#proof[
    Write $z(t) = x(t) + i y(t)$, then
    $ 
    z(t_i) - z(t_(i - 1)) = (x(t_i) - x(t_(i - 1))) + i (y(t_i) - y(t_(i - 1))).
    $
    The conclusion follows from
    $ 
    |a + b i| <= |a| + |b| <= 2 |a + b i|
    $
    for every $a, b in RR$. 
    $qed$
]

We'd like to know when the length of a rectifiable curve can be computed by integration, i.e. when we have
$ 
L(gamma) = integral_a^b sqrt(|x'(t)|^2 + |y'(t)|^2)  d t.
$
However, this is not always the case. For example, if $x(t) = y(t) = F(t)$ where $F$ is the Cantor function, then $gamma$ traces out the line segment from $(0, 0)$ to $(1, 1)$, so $L(gamma) = sqrt(2)$, but $z'(t) = 0$ a.e., so $integral_0^1 |z'(t)|  d t = 0$.

#proposition[
    If $F: [a, b] -> CC$ is absolutely continuous, then
    $ 
    T_F(a, b) = integral_a^b |F'(t)|  d t, 
    $
    where $T_F(a, b)$ is the total variation of $F$ on $[a, b]$.
]
#proof[
    By absolute continuity, for any partition $a = t_0 < t_1 < dots.c < t_N = b$ of $[a, b]$, we have
    $ 
    sum_(j=1)^N |F(t_j) - F(t_(j - 1))| &= sum_(j=1)^N abs(integral_(t_(j - 1))^(t_j) F'(t)  d t ) \
    &<= sum_(j=1)^N integral_(t_(j - 1))^(t_j) |F'(t)|  d t = integral_a^b |F'(t)|  d t, 
    $
    so $T_F(a, b) <= integral_a^b |F'(t)|  d t$. On the other hand, by absolute continuity, $F'$ is integrable, so there exists a step function $g$ on $[a, b]$ such that $|F' - g|_1 < epsilon/2$. Let $h = F' - g$, then $|h|_1 = integral_a^b |h(t)|  d t < epsilon/2$. Set $G(x) = integral_a^x g(t)  d t$ and $H(x) = integral_a^x h(t)  d t$, then
    $ 
    F(x) - F(a) = G(x) + H(x) => T_F(a, b) >= T_G(a, b) - T_H(a, b). 
    $
    By the first part, we have $T_H(a, b) <= integral_a^b |h(t)|  d t < epsilon/2$, hence
    $ 
    T_F(a, b) >= T_G(a, b) - epsilon/2. 
    $
    Partition the interval $[a, b]$ so that $g$ is constant on each subinterval, then we have
    $ 
    T_G(a, b) &>= sum_(j=1)^N |G(t_j) - G(t_(j - 1))| = sum_(j=1)^N abs(integral_(t_(j - 1))^(t_j) g(t)  d t) \
    &= sum_(j=1)^N integral_(t_(j - 1))^(t_j) |g(t)|  d t = integral_a^b |g(t)|  d t. 
    $
    Since $|F' - g|_1 < epsilon/2$, we have $integral_a^b |g(t)|  d t > integral_a^b |F'(t)|  d t - epsilon/2$, so
    $ 
    T_F(a, b) >= integral_a^b |F'(t)|  d t - epsilon.
    $
    Since $epsilon$ is arbitrary, we have $T_F(a, b) >= integral_a^b |F'(t)|  d t$, hence $T_F(a, b) = integral_a^b |F'(t)|  d t$.
    $qed$
]

#theorem[
    If $x, y$ are absolutely continuous on $[a, b]$, then $gamma$ is rectifiable and
    $ 
    L(gamma) = integral_a^b sqrt(|x'(t)|^2 + |y'(t)|^2)  d t.
    $
]
#proof[
    Since $x$ and $y$ are absolutely continuous, they are of bounded variation, so $gamma$ is rectifiable. The length formula follows from the previous proposition. 
    $qed$
]

A rectifiable curve has a natural parametrization, called the arc-length parametrization. Suppose that $gamma$ is parametrized by $t |-> z(t)$. Write $s(t)$ for the length of the segment of $gamma$ that arises as the image of $z([a, t])$. Then $s$ is continuous, nondecreasing and it maps $[a, b]$ to $[0, L(gamma)]$. The arc-length parametrization of $gamma$ is given by $tilde(z)(s)$, where $tilde(z)(s) = z(t)$ for $s = s(t)$. If $s(t_1) = s(t_2)$ for some $t_1 < t_2$, then $z(t)$ does not vary on $[t_1, t_2]$, so $z(t_1) = z(t_2)$. Therefore, $tilde(z)$ is well-defined. Moreover, $|tilde(z)(s_1) - tilde(z)(s_2)| <= |s_1 - s_2|$ for every $s_1, s_2$, so $tilde(z)$ is Lipschitz continuous with constant 1, hence $|tilde(z)'(s)| <= 1$. By definition of total variation, 
$ 
L(gamma) = T_(tilde(z))(0, L(gamma)) = integral_0^(L(gamma)) |tilde(z)'(s)|  d s, 
$
so $|tilde(z)'(s)| = 1$ for a.e. $s$. In particular, writing $tilde(z)(s) = (tilde(x)(s), tilde(y)(s))$, we have
$ 
L = integral_0^L sqrt(|tilde(x)'(s)|^2 + |tilde(y)'(s)|^2)  d s. 
$

=== Isoperimetric Inequality

#definition[
    A curve parametrized by $z(t) |-> (x(t), y(t))$ is simple if $t |-> z(t)$ is injective. A curve is simple and closed if $t |-> z(t)$ is injective on $[a, b)$ and $z(a) = z(b)$. A curve is quasi-simple if $t |-> z(t)$ is injective for $t$ in the complement of finitely many points in $[a, b]$.
]

For a compact set $K subset RR^2$ and $delta > 0$, define
$ 
K^delta = {x in RR^2 : d(x, K) < delta}.
$
We say that $K$ has (one-dimensional) Minkowski content if the limit
$ 
cal(M)(K) = lim_(delta -> 0) (m(K^delta))/(2 delta)
$
exists and is finite. 

#lemma[
    If $gamma = {z(t) : t in [a, b]}$ is a curve, and if $D := |z(b) - z(a)|$ is the distance between the endpoints of $gamma$, then $m(gamma^delta) >= 2 delta D$. 
    
]
#proof[
    By translation and rotation, we may assume that $z(a) = (A, 0)$ and $z(b) = (B, 0)$ for some $A < B$, then $D = B - A$. By continuity of $t |-> x(t)$, for all $x in [A, B]$, there exists $overline(t)$ such that $x(overline(t)) = x$. Define $overline(Q) = (x(overline(t)), y(overline(t)))$, then $overline(Q) in gamma$ and $gamma^delta$ contains a segment of the vertical line of length $2 delta$ centered at $overline(Q)$. In other words, $m_1((gamma^delta)_x) >= 2 delta$ for every $x in [A, B]$. By Fubini's theorem, we have
    $ 
    m(gamma^delta) = integral_RR m_1((gamma^delta)_x)  d x >= integral_A^B 2 delta  d x = 2 delta D.
    $
    $qed$
]

Consider
$ 
overline(cal(M))(K) = limsup_(delta -> 0) (m(K^delta))/(2 delta),  quad  underline(cal(M))(K) = liminf_(delta -> 0) (m(K^delta))/(2 delta).
$

#proposition[
    Suppose that $gamma = {z(t) : t in [a, b]}$ is quasi-simple. If $underline(cal(M))(gamma) < oo$, then $gamma$ is rectifiable and $L(gamma) <= underline(cal(M))(gamma)$.
]
#proof[
    Let $P$ be any partition $a = t_0 < t_1 < dots.c < t_N = b$ of $[a, b]$. Define
    $ 
    L_P = sum_(j=1)^N |z(t_j) - z(t_(j - 1))|, 
    $
    then $L_P$ is the length of the polygonal curve obtained by connecting $z(t_0), z(t_1), ..., z(t_N)$ in order. Let $epsilon > 0$. By continuity of $z$, there exists subintervals $I_j := [a_j, b_j] subset (t_(j - 1), t_j)$ such that
    $ 
    sum_(j=1)^N |z(b_j) - z(a_j)| >= L_P - epsilon.
    $
    Since $gamma$ is quasi-simple, we can choose these subintervals so that their image under $z$ are disjoint. Write $gamma_j = {z(t) : t in I_j}$. Also, 
    $ 
    gamma supset.eq union.big_(j=1)^N gamma_j arrow.r.squiggly gamma^delta supset.eq union.big_(j=1)^N gamma_j^delta.
    $
    If $delta$ is sufficiently small, then $gamma_j^delta$ are disjoint for distinct $j$, so
    $ 
    m(gamma^delta) >= m( union.big_(j=1)^N gamma_j^delta ) = sum_(j=1)^N m(gamma_j^delta) >= 2 delta sum_(j=1)^N |z(b_j) - z(a_j)| >= 2 delta (L_P - epsilon).
    $
    Since $epsilon$ is arbitrary, we have $m(gamma^delta) >= 2 delta L_P$ for every partition $P$. Taking supremum over all partitions gives $m(gamma^delta) >= 2 delta L(gamma)$, so $underline(cal(M))(gamma) >= L(gamma)$. 
    $qed$
]

#proposition[
    Suppose that $gamma = {z(t) : t in [a, b]}$ is rectifiable, then $overline(cal(M))(gamma) <= L(gamma)$.
]
#proof[
    Since both quantites are independent of the parametrization, we may assume that $gamma$ is parametrized by arc-length. Write the arc-length parametrization of $gamma$ as $z(s) = (x(s), y(s))$ for $s in [0, L]$, then $z$ is absolutely continuous and $|z'(s)| = 1$ for a.e. $s$. For each $n in NN$, define
    $ 
    F_n(s) = sup_(0 < |h| < 1/n) abs((z(s + h) - z(s))/(h) - z'(s)).
    $
    where we set $z(s) = z(0)$ for $s < 0$ and $z(s) = z(L)$ for $s > L$. Since $z$ is continuous, the supremum can be replaced by supremum over countably many $h$, so $F_n$ is measurable. Moreover, $F_n(s) -> 0$ as $n -> oo$ for a.e. $s$. Fix $epsilon in (0, 1)$. By the Egorov theorem, there exists a measurable set $E_epsilon subset.eq [0, L]$ with $m(E_epsilon) < epsilon$ such that the convergence $F_n(s) -> 0$ is uniform on $[0, L] backslash E_epsilon$. Choose $r_epsilon = 1/n$ for sufficiently large $n$ such that
    $ 
    sup_(0 < |h| < r_epsilon) abs((z(s + h) - z(s))/(h) - z'(s)) < epsilon
    $
    for every $s in [0, L] backslash E_epsilon$. By enlarging $E_epsilon$ if necessary, we can assume that $|z'(s)| = 1$ for every $s in [0, L] backslash E_epsilon$. Fix $rho in (0, r_epsilon)$. Partition $[0, L]$ into subintervals of length $rho$, then there are $N <= L/rho + 1$ subintervals, say $I_1, ..., I_N$. We say that $I_j$ is good if $I_j subset.eq.not E_epsilon$ and bad if $I_j subset.eq E_epsilon$. The total length of bad intervals is at most $m(E_epsilon) < epsilon$. Define $gamma_j = {z(s) : s in I_j}$, then $m(gamma^delta) <= sum_(j=1)^N m(gamma_j^delta)$. 

    First consider that $I_j$ is good, then there exists $s_0 in I_j backslash E_epsilon$ such that
    $ 
    sup_(0 < |h| < r_epsilon) abs((z(s_0 + h) - z(s_0))/(h) - z'(s_0)) < epsilon,  quad  |z'(s_0)| = 1.
    $
    By translation and rotation, we may assume that $z(s_0) = (0, 0)$ and $z'(s_0) = (1, 0)$. Note that as $h$ varies over $[a_j - s_0, b_j - s_0]$, $h + s_0$ varies over $I_j$. Note that $|h| < r_epsilon$ for every $h in [a_j - s_0, b_j - s_0]$, so $gamma_j$ is contained in the rectangle
    $ 
    [a_j - s_0 - epsilon rho, b_j - s_0 + epsilon rho] times [-epsilon rho, epsilon rho].
        $
    Therefore, $gamma_j^delta$ is contained in the rectangle
    $ 
    [a_j - s_0 - epsilon rho - delta, b_j - s_0 + epsilon rho + delta] times [-epsilon rho - delta, epsilon rho + delta],
    $
    so
    $ 
    m(gamma_j^delta) <= (rho + 2 epsilon rho + 2 delta) (2 epsilon rho + 2 delta) = 2 delta rho + O(epsilon rho^2 + epsilon rho delta + delta^2).
    $
    For bad intervals, $|z(s) - z(s')| <= |s - s'|$ for every $s, s' in I_j$, so $gamma_j$ is contained in a ball of radius $rho$, hence $gamma_j^delta$ is contained in a ball of radius $rho + delta$, so $m(gamma_j^delta) <= pi (rho + delta)^2 = O(rho^2 + rho delta + delta^2)$. Since there are at most $L/rho + 1$ intervals, so at most $epsilon/rho + 1$ bad intervals, we have
    $ 
    m(gamma^delta) &<= sum_(j=1)^N m(gamma_j^delta) \
    &<= ( L/rho + 1 ) (2 delta rho + O(epsilon rho^2 + epsilon rho delta + delta^2)) + ( epsilon/rho + 1 ) O(rho^2 + rho delta + delta^2) \
    &= 2 delta L + 2 delta rho + O(epsilon delta + delta^2/rho + epsilon rho) + O((epsilon/rho + 1)(rho^2 + delta^2)).
    $
    take $rho = delta/sqrt(epsilon)$, then
    $ 
    (m(gamma^delta))/(2 delta) <= L + O(delta/sqrt(epsilon) + epsilon + sqrt(epsilon) + delta/epsilon).
    $
    Letting $delta -> 0$ gives $overline(cal(M))(gamma) <= L$.
    $qed$
]

#theorem[
    Suppose that $Omega$ is a bounded open subset and its boundary $overline(Omega) backslash Omega$ is a rectifiable curve $gamma$, then
    $ 
    L(gamma)^2 >= 4 pi m(Omega).
    $
]
#proof[
    For each $delta > 0$, consider
    $ 
    Omega_+(delta) = {x in RR^2 : d(x, overline(Omega)) < delta},  quad  Omega_-(delta) = {x in RR^2 : d(x, RR^2 backslash Omega) >= delta}.
    $
    Thus $Omega_-(delta) subset.eq Omega subset.eq Omega_+(delta)$. Note that
    $ 
    Omega_+(delta) = Omega_-(delta) union gamma^delta
    $
    and the union is disjoint. We have
    $ 
    Omega + B(0, delta) subset.eq Omega_+(delta),  quad  Omega_-(delta) + B(0, delta) subset.eq Omega.
    $
    By the Brunn-Minkowski inequality, we have
    $ 
    m(Omega_+(delta)) >= (m(Omega)^(1/2) + m(B(0, delta))^(1/2))^2 = (m(Omega)^(1/2) + sqrt(pi) delta)^2 >= m(Omega) + 2 sqrt(pi) delta sqrt(m(Omega)).
    $
    Similarly, we have
    $ 
    m(Omega) >= m(Omega_-(delta)) + 2 sqrt(pi) delta sqrt(m(Omega_-(delta))).
    $
    Therefore, 
    $ 
    m(gamma^delta) = m(Omega_+(delta)) - m(Omega_-(delta)) >= 2 sqrt(pi) delta (sqrt(m(Omega)) + sqrt(m(Omega_-(delta)))), 
    $
    dividing both sides by $2 delta$ and taking limsup as $delta -> 0$ gives
    $ 
    cal(M)(gamma) >= 2 sqrt(pi) sqrt(m(Omega)).
    $
    By the previous propositions, we have $L(gamma) >= cal(M)(gamma)$, so $L(gamma) >= 2 sqrt(pi) sqrt(m(Omega)) arrow.r.squiggly L(gamma)^2 >= 4 pi m(Omega)$. The equality holds if and only if $Omega$ is a disk, which can be seen from the equality case of the Brunn-Minkowski inequality.
    $qed$
]

= Hilbert Spaces

Let $X$ be a vector space. An inner product is a map $chevron.l dot.op, dot.op chevron.r : X times X -> CC$ such that

+ $chevron.l alpha_1 x_1 + alpha_2 x_2, y chevron.r = alpha_1 chevron.l x_1, y chevron.r + alpha_2 chevron.l x_2, y chevron.r$ for every $x_1, x_2, y in X$ and $alpha_1, alpha_2 in CC$;
+ $chevron.l y, x chevron.r = overline(chevron.l x\, y chevron.r)$ for every $x, y in X$;
+ $chevron.l x, x chevron.r >= 0$ for every $x in X$, and $chevron.l x, x chevron.r = 0$ if and only if $x = 0$.

In general, the inner product is a continuos map from $X times X$ to $CC$. Two vectors $x, y$ are orthogonal if $chevron.l x, y chevron.r = 0$. The norm of a vector $x$ is defined by $|x| = sqrt(chevron.l x x chevron.r)$. A complete inner product space is called a Hilbert space. 

#example[
    $ell^2$ is the space of square-summable sequences, i.e. 
    $ 
    ell^2 = {(x_n)_(n=1)^oo : sum_(n=1)^oo |x_n|^2 < oo},
    $
    and the inner product is defined by
    $ 
    chevron.l (x_n), (y_n) chevron.r = sum_(n=1)^oo x_n overline(y_n).
    $
]

#example[
    Recall that $L^2(RR^d)$ is the space of square-integrable functions on $RR^d$, and it is a Hilbert space with inner product defined by
    $ 
    chevron.l f, g chevron.r = integral_(RR^d) f(x) overline(g(x))  d x.
    $
]

If $|dot.op|$ is the norm induced by the inner product $chevron.l dot.op, dot.op chevron.r$ and $|dot.op|'$ is the completion of $|dot.op|$, then there exists an inner product $chevron.l dot.op, dot.op chevron.r'$ extending $chevron.l dot.op, dot.op chevron.r$ such that $|dot.op|'$ is the norm induced by $chevron.l dot.op, dot.op chevron.r'$. 

#proposition(name: "Parallelogram Law")[
    Let $|dot.op|$ be a norm on $X$ induced by an inner product $chevron.l dot.op, dot.op chevron.r$, then for any $x, y in X$, we have
    $ 
    |x + y|^2 + |x - y|^2 = 2 |x|^2 + 2 |y|^2.
    $
]
#proof[
    By definition of the norm, we have
    $ 
    |x + y|^2 = chevron.l x + y, x + y chevron.r = chevron.l x, x chevron.r + chevron.l y, y chevron.r + 2 "Re" chevron.l x, y chevron.r,
    $
    and
    $ 
    |x - y|^2 = chevron.l x - y, x - y chevron.r = chevron.l x, x chevron.r + chevron.l y, y chevron.r - 2 "Re" chevron.l x, y chevron.r.
    $
    Adding these two equations gives the desired result.
    $qed$
]

#example[
    Consider $ell^p$ spaces for $p in [1, oo)$ with norm defined by
    $ 
    |(x_n)|_p = ( sum_(n=1)^oo |x_n|^p )^(1/p).
    $
    Suppose that $ell^p$ is a Hilbert space. Take $x = (1, 1, 0, ...)$ and $y = (1, -1, 0, ...)$, then
    $ 
    |x + y|_p^2 + |x - y|_p^2 = 2 dot.op 2^2 = 8,
    $
    while
    $ 
    2 |x|_p^2 + 2 |y|_p^2 = 2 dot.op 2^(2/p) + 2 dot.op 2^(2/p) = 4 dot.op 2^(2/p),
    $
    so we must have $p = 2$. Therefore, $ell^p$ is a Hilbert space if and only if $p = 2$.
]

#proposition(name: "Polarization Identity")[
    Let $|dot.op|$ be a norm on $X$ induced by an inner product $chevron.l dot.op, dot.op chevron.r$, then for any $x, y in X$, we have
    $ 
    "Re" chevron.l x, y chevron.r = 1/4 (|x + y|^2 - |x - y|^2),  quad  "Im" chevron.l x, y chevron.r = 1/4 (|x + i y|^2 - |x - i y|^2).
    $
]

#theorem[
    Let $K$ be a closed, convex, proper subset of a Hilbert space $X$, and let $x_0 in X backslash K$. Then there exists a unique $x^* in K$ such that
    $ 
    |x_0 - x^*| = inf_(x in K) |x_0 - x|.
    $
]
#proof[
    Let $d = inf_(x in K) |x_0 - x|$. Let $(x_n)$ be a sequence in $K$ such that $|x_0 - x_n| -> inf_(x in K) |x_0 - x|$. We claim that $(x_n)$ is a Cauchy sequence. Note that
    $ 
    |x_n - x_m|^2 &= |(x_n - x_0) - (x_m - x_0)|^2 \
    &= 2 |x_n - x_0|^2 + 2 |x_m - x_0|^2 - |(x_n - x_0) + (x_m - x_0)|^2 \
    &= 2 |x_n - x_0|^2 + 2 |x_m - x_0|^2 - 4 abs(x_n + x_m/2 - x_0)^2.
    $
    Note that $x_n + x_m/2 in K$ by convexity of $K$, so $| x_n + x_m/2 - x_0 | >= d$, hence
    $ 
    |x_n - x_m|^2 <= 2 |x_n - x_0|^2 + 2 |x_m - x_0|^2 - 4 d^2 -> 0
    $
    as $n, m -> oo$, so $(x_n)$ is a Cauchy sequence. Since $X$ is complete, there exists $x^* in X$ such that $x_n -> x^*$. Since $K$ is closed, we have $x^* in K$. By continuity of the norm, we have $|x_0 - x^*| = lim_(n -> oo) |x_0 - x_n| = d$, so $x^*$ is a minimizer.

    If $x' in K$ is another minimizer, then
    $ 
    |x' - x^*|^2 &= 2 |x' - x_0|^2 + 2 |x^* - x_0|^2 - 4 abs(x' + (x^*)/2 - x_0)^2 \
    &<= -4d^2 + 2d^2 + 2d^2 = 0,
    $
    so $x' = x^*$, hence the minimizer is unique.
    $qed$
]

== Orthogonal Decomposition

#theorem[
    Let $Y$ be a closed proper subspace of a Hilbert space $X$, and let $x_0 in X backslash Y$. The point $y_0$ that minimizes the distance between $x_0$ and $Y$ satisfies
    $ 
    chevron.l x_0 - y_0, y chevron.r = 0
    $
    for every $y in Y$. Conversely, if $z in Y$ satisfies $chevron.l x_0 - z, y chevron.r = 0$ for every $y in Y$, then $z = y_0$. In this case, 
    $ 
    |x_0 - y_0|^2 + |y_0|^2 = |x_0|^2.
    $
]
#proof[
    The existence and uniqueness of $y_0$ follows from the previous theorem.

    For $y in Y$ and $h in RR$, define
    $ 
    phi(h) = |x_0 - y_0 + h y|^2, 
    $
    then $phi$ attains its minimum at $h = 0$. By differentiating $phi$ at $h = 0$, we have
    $ 
    0 = phi'(0) = 2 "Re" chevron.l x_0 - y_0, y chevron.r.
    $
    Replacing $y$ by $i y$ gives $"Im" chevron.l x_0 - y_0, y chevron.r = 0$, so $chevron.l x_0 - y_0, y chevron.r = 0$ for every $y in Y$. 

    Conversely, if $z in Y$ satisfies $chevron.l x_0 - z, y chevron.r = 0$ for every $y in Y$, then $chevron.l x_0 - z, z - y chevron.r = 0$ for every $y in Y$, so
    $ 
    |x_0 - y|^2 = |x_0 - z|^2 + |z - y|^2 >= |x_0 - z|^2
    $
    for every $y in Y$, hence $z$ minimizes the distance between $x_0$ and $Y$, so $z = y_0$. In this case, we have
    $ 
    |x_0|^2 = |x_0 - y_0|^2 + |y_0|^2
    $
    since $chevron.l x_0 - y_0, y_0 chevron.r = 0$.
    $qed$
]

#definition[
    Let $Y$ be a closed subspace of a Hilbert space $X$. The projection operator $cal(P)$ of $X$ onto $Y$ is defined by
    $ 
    cal(P)(x_0) = cases(
        y_0 & x_0 in X backslash Y, 
        x_0 & x_0 in Y,
    )
    $
    where $y_0$ is the unique point in $Y$ that minimizes the distance between $x_0$ and $Y$. 
]

It's easy to see that $cal(P)$ is linear and continuous, and $cal(P)^2 = cal(P)$. Moreover, the operator norm of $cal(P)$ equals
$ 
|cal(P)| = sup_(x eq.not 0) (|cal(P) x|)/(|x|) = 1.
$

=== Self-Duality

Hilbert spaces have self-duality. For each $z in X$, we can associate a bounded linear functional $Lambda_z$ defined by $Lambda_z(x) = chevron.l x, z chevron.r$. The map
$ 
Phi : X -> X^*,  quad  z |-> Lambda_z
$
is a sesquilinear map, i.e. $Phi(alpha z_1 + beta z_2) = overline(alpha) Phi(z_1) + overline(beta) Phi(z_2)$ for every $z_1, z_2 in X$ and $alpha, beta in CC$. 

#theorem(name: "Riesz Representation Theorem")[
    Let $X$ be a Hilbert space. If $Lambda$ is a bounded linear functional on $X$, then there exists a unique $z in X$ such that $Lambda = Lambda_z$. Moreover, $|Lambda_z| = |z|$. 
]
#proof[
    Let $Lambda$ be a bounded linear functional on $X$. Consider $Y = {x in X : Lambda(x) = 0}$, then $Y$ is a closed subspace of $X$. If $Y = X$, then $Lambda = 0$, so we can take $z = 0$. Otherwise, take any $x_0 in X backslash Y$, so
    $ 
    chevron.l x_0 - cal(P) x_0, y chevron.r = 0
    $
    for every $y in Y$. Set $z_0 = x_0 - cal(P) x_0$. Fix $x in X$. Let $u = (Lambda x)z_0 - (Lambda z_0)x$, then $u in Y$ since $Lambda u = 0$. Therefore, we have
    $ 
    0 = chevron.l u, z_0 chevron.r = chevron.l (Lambda x) z_0 - (Lambda z_0) x, z_0 chevron.r = (Lambda x) |z_0|^2 - (Lambda z_0) chevron.l x, z_0 chevron.r,
    $
    so
    $ 
    Lambda x = (Lambda z_0)/(|z_0|^2) chevron.l x, z_0 chevron.r.
    $
    Set $z = overline(Lambda z_0)/(|z_0|^2) z_0$, then $Lambda x = chevron.l x, z chevron.r$ for every $x in X$, so $Lambda = Lambda_z$. Moreover, 
    $ 
    |Lambda_z| = sup_(x eq.not 0) (|chevron.l x, z chevron.r|)/(|x|) <= |z|
    $
    by the Cauchy-Schwarz inequality, and $|chevron.l z, z chevron.r| = |z|^2$, so $|Lambda_z| = |z|$.
    $qed$
]

#remark[
    This shows that $Phi$ is an isometric sesquilinear isomorphism between $X$ and $X^*$. 
]

=== Direct Sum Decomposition

We want to write $X = X_1 xor X_2$ for some closed subspaces $X_1, X_2$ of $X$, so that the projections onto $X_1$ and $X_2$ are continuous. This gives rise to the following question: gives a closed subspace $X_1$ of a Banach space $X$, does there exist a closed subspace $X_2$ such that $X = X_1 xor X_2$. The answer is negative for general Banach spaces, but it is positive for Hilbert spaces, as we can set $X_2 = X_1^perp$. In fact, if a Banach space satisfies this property, then its norm must be equivalent to a norm induced by a complete inner product. 

#definition[
    Let $X$ be a Hilbert space, and let $X_1$ be a closed subspace of $X$. The orthogonal complement of $X_1$ is defined by
    $ 
    X_1^perp = {x in X : chevron.l x, x_1 chevron.r = 0 "for every" x_1 in X_1}.
    $
]

#proposition[
    $X_1^perp$ is a closed subspace of $X$, and $X = X_1 xor X_1^perp$.
]
#proof[
    It's easy to see that $X_1^perp$ is a closed subspace of $X$ since the inner product is continuous. For each $x in X$, we can write
    $ 
    x = cal(P) x + (x - cal(P) x),
    $
    where $cal(P)$ is the projection operator of $X$ onto $X_1$, so $cal(P) x in X_1$ and $x - cal(P) x in X_1^perp$, hence $X = X_1 + X_1^perp$. If $x_0 in X_1 inter X_1^perp$, then $chevron.l x_0, x_0 chevron.r = 0$, so $x_0 = 0$, hence $X_1 inter X_1^perp = {0}$, implying that $X = X_1 xor X_1^perp$.
    $qed$
]

The bounded operators $cal(P)$ and $I - cal(P)$ are the projections of $X$ onto $X_1$ and $X_1^perp$, respectively.

#theorem[
    For any closed subspace $X_1$ of a Hilbert space $X$, we have $X = X_1 xor X_1^perp$. Moreover, if $cal(P): X -> X_1$ is the projection operator, then $forall x in X$, $cal(P) x$ is the unique point in $X_1$ such that
    $ 
    |x - cal(P) x| = inf_(x_1 in X_1) |x - x_1|, 
    $
    and the projection $cal(Q): X -> X_1^perp$ is given by $cal(Q) x = x - cal(P) x$.
]

=== Complete Orthonormal Sets

Given an orthonormal spanning set, we can compute the projection $cal(P) x$ of $x$ onto the closed subspace spanned by the set efficiently. 

#lemma(name: "Bessel's Inequality")[
    Let $S = {x_alpha: alpha in I}$ be an orthonormal set in a Hilbert space $X$. Then for every $x in X$, $chevron.l x, x_alpha chevron.r = 0$ for all but countably many $alpha in I$. Write $B$ for the set of $alpha in I$ such that $chevron.l x, x_alpha chevron.r eq.not 0$, then for any sequence $(alpha_k)$ in $B$, we have
    $ 
    sum_k |chevron.l x, x_(alpha_k) chevron.r|^2 <= |x|^2.
    $
]
#proof[
    Assume that $S$ is finite. Let $S = {x_1, ..., x_n}$. Let $y = sum_(k=1)^n chevron.l x, x_k chevron.r x_k$, then $chevron.l x - y, x_k chevron.r = 0$ for every $k$, so
    $ 
    |x|^2 = |x - y|^2 + |y|^2 >= |y|^2 = sum_(k=1)^n |chevron.l x, x_k chevron.r|^2.
    $

    In general, let $x in X$ and $l in NN$. Consider
    $ 
    S_l = {x_alpha in S : |chevron.l x, x_alpha chevron.r| > 1/l}.
    $
    By the finite case, we have $sum_(x_alpha in S_l) |chevron.l x, x_alpha chevron.r|^2 <= |x|^2$, so $S_l$ is finite for every $l$. Therefore, 
    $ 
    S_x = {x_alpha in S : chevron.l x, x_alpha chevron.r eq.not 0} = union.big_(l=1)^oo S_l
    $
    is countable. The general case follows from the finite case by taking limit as $n -> oo$.
    $qed$
]

#theorem[
    Let $Y$ be a closed subspace of a Hilbert space $X$. Suppose that $S$ is an orthonormal subset of $Y$ such that $"span"(S)$, the set of finite linear combinations of elements in $S$, is dense in $Y$. Then for every $x in X$, its orthogonal projection on $Y$ is given by
    $ 
    cal(P) x = sum_k chevron.l x, x_k chevron.r x_k,
    $
    where $B = {x_k : k in NN}$ is the set of elements in $S$ that are not orthogonal to $x$. 
]
#proof[
    We first verify that the sum is convergent. Let $z_n = sum_(k=1)^n chevron.l x, x_k chevron.r x_k$. It suffices to show that $(z_n)$ is a Cauchy sequence. For $m < n$, we have
    $ 
    |z_m - z_n|^2 = |sum_(k=m+1)^n chevron.l x, x_k chevron.r x_k|^2 = sum_(k=m+1)^n |chevron.l x, x_k chevron.r|^2 -> 0
    $
    as $m, n -> oo$ by Bessel's inequality. Next we verify that $cal(P) x = sum_k chevron.l x, x_k chevron.r x_k$. If $y$ is a finite linear combination of elements in $S$, then $chevron.l x - z_n, y chevron.r = 0$ for sufficiently large $n$, so $chevron.l x - sum_k chevron.l x, x_k chevron.r x_k, y chevron.r = 0$. Since $"span"(S)$ is dense in $Y$, we can take $n -> oo$ and by continuity of the inner product, we have $chevron.l x - sum_k chevron.l x, x_k chevron.r x_k, y chevron.r = 0$ for every $y in Y$, so $cal(P) x = sum_k chevron.l x, x_k chevron.r x_k$.
    $qed$
]

#definition[
    A subset $B$ of a Hilbert space $X$ is called a complete orthonormal set if
    
    + $B$ is an orthonormal set, and
    + $"span"(B)$ is dense in $X$.
]

#theorem[
    Every nonzero Hilbert space has a complete orthonormal set.
]
#proof[
    Let $cal(O)$ be the collection of orthonormal sets in $X$, partially ordered by inclusion, which in nonempty since $X$ is nonzero. Let $cal(C)$ be a chain in $cal(O)$, then $union.big_(O in cal(C)) O$ is an upper bound of $cal(C)$, so by Zorn's lemma, there exists a maximal orthonormal set $B$. We claim that $B$ is a complete orthonormal set. If not, then there exists $z in X backslash overline("span"(B))$. Let $cal(P)$ be the projection operator of $X$ onto $overline("span"(B))$ and
    $ 
    z' = z - (cal(P) z)/(|z - cal(P) z|),
    $
    then $B union {z'}$ is an orthonormal set, contradicting the maximality of $B$. Therefore, $B$ is a complete orthonormal set. 
    $qed$
]

#theorem[
    Let $B$ be an orthonormal set in a Hilbert space $X$. The following are equivalent:

    + $B$ is a complete orthonormal set;
    + $x = sum_(x_alpha in B) chevron.l x, x_alpha chevron.r x_alpha$ for every $x in X$;
    + $|x|^2 = sum_(x_alpha in B) |chevron.l x, x_alpha chevron.r|^2$ for every $x in X$ (Parseval's identity);
    + if $chevron.l x, x_alpha chevron.r = 0$ for every $x_alpha in B$, then $x = 0$.
]
#proof[
    - (i) $=>$ (ii): Since $x in X = overline("span"(B))$, the orthogonal projection of $x$ onto $overline("span"(B))$ is $x$ itself, so $x = sum_(x_alpha in B) chevron.l x, x_alpha chevron.r x_alpha$.
    - (ii) $=>$ (iii): We have
    $ 
    |x|^2 = chevron.l x, x chevron.r = lr(chevron.l sum_(x_alpha in B) chevron.l x, x_alpha chevron.r x_alpha, x chevron.r) = sum_(x_alpha in B) |chevron.l x, x_alpha chevron.r|^2.
    $
    - (iii) $=>$ (iv): Straightforward.
    - (iv) $=>$ (i): If $B$ is not complete, then there exists $x in X backslash overline("span"(B))$. Let $cal(P)$ be the projection operator of $X$ onto $overline("span"(B))$, then $chevron.l x - cal(P) x, x_alpha chevron.r = 0$ for every $x_alpha in B$, but $x - cal(P) x eq.not 0$, contradicting (iv). Therefore, $B$ is a complete orthonormal set.
    $qed$
]

#proposition[
    A Hilbert space $X$ has a countable complete orthonormal set if and only if $X$ is separable.
]
#proof[
    "$=>$": Let $B$ be a countable orthonormal set. Then rational linear combinations of elements in $B$ form a countable dense subset of $X$, so $X$ is separable.
    "$<=$": Let $D = {x_1, x_2, ...}$ be a countable dense subset of $X$. For each $n$, we throw away $x_n$ if it is linearly dependent on $x_1, ..., x_(n-1)$, obtaining a linearly independent subset $D' = {y_1, y_2, ...}$ whose closure of span is still $X$. Applying the Gram-Schmidt process to $D'$ gives a countable complete orthonormal set.
    $qed$
]

#theorem[
    Let $X$ be an infinite dimensional separable Hilbert space. Then exists an inner-product preserving isomorphism $Phi: X -> ell^2$.
]
#proof[
    Let $(x_k)$ be a countable complete orthonormal set in $X$. Define
    $ 
    Phi : X -> ell^2,  quad  x |-> (chevron.l x, x_k chevron.r)_(k=1)^oo.
    $
    By the Parseval's identity, we have $|Phi x|_2^2 = sum_(k=1)^oo |chevron.l x, x_k chevron.r|^2 = |x|^2$, so $Phi$ is an isometry hence linear. 

    For $(b_k) in ell^2$, define
    $ 
    y_n = sum_(k=1)^n b_k x_k,  quad  y = lim_(n -> oo) y_n. 
    $
    The limit exists since $(y_n)$ is a Cauchy sequence by definition of $ell^2$. By completeness of $X$, we have $y in X$. Moreover, $Phi y = (b_k)_(k=1)^oo$, so $Phi$ is surjective. $Phi$ is injective since $Phi x = 0$ implies $|x|^2 = sum_(k=1)^oo |chevron.l x, x_k chevron.r|^2 = 0$, so $x = 0$. By Polarization Identity, $Phi$ preserves the inner product. Therefore, $Phi$ is an inner-product preserving isomorphism between $X$ and $ell^2$.
    $qed$
]

= Fourier Analysis

== Fourier Series

For $f in L^1([-pi, pi])$, we can define its $n$-the Fourier coefficient $n in ZZ$ by
$ 
hat(f)(n) = 1/(2pi) integral_(-pi)^pi f(x) e^(-i n x)  d x.
$
$hat(f)(n)$ is well-defined since the absolute value of the integrand is $|f(x)|$, which is integrable. Write
$ 
f(x) tilde sum_(n=-oo)^oo hat(f)(n) e^(i n x)
$
for the Fourier series of $f$. In general, we don't expect the Fourier series of $f$ to converge to $f$ pointwise. By Riemann-Lebesgue lemma, we have $hat(f)(n) -> 0$ as $|n| -> oo$. We want to know whether there is a certain rate at which $hat(f)(n)$ goes to zero, and conversely, given a sequence $(a_n)$ that goes to zero, can we find a function $f$ such that $hat(f)(n) = a_n$ for every $n$?

Recall the Fejér kernel $F_N$ defined by
$ 
F_N (x) = 1/N ( (sin (N x / 2))/(sin (x / 2)) )^2. 
$
We have $|F_N|_(L^1([-pi, pi])) = 2pi$, and
$ 
hat(F)_N (n) = cases(
    1 - (|n|)/N & |n| < N, 
    0 & |n| >= N,
)
$

If $g$ is continuous and $2pi$-periodic, and define convolution
$ 
(g * F_N)(x) = 1/(2pi) integral_(-pi)^pi g(y) F_N(x - y)  d y = sum_(n=-(N-1))^(N-1) (1 - (|n|)/N) hat(g)(n) e^(i n x).
$
then $g * F_N arrows.rr g$ uniformly as $N -> oo$. 

#proposition[
    Let $(a_n)$ be a sequence of nonnegative numbers such that $lim_(|n| -> oo) a_n = 0$. Suppose that $a_(-n) = a_n$ and $a_(n-1) + a_(n+1) >= 2 a_n$ for every $n >= 1$, then there exists a nonnegative function $f in L^1([-pi, pi])$ such that $hat(f)(n) = a_n$ for every $n$.
]
#proof[
    Note that $(a_n - a_(n+1))$ is a decreasing sequence. Also, 
    $ 
    sum_(n=0)^N (a_n - a_(n+1)) = a_0 - a_(N+1) -> a_0
    $
    as $N -> oo$, so
    $ 
    lim_(n -> oo) n (a_n - a_(n+1)) = 0.
    $
    We have
    $ 
    sum_(n=1)^N n (a_(n-1) + a_(n+1) - 2 a_n) = a_0 - a_N - N (a_N - a_(N+1)) -> a_0
    $
    as $N -> oo$. Define
    $ 
    f(x) = sum_(n=1)^oo n (a_(n-1) + a_(n+1) - 2 a_n) F_n(x).
    $
    Since $|F_n|_(L^1([-pi, pi])) = 2pi$, the series converges in $L^1([-pi, pi])$. Also, $f$ is nonnegative since $F_n$ is nonnegative and $a_(n-1) + a_(n+1) >= 2 a_n$. By dominated convergence theorem, we have
    $ 
    hat(f)(m) &= sum_(n=1)^oo n (a_(n-1) + a_(n+1) - 2 a_n) hat(F)_n(m) \
    &= sum_(n=|m|+1)^oo n (a_(n-1) + a_(n+1) - 2 a_n) (1 - (|m|)/n) \
    &= sum_(n=|m|+1)^oo (a_(n-1) + a_(n+1) - 2 a_n) (n - |m|) \
    &= sum_(n=|m|+1)^oo (a_(n-1) + a_(n+1) - 2 a_n) n - |m| sum_(n=|m|+1)^oo (a_(n-1) + a_(n+1) - 2 a_n) \
    &= a_(|m|) - lim_(n -> oo) a_n - |m| dot.op 0 = a_(|m|) = a_m.
    $
    $qed$
]

#remark[
    The condition $a_(n-1) + a_(n+1) >= 2 a_n$ roughly says that $a_n$ is convex in $n$. If we can construct convex functions of arbitrarily slow decay, then we can construct functions whose Fourier coefficients decay arbitrarily slowly. 
]

#proposition[
    Let $f in L^1([-pi, pi])$ and assume that $hat(f)(|n|) = -hat(f)(-|n|)$ for every $n in ZZ$. Then
    $ 
    sum_(n eq.not 0) (|hat(f)(n)|)/(|n|) < oo.
    $
]
#proof[
    Note that $hat(f)(0) = 0$, hence
    $ 
    1/(2pi) integral_(-pi)^pi f(x)  d x = 0,
    $
    so we can extend $f$ to a $2pi$-periodic function on $RR$ and define
    $ 
    F(x) = integral_(-pi)^x f(t)  d t,
    $
    then $F$ is also $2pi$-periodic and absolutely continuous. By integration by parts, we have
    $ 
    hat(F)(n) = 1/(2pi) integral_(-pi)^pi F(x) e^(-i n x)  d x = -1/(2pi) integral_(-pi)^pi f(x) (e^(-i n x))/(-i n)  d x = (hat(f)(n))/(i n).
    $
    Let $F_N$ be the $N$-th Fejér kernel, then $F * F_N arrows.rr F$ uniformly as $N -> oo$, so
    $ 
    F(0) &= lim_(N -> oo) (F * F_N)(0) \
    &= lim_(N -> oo) sum_(n=-(N-1))^(N-1) (1 - (|n|)/N) hat(F)(n) \
    &= lim_(N -> oo) sum_(n=-(N-1))^(N-1) (1 - (|n|)/N) (hat(f)(n))/(i n) \
    &= lim_(N -> oo) 2 sum_(n=1)^(N-1) (1 - n/N) (hat(f)(n))/(i n) + hat(F)(0), 
    $
    $ 
    => & lim_(N -> oo) sum_(n=1)^(N-1) (1 - n/N) (hat(f)(n))/(n) = i/2 (F(0) - hat(F)(0)) \
    => & sum_(n=1)^(oo) (hat(f)(n))/(n) - lim_(N -> oo) 1/N sum_(n=1)^(N-1) hat(f)(n) = i/2 (F(0) - hat(F)(0)).
    $
    By Riemann-Lebesgue lemma, we have $lim_(N -> oo) 1/N sum_(n=1)^(N-1) hat(f)(n) = 0$, so $sum_(n=1)^(oo) (hat(f)(n))/(n)$ converges. 
    $qed$
]

#remark[
    If we choose $(a_n)$ such that $a_n > 0$, $a_n -> 0$ as $|n| -> oo$, and $sum_n a_n/(|n|) = oo$, then
    $ 
    sum_(n=1)^oo a_n sin(n x)
    $
    is not the Fourier series of any function in $L^1([-pi, pi])$. In particular, 
    $ 
    sum_(n=2)^oo (sin(n x))/(log n)
    $
    is not the Fourier series of any function in $L^1([-pi, pi])$.
]

By Riemann-Lebesgue lemma, the map
$ 
cal(F): f |-> (hat(f)(n))_(n in ZZ)
$
defines a linear map from $L^1([-pi, pi])$ to $c_0(ZZ)$, where
$ 
c_0(ZZ) = {(a_n)_(n in ZZ) : a_n -> 0 "as" |n| -> oo}.
$
Since $|hat(f)|_oo <= 1/(2pi) |f|_(L^1([-pi, pi]))$, $cal(F)$ is a bounded linear operator from $L^1([-pi, pi])$ to $c_0(ZZ) subset.eq ell^oo(ZZ)$. Also, $cal(F)$ is not surjective. 

=== Fourier Series for $L^2$-Functions

$L^2([-pi, pi])$ can be equipped with the inner product
$ 
chevron.l f, g chevron.r = 1/(2pi) integral_(-pi)^pi f(x) overline(g(x))  d x. 
$
The set $B = {e^(i n x) : n in ZZ}$ is a countable orthonormal set in $L^2([-pi, pi])$. If $f in L^2([-pi, pi])$, then $f in L^1([-pi, pi])$, so we can define its Fourier coefficients $hat(f)(n)$ for every $n in ZZ$. In fact, the Fourier series $sum_(n=-oo)^oo hat(f)(n) e^(i n x)$ can be viewed as the orthogonal projection of $f$ onto the closed subspace $overline("span"(B))$. By the Weierstrass approximation theorem, $"span"(B)$ is dense in the space of all continuous, $2pi$-periodic functions under the sup-norm. Since
$ 
|f - g|_2 <= (1/(2pi) integral_(-pi)^pi |f(x) - g(x)|^2  d x)^(1/2) <= |f - g|_oo,
$
$"span"(B)$ is also dense in $L^2([-pi, pi])$, so $B$ is a complete orthonormal set in $L^2([-pi, pi])$. For all $f in L^2([-pi, pi])$, the series
$ 
sum_(n=-oo)^oo hat(f)(n) e^(i n x)
$
converges to $f$ in $L^2$-norm, and
$ 
|f|_2^2 = sum_(n=-oo)^oo |hat(f)(n)|^2
$
by Parseval's identity. Thus $cal(F)$ is an isometric isomorphism between $L^2([-pi, pi])$ and $ell^2(ZZ)$.

== Fourier Transform

#definition[
    If $f in L^1(RR)$, then we can define its Fourier transform $hat(f)$ by
    $ 
    hat(f)(xi) = integral_(-oo)^oo f(x) e^(-2pi i xi x)  d x.
    $
]

For $f, g in L^1(RR)$, we have

+ $|hat(f)|_(L^oo) <= |f|_(L^1)$
+ $hat(f + a g) = hat(f) + a hat(g)$ for every $a in CC$
+ $hat(f)_y(xi) = hat(f)(xi) e^(-2pi i xi y)$ for every $y in RR$, where $f_y(x) = f(x - y)$
+ $hat(f_lambda)(xi) = hat(f)(xi/lambda)$ for every $lambda > 0$, where $f_lambda(x) = lambda f(lambda x)$
+ $hat(f * g) = hat(f) dot.op hat(g)$, 
+ If $f' in L^1(RR)$, then $hat(f')(xi) = 2pi i xi hat(f)(xi)$.


#proposition[
    Let $f in L^1(RR)$, then $hat(f)$ is uniformly continuous on $RR$. If further $x f(x) in L^1(RR)$, then $hat(f)$ is differentiable and
    $ 
    d/d xi hat(f)(xi) = hat(-2pi i x f)(xi).
    $
]
#proof[
    Let $xi, eta in RR$. We have
    $ 
    & hat(f)(xi + eta) - hat(f)(xi) = integral f(x)(e^(-2pi i (xi + eta) x) - e^(-2pi i xi x))  d x \
    => & |hat(f)(xi + eta) - hat(f)(xi)| <= integral |f(x)| |e^(-2pi i eta x) - 1|  d x -> 0
    $
    as $eta -> 0$ by dominated convergence theorem, so $hat(f)$ is uniformly continuous. If $x f(x) in L^1(RR)$, then
    $ 
    & (hat(f)(xi + eta) - hat(f)(xi))/(eta) = integral f(x) e^(-2pi i xi x) e^(-2pi i eta x) - 1/eta  d x \
    => & lim_(eta -> 0) (hat(f)(xi + eta) - hat(f)(xi))/(eta) = integral f(x) e^(-2pi i xi x) lim_(eta -> 0) (e^(-2pi i eta x) - 1)/eta  d x = hat(-2pi i x f)(xi)
    $
    by dominated convergence theorem, so $hat(f)$ is differentiable and $d/(d xi) hat(f)(xi) = hat(-2pi i x f)(xi)$.
    $qed$
]

#theorem(name: "Riemann-Lebesgue lemma")[
    If $f in L^1(RR)$, then
    $ 
    lim_(|xi| -> oo) hat(f)(xi) = 0.
    $
]
#proof[
    If $f$ in $C^1$ with compact support, then $hat(f)(xi) = 1/(2pi i xi) hat(f')(xi)$, so $hat(f)(xi) -> 0$ as $|xi| -> oo$. In general, let $epsilon > 0$, then there exists $g in C^1$ with compact support such that $|f - g|_(L^1) < epsilon$, so
    $ 
    |hat(f)(xi) - hat(g)(xi)| <= |f - g|_(L^1) < epsilon, \
    => limsup_(|xi| -> oo) |hat(f)(xi)| <= limsup_(|xi| -> oo) |hat(f)(xi) - hat(g)(xi)| + limsup_(|xi| -> oo) |hat(g)(xi)| < epsilon.
    $
    Since $epsilon$ is arbitrary, we have $lim_(|xi| -> oo) hat(f)(xi) = 0$.
    $qed$
]

The Fejér kernel on $RR$ is defined by
$ 
F_lambda(x) = lambda ( (sin (pi lambda x))/(pi lambda x) )^2, 
$
which comes from the Fourier transform of the function
$ 
f(x) = cases(
    1 - |x| & |x| < 1, 
    0 & |x| >= 1,
)
$
$F_lambda$ is an approximate identity as $lambda -> oo$, so $F_lambda * f -> f$ a.e. and in $L^1$-norm for every $f in L^1(RR)$. 

#lemma[
    If $f, g in L^1(RR)$ and
    $ 
    g(x) = integral G(xi) e^(2pi i xi x)  d xi
    $
    for some $G in L^1(RR)$, then
    $ 
    (f * g)(x) = integral hat(f)(xi) G(xi) e^(2pi i xi x)  d xi.
    $
]
#proof[
    By Fubini's theorem, we have
    $ 
    (f * g)(x) &= integral f(y) g(x - y)  d y \
    &= integral f(y) integral G(xi) e^(2pi i xi (x - y))  d xi  d y \
    &= integral G(xi) e^(2pi i xi x) integral f(y) e^(-2pi i xi y)  d y  d xi = integral hat(f)(xi) G(xi) e^(2pi i xi x)  d xi.
    $
    $qed$
]

#claim[
    $ 
    (f * F_lambda)(x) = integral_(-lambda)^lambda (1 - (|xi|)/lambda) hat(f)(xi) e^(2pi i xi x)  d xi.
    $   
]
#proof[
    Since
    $ 
    F_lambda(x) = integral_(-lambda)^lambda (1 - (|xi|)/lambda) e^(2pi i xi x)  d xi,
    $
    the conclusion follows from the previous lemma.
    $qed$
]

#claim(name: "Uniqueness of Fourier transform")[
    If $f in L^1(RR)$ and $hat(f)(xi) = 0$ for every $xi in RR$, then $f = 0$ a.e.
]
#proof[
    Let $F_lambda$ be the Fejér kernel on $RR$. We have
    $ 
    (f * F_lambda)(x) = integral_(-lambda)^lambda (1 - (|xi|)/lambda) hat(f)(xi) e^(2pi i xi x)  d xi = 0
    $
    for every $x$ and $lambda$. Since $F_lambda * f -> f$ a.e. as $lambda -> oo$, we have $f = 0$ a.e.
    $qed$
]

#claim(name: "Fourier inversion formula")[
    If $f in L^1(RR)$ and $hat(f) in L^1(RR)$, then
    $ 
    f(x) = integral hat(f)(xi) e^(2pi i xi x)  d xi
    $
    for a.e. $x$.
]
#proof[
    Let $F_lambda$ be the Fejér kernel on $RR$. We have
    $ 
    (f * F_lambda)(x) = integral_(-lambda)^lambda (1 - (|xi|)/lambda) hat(f)(xi) e^(2pi i xi x)  d xi.
    $
    Since $F_lambda * f -> f$ a.e. as $lambda -> oo$, we have
    $ 
    f(x) = integral_(-oo)^oo hat(f)(xi) e^(2pi i xi x)  d xi
    $
    for a.e. $x$.
    $qed$
]

#claim[
    The functions whose Fourier transform are compactly supported are dense in $L^1(RR)$.
]
#proof[
    Let $f in L^1(RR)$ and $epsilon > 0$. Since $hat(f)$ is uniformly continuous, there exists $lambda > 0$ such that $|hat(f)(xi)| < epsilon$ for every $|xi| > lambda$. Define
    $ 
    g(x) = integral_(-lambda)^lambda hat(f)(xi) e^(2pi i xi x)  d xi,
    $
    then $hat(g)$ is compactly supported and
    $ 
    |f - g|_(L^1) &= |integral_(-oo)^oo (hat(f)(xi) - hat(g)(xi)) e^(2pi i xi x)  d xi|_(L^1) \
    &<= integral_(-oo)^oo |hat(f)(xi) - hat(g)(xi)|  d xi = integral_(|xi| > lambda) |hat(f)(xi)|  d xi < epsilon.
    $
    $qed$
]

We may also want to define the Fourier transform for functions in $L^2(RR)$. 

#lemma[
    If $f$ is continuous with compact support on $RR$, then
    $ 
    |f|_(L^2)^2 = |hat(f)|_(L^2)^2.
    $
]
#proof[
    Write $tilde(f)(x) = overline(f(-x))$, and let $g(x) = f * tilde(f)$, then
    $ 
    g(0) = integral f(x) overline(f(x))  d x = |f|_(L^2)^2,
    $
    and
    $ 
    hat(g)(xi) = integral f(x) overline(f(x - y))  d x = integral f(x) overline(f(x - y)) e^(-2pi i xi y)  d y = |hat(f)(xi)|^2,
    $
    so by continuity of $f$, $g$ is also continuous, thus $g(0) = lim_(lambda -> oo) (g * F_lambda)(0)$. Therefore, 
    $ 
    |f|_(L^2)^2 &= lim_(lambda -> oo) (g * F_lambda)(0) \
    &= lim_(lambda -> oo) integral |hat(f)(xi)|^2 (1 - (|xi|)/lambda) e^(2pi i xi dot.op 0)  d xi = integral |hat(f)(xi)|^2  d xi = |hat(f)|_(L^2)^2.
    $
    $qed$
]

#theorem(name: "Plancherel")[
    There exists a unique surjective bounded linear operator
    $ 
    cal(F): L^2(RR) -> L^2(RR)
    $
    such that $cal(F) f = hat(f)$ for every $f in L^1(RR) inter L^2(RR)$ and $|cal(F) f|_(L^2) = |f|_(L^2)$ for every $f in L^2(RR)$.
]
#proof[
    Let $S = L^1(RR) inter L^2(RR)$, then $S$ is dense in $L^2(RR)$ since $C_c(RR) subset.eq S$ is dense in $L^2(RR)$. Hence, any bounded linear operator on $L^2(RR)$ is determined by its values on $S$, so there is at most one operator $cal(F)$ satisfying the conditions. By lemma, we have $|hat(f)|_(L^2) = |f|_(L^2)$ for every $f in S$, so by continuity, $cal(F)$ defines an isometry from $L^2(RR)$ to $L^2(RR)$. 

    It remains to show that $cal(F)$ is surjective. Let $g$ be a $C^2$-function with compact support. We claim that $g$ equals $cal(F) f$ for some $f in L^1(RR) inter L^2(RR)$. Define
    $ 
    f(x) = integral g(xi) e^(2pi i xi x)  d xi. 
    $
    Since $g$ has compact support, so does $g''$. Define
    $ 
    h(x) = integral g''(xi) e^(2pi i xi x)  d xi. 
    $
    Integrating by parts, we have
    $ 
    h(x) = -4pi^2 x^2 integral g(xi) e^(2pi i xi x)  d xi = -4pi^2 x^2 f(x),
    $
    so $|f(x)| <= (|h(x)|)/(4pi^2 x^2)$ for every $x eq.not 0$. Since $h$ is bounded and $1/x^2$ is integrable on $RR$, also $f$ is bounded near $0$, we have $f in L^1(RR)$. Therefore, the range of $cal(F)$ is dense in $L^2(RR)$ since $C_c^2(RR)$ is dense in $L^2(RR)$. Let $(cal(F) f_n)$ be a Cauchy sequence in $cal(F)(L^2(RR))$. Since $cal(F)$ is an isometry, $(f_n)$ is Cauchy in $L^2(RR)$, so there exists $f in L^2(RR)$ such that $f_n -> f$ in $L^2$-norm. By continuity of $cal(F)$, we have $cal(F) f_n -> cal(F) f$ in $L^2$-norm, so $cal(F)(L^2(RR))$ is closed in $L^2(RR)$. 
    $qed$
]

#remark[
    + If $f in L^2(RR)$, we will simply write $hat(f) = cal(F) f$. Given $f in L^2(RR)$, we can define $hat(f)$ to be the $L^2$-limit of $hat(f)_n$, where $(f_n)$ is any sequence in $L^1(RR) inter L^2(RR)$ such that $f_n -> f$ in $L^2$-norm. A natural choice is $f_n := f dot.op chi_([-n, n])$. For this choice of $(f_n)$, we see that the sequence
    $ 
    hat(f)_n(xi) = integral_(-n)^n f(x) e^(-2pi i xi x)  d x
    $
    converges to a function $hat(f)$ in $L^2$. 
    + Fourier transform on $L^2(RR)$ is invertible. We can obtain the inverse map by
    $ 
    f(x) = lim_(n -> oo) integral_(-n)^n hat(f)(xi) e^(2pi i xi x)  d xi
    $
    for every $f in L^2(RR)$, where the limit is taken in $L^2$-norm. 
    + By polarization identity, we have
    $ 
    chevron.l f, g chevron.r = chevron.l hat(f), hat(g) chevron.r
    $
    for every $f, g in L^2(RR)$, so $cal(F)$ preserves the inner product. 
]

= Abstract Measure

== Abstract Measure Spaces

#definition[
    Let $X$ be a nonempty set. 
    
    + A $sigma$-algebra $cal(M)$ is a collection of subsets of $X$ that contains $emptyset$ and is closed under complements and countable unions. Elements of $cal(M)$ are called measurable sets.
    + A measure $mu: cal(M) -> [0, oo]$ is a function such that $mu(emptyset) = 0$ and if $E_1, E_2, ...$ is a countable sequence of pairwise disjoint sets in $cal(M)$, then
        $ 
        mu(union.big_(n=1)^oo E_n) = sum_(n=1)^oo mu(E_n).
        $
    + A measure space is a triple $(X, cal(M), mu)$, where $X$ is a nonempty set, $cal(M)$ is a $sigma$-algebra on $X$, and $mu$ is a measure on $cal(M)$.
    + A measure space $(X, cal(M), mu)$ is $sigma$-finite if $X$ can be written as a countable union of elements of $cal(M)$ with finite measure.
]

#example[
    - Lebesgue measure. 
    - Let $X$ be a countable set, write $X = {x_n : n in NN}$, and let $cal(M) = 2^X$. Let $(mu_n)$ be a sequence in $[0, oo]$. For all $E subset.eq X$, define
        $ 
        mu(E) = sum_(x_n in E) mu_n,
        $
        then $mu$ is a measure on $cal(M)$. In particular, if $mu_n = 1$ for every $n$, then $mu$ is the counting measure on $X$.
    - Let $X = RR^d$ and $cal(M)$ be the collection of all Lebesgue measurable sets in $RR^d$. Define
        $ 
        mu(E) = integral_E f(x)  d x
        $
        for every $E in cal(M)$, where $f$ is a nonnegative measurable function on $RR^d$. If $f equiv 1$, then $mu$ is the Lebesgue measure on $RR^d$. 
]

=== Outer Measures

Recall that the Lebesgue measure on $RR$ is first defined as an outer measure, and then we restrict it to the $sigma$-algebra of Lebesgue measurable sets. 

#definition[
    Let $X$ be a nonempty set. An outer measure $mu_*$ on $X$ is a function from the power set of $X$ to $[0, oo]$ that satisfies
    
    + $mu_*(emptyset) = 0$;
    + If $E_1 subset.eq E_2$, then $mu_*(E_1) <= mu_*(E_2)$;
    + If $E_1, E_2, ...$ is a countable sequence of subsets of $X$, then
    $ 
    mu_*(union.big_(n=1)^oo E_n) <= sum_(n=1)^oo mu_*(E_n).
    $
]

#definition[
    Let $mu_*$ be an outer measure on $X$. A set $E subset.eq X$ is Carathéodory measurable, or simply measurable, if
    $ 
    mu_*(A) = mu_*(A inter E) + mu_*(A inter E^c)
    $
    for every $A subset.eq X$. Define $cal(M)$ to be the collection of all measurable sets. 
]

To prove that a set $E$ is measurable, it suffices to show that $mu_*(A) >= mu_*(A inter E) + mu_*(A inter E^c)$ for every $A subset.eq X$, since the opposite inequality always holds by subadditivity of $mu_*$. In particular, every set $E$ with $mu_*(E) = 0$ is measurable, since $mu_*(A) >= mu_*(A inter E^c)$ for every $A subset.eq X$.

#lemma[
    If $E_1, E_2, ... in cal(M)$ are pairwise disjoint, then for all $A subset.eq X$, 
    $ 
    mu_*(A inter union.big_(n=1)^oo E_n) = sum_(n=1)^oo mu_*(A inter E_n).
    $
]
#proof[
    When there is only one set $E_1$, there's nothing to prove. For two disjoint sets $E_1$ and $E_2$, we have
    $ 
    mu_*(A inter (E_1 union E_2)) &= mu_*(A inter (E_1 union E_2) inter E_2) + mu_*(A inter (E_1 union E_2) inter E_2^c) \
    &= mu_*(A inter E_2) + mu_*(A inter E_1). 
    $
    By induction, the finite case follows. For the infinite case, we have
    $ 
    & mu_*(A inter union.big_(n=1)^oo E_n) <= sum_(n=1)^oo mu_*(A inter E_n), \
    => & mu_*(A inter union.big_(n=1)^oo E_n) >= mu_*(A inter union.big_(n=1)^N E_n) = sum_(n=1)^N mu_*(A inter E_n)
    $
    for every $N$, so $mu_*(A inter union.big_(n=1)^oo E_n) >= sum_(n=1)^oo mu_*(A inter E_n)$.
    $qed$
]

#theorem[
    Given an outer measure $mu_*$ on $X$, then $cal(M)$ is a $sigma$-algebra on $X$ and the restriction of $mu_*$ to $cal(M)$ is a measure.
]
#proof[
    For all $A subset.eq X$, we have
    $ 
    mu_*(A) = mu_*(X inter A) + mu_*(emptyset inter A),
    $
    so $emptyset in cal(M)$. If $E in cal(M)$, then since the definition of measurability is symmetric in $E$ and $E^c$, we have $E^c in cal(M)$. 

    If $E, F in cal(M)$, then for all $A subset.eq X$, we have
    $ 
    mu_*(A) &= mu_*(A inter E) + mu_*(A inter E^c) \
    &= mu_*(A inter E inter F) + mu_*(A inter E inter F^c) + mu_*(A inter E^c inter F) + mu_*(A inter E^c inter F^c) \
    &>= mu_*(A inter (E union F)) + mu_*(A inter (E union F)^c),
    $
    so $E union F in cal(M)$. By induction, we have $union.big_(n=1)^N E_n in cal(M)$ for every $N$. If $E_1, E_2, ...$ are pairwise disjoint, then for each $N$, we have $union.big_(n=1)^N E_n in cal(M)$, so for all $A subset.eq X$, we have
    $ 
    mu_*(A) &= mu_*(A inter union.big_(n=1)^N E_n) + mu_*(A inter (union.big_(n=1)^N E_n)^c) \
    &>= sum_(n=1)^N mu_*(A inter E_n) + mu_*(A inter (union.big_(n=1)^oo E_n)^c). 
    $
    When $N -> oo$, we have
    $ 
    mu_*(A) &>= sum_(n=1)^oo mu_*(A inter E_n) + mu_*(A inter (union.big_(n=1)^oo E_n)^c) \
    &= mu_*(A inter union.big_(n=1)^oo E_n) + mu_*(A inter (union.big_(n=1)^oo E_n)^c),
    $
    so $union.big_(n=1)^oo E_n in cal(M)$. If $E_1, E_2, ...$ are not pairwise disjoint, then we can write
    $ 
    F_1 &= E_1, \
    F_2 &= E_2 inter E_1^c, \
    F_3 &= E_3 inter E_1^c inter E_2^c, \
    &dots.v \
    F_n &= E_n inter inter_(k=1)^(n-1) E_k^c, \
    &dots.v
    $
    so $F_1, F_2, ...$ are pairwise disjoint and $union.big_(n=1)^oo E_n = union.big_(n=1)^oo F_n$, thus $union.big_(n=1)^oo E_n in cal(M)$.
    $qed$
]

#proposition[
    In $RR^d$ with the Lebesgue outer measure, Lebesgue measurability is equivalent to Carathéodory measurability.
]

#proposition[
    Suppose that $E_1, E_2, ...$ are measurable sets.

    + If $E_n arrow.t E$, then $m(E_n) -> m(E)$.
    + If $E_n arrow.b E$ and $m(E_1) < oo$, then $m(E_n) -> m(E)$.
]
#proof[
    Same as the proof of continuity of measure for Lebesgue measurable sets (See Chapter 1 @prop:continuity_of_measure).
    $qed$
]

=== Metric Outer Measures

Suppose that $X$ is a metric space. The Borel $sigma$-algebra $cal(B)_X$ on $X$ is the smallest $sigma$-algebra on $X$ that contains all open sets. We want to construct a measure defined on $cal(B)_X$.

For $A, B subset.eq X$, define
$ 
d(A, B) = inf{d(x, y) : x in A, y in B}.
$

#definition[
    An outer measure $mu_*$ on $X$ is a metric outer measure if
    $ 
    mu_*(A union B) = mu_*(A) + mu_*(B)
    $
    for every $A, B subset.eq X$ with $d(A, B) > 0$.
]

#theorem[
    If $mu_*$ is a metric outer measure on $X$, then every Borel set is $mu_*$-measurable. In particular, the restriction of $mu_*$ to $cal(B)_X$ is a measure. 
]
#proof[
    It suffices to show that every closed set is $mu_*$-measurable. Let $F$ be a closed set and $A subset.eq X$ with $mu_*(A) < oo$. For each $n$, define
    $ 
    A_n = {x in A : d(x, F) > 1/n}.
    $
    Then $A_n subset.eq A_(n+1)$. Since $F$ is closed, we have $F^c inter A = union.big_(n=1)^oo A_n$. Also, $d(F, A_n) > 0$ for every $n$, so
    $ 
    mu_*(A) &= mu_*((F inter A) union (F^c inter A)) \
    &>= mu_*((F inter A) union A_n) = mu_*(F inter A) + mu_*(A_n)
    $
    for every $n$. Let $B_n = A_(n+1) backslash A_n$. Note that
    $ 
    d(B_(n+1), A_n) >= 1/n - 1/n+1 > 0,
    $
    so
    $ 
    mu_*(A_(2n+1)) &>= mu_*(B_2 union B_4 union dots.c union B_(2n)) = sum_(k=1)^n mu_*(B_(2k)), \
    mu_*(A_(2n)) &<= mu_*(B_1 union B_3 union dots.c union B_(2n-1)) = sum_(k=1)^n mu_*(B_(2k-1)).
    $
    Since $mu_*(A) < oo$, both series $sum_(k=1)^oo mu_*(B_(2k))$ and $sum_(k=1)^oo mu_*(B_(2k-1))$ are convergent. By countable subadditivity, we have
    $ 
    mu_*(A_n) <= mu_*(F^c inter A) = mu_*(union.big_(k=1)^oo A_k) <= mu_*(A_n) + sum_(k=n+1)^oo mu_*(B_(2k-1)),
    $
    so $lim_(n -> oo) mu_*(A_n) = mu_*(F^c inter A)$. Therefore, $mu_*(A) >= mu_*(F inter A) + mu_*(F^c inter A)$, so $F$ is $mu_*$-measurable.

    If $mu_*(A) = oo$, then $mu_*(A) >= mu_*(F inter A) + mu_*(F^c inter A)$ holds trivially, so $F$ is $mu_*$-measurable.
    $qed$
]

#definition[
    A measue $mu$ defined on the Borel sets of a metric space $X$ is called a Borel measure.
]

If a Borel measure is finite on all balls (of finite radius), then it has nice regularity properties.

#proposition[
    Suppose that the Borel measure $mu$ is finite on all balls in $X$ of finite radius. Then for every Borel set $E$ and $epsilon > 0$, there exists an open set $U$ and a closed set $F$ such that $F subset.eq E subset.eq U$ and
    $ 
    mu(G backslash E) < epsilon,  quad  mu(E backslash F) < epsilon.
    $
]
#proof[
    We will first show that inner regularity holds for $F_sigma$-sets. Let $F^* = union.big_(n=1)^oo F_n$ be an $F_sigma$-set, where $F_n$ are closed sets. We may assume that $F_n subset.eq F_(n+1)$ for every $n$. Fix $x_0 in X$ and let $B_n = {x in X : d(x, x_0) < n}$ for every $n$, then
    $ 
    X = union.big_(n=1)^oo B_n,  quad  F^* = union.big_(n=1)^oo (F^* inter (overline(B_n) backslash B_(n-1))).
    $
    Note that $F^* inter (overline(B_n) backslash B_(n-1))$ is the increasing limit of $F_k inter (overline(B_n) backslash B_(n-1))$ as $k -> oo$, hence
    $ 
    mu(F^* inter (overline(B_n) backslash B_(n-1))) = lim_(k -> oo) mu(F_k inter (overline(B_n) backslash B_(n-1))). 
    $
    Since $mu(overline(B_n)) < oo$, we can find an integer $N_n$ such that
    $ 
    mu((F^* backslash F_(N_n)) inter (overline(B_n) backslash B_(n-1))) < epsilon/2^n.
    $
    Let $F = union.big_(n=1)^oo F_(N_n) inter (overline(B_n) backslash B_(n-1))$, then $mu(F^* backslash F) < epsilon$. Since $F inter overline(B_n)$ is a finite union of closed sets, it is closed, hence $F$ itself is closed.

    Let $cal(C)$ be the collection of sets that satisfy both outer and inner regularity (by closed sets). Clearly $cal(C)$ is closed under complements. Suppose that $E_1, E_2, ...$ are sets in $cal(C)$. We want to prove that $E = union.big_(n=1)^oo E_n in cal(C)$. We can find open sets $U_n$ and closed sets $F_n$ such that $F_n subset.eq E_n subset.eq U_n$ and
    $ 
    mu(U_n backslash E_n) < epsilon/2^n,  quad  mu(E_n backslash F_n) < epsilon/2^n
    $
    for every $n$. Let $U = union.big_(n=1)^oo U_n$, then $U$ is open and $mu(U backslash E) <= sum_(n=1)^oo mu(U_n backslash E_n) < epsilon$. Let $F^* = union.big_(n=1)^oo F_n$, then $F^*$ is a $F_sigma$-set and $mu(E backslash F^*) < epsilon$. By the first step, we can find a closed set $F$ such that $F subset.eq F^*$ and $mu(F^* backslash F) < epsilon$, hence $mu(E backslash F) < 2epsilon$. Therefore, $E in cal(C)$. 

    It remains to show that every open set is in $cal(C)$. Let $U$ be an open set, then outer regularity is trivial. For inner regularity, write
    $ 
    F_k = {x in overline(B_k) : d(x, U^c) >= 1/k}.
    $
    Then $F_k$ is closed and $U = union.big_(k=1)^oo F_k$, so $U$ is a $F_sigma$-set and we can find a closed set $F$ such that $F subset.eq U$ and $mu(U backslash F) < epsilon$. Therefore, $U in cal(C)$.
    $qed$
]

=== Premeasures

#definition[
    Let $X$ be a set. An algebra $cal(A)$ on $X$ is a collection of subsets of $X$ that contains $emptyset$ and is closed under complements and finite unions. 
]

#definition[
    Let $cal(A)$ be an algebra on $X$. A premeasure $mu_0: cal(A) -> [0, oo]$ is a function such that
    
    + $mu_0(emptyset) = 0$, and
    + if $E_1, E_2, ...$ is a countable collection of pairwise disjoint sets in $cal(A)$ such that $union.big_(n=1)^oo E_n in cal(A)$, then
        $ 
        mu_0(union.big_(n=1)^oo E_n) = sum_(n=1)^oo mu_0(E_n).
        $
        In particular, $mu_0$ is finitely additive on $cal(A)$.
]

#lemma[
    Let $mu_0$ be a premeasure on an algebra $cal(A)$. For any $E subset.eq X$, define
    $ 
    mu_*(E) = inf{sum_(n=1)^oo mu_0(E_n) : E_n in cal(A), E subset.eq union.big_(n=1)^oo E_n}.
    $
    Then $mu_*$ is an outer measure on $X$ that satisfies
    
    + $mu_*(E) = mu_0(E)$ for every $E in cal(A)$;
    + all sets in $cal(A)$ are $mu_*$-measurable.
]
#proof[
    We will first show that $mu_*$ is an outer measure. Since $mu_0(emptyset) = 0$, we have $mu_*(emptyset) = 0$. If $E_1 subset.eq E_2$, then every cover of $E_2$ is also a cover of $E_1$, so $mu_*(E_1) <= mu_*(E_2)$. If $E_1, E_2, ...$ is a countable sequence of subsets of $X$, then for each $n$, we can find a sequence $(E_(n, k))_(k=1)^oo$ in $cal(A)$ such that $E_n subset.eq union.big_(k=1)^oo E_(n, k)$ and
    $ 
    sum_(k=1)^oo mu_0(E_(n, k)) < mu_*(E_n) + epsilon/2^n.
    $
    Then $union.big_(n=1)^oo E_n subset.eq union.big_(n=1)^oo union.big_(k=1)^oo E_(n, k)$ and
    $ 
    sum_(n=1)^oo sum_(k=1)^oo mu_0(E_(n, k)) < sum_(n=1)^oo (mu_*(E_n) + epsilon/2^n) = sum_(n=1)^oo mu_*(E_n) + epsilon,
    $
    so $mu_*(union.big_(n=1)^oo E_n) <= sum_(n=1)^oo mu_*(E_n)$.

    We will then show that $mu_*(E) = mu_0(E)$ for every $E in cal(A)$. Since $E$ itself is a cover of $E$, we have $mu_*(E) <= mu_0(E)$. Suppose that $E subset.eq union.big_(n=1)^oo E_n$ for some sequence $(E_n)$ in $cal(A)$. Let
    $ 
    F_j = E inter (E_j backslash union.big_(k=1)^(j-1) E_k),
    $
    then $F_1, F_2, ...$ are pairwise disjoint sets in $cal(A)$. Also, $F_j subset.eq E_j$ and $union.big_(j=1)^oo F_j = E$, so by definition of premeasure, we have
    $ 
    mu_0(E) = mu_0(union.big_(j=1)^oo F_j) = sum_(j=1)^oo mu_0(F_j) <= sum_(j=1)^oo mu_0(E_j).
    $
    Taking infimum over all covers of $E$, we have $mu_0(E) <= mu_*(E)$, hence $mu_*(E) = mu_0(E)$.

    Finally, we will show that all sets in $cal(A)$ are $mu_*$-measurable. Let $E in cal(A)$ and $A subset.eq X$. Let $epsilon > 0$. There exists $A_1, A_2, ... in cal(A)$ such that $A subset.eq union.big_(n=1)^oo A_n$ and
    $ 
    sum_(n=1)^oo mu_0(A_n) < mu_*(A) + epsilon.
    $
    We have
    $ 
    E inter A_j in cal(A),  quad  union.big_(n=1)^oo (E inter A_n) supset.eq E inter A, \
    E^c inter A_j in cal(A),  quad  union.big_(n=1)^oo (E^c inter A_n) supset.eq E^c inter A, \
    => sum_(n=1)^oo mu_0(E inter A_n) >= mu_*(E inter A),  quad  sum_(n=1)^oo mu_0(E^c inter A_n) >= mu_*(E^c inter A), \
    => mu_*(E inter A) + mu_*(E^c inter A) <= sum_(n=1)^oo mu_0(A_n) < mu_*(A) + epsilon.
    $
    Since $epsilon$ is arbitrary, we have $mu_*(E inter A) + mu_*(E^c inter A) <= mu_*(A)$, so $E$ is $mu_*$-measurable.
    $qed$
]

#corollary[
    Suppose that $cal(A)$ is an algebra on $X$ and $mu_0$ is a premeasure on $cal(A)$. Let $cal(M)$ be the $sigma$-algebra generated by $cal(A)$. Then there exists a measure $mu$ on $cal(M)$ that extends $mu_0$. Moreover, if $mu$ is $sigma$-finite, then such $mu$ is unique.
]
#proof[
    By the previous lemma, we can find an outer measure $mu_*$ on $X$ such that $mu_*(E) = mu_0(E)$ for every $E in cal(A)$ and all sets in $cal(A)$ are $mu_*$-measurable. 

    Suppose that $nu$ is another measure on $cal(M)$ that coincides with $mu_0$ on $cal(A)$. Suppose that $F in cal(M)$ with $mu(F) < oo$. Let $E_1, E_2, ...$ be a sequence in $cal(A)$ be a cover for $F$, then
    $ 
    nu(F) <= sum_(n=1)^oo nu(E_n) = sum_(n=1)^oo mu_0(E_n).
    $
    Taking infimum over all covers of $F$, we have $nu(F) <= mu(F)$. Suppose $E = union.big_(n=1)^oo E_n$ with $E_n in cal(A)$. Define $F_n = E_n backslash union.big_(k=1)^(n-1) E_k$, then $F_1, F_2, ...$ are pairwise disjoint sets in $cal(A)$ and $union.big_(n=1)^oo F_n = E$, so
    $ 
    nu(E) = nu(union.big_(n=1)^oo F_n) = lim_(N -> oo) nu(union.big_(n=1)^N F_n) = lim_(N -> oo) mu(union.big_(n=1)^N F_n) = mu(E).
    $
    We can choose $(E_j)$ in $cal(A)$ such that $F subset.eq union.big_(j=1)^oo E_j =: E$ and $mu(E) < mu(F) + epsilon$. Since $F$ has finite measure, we have $mu(E backslash F) < epsilon$, so 
    $ 
    mu(F) &<= mu(E) = nu(E) = nu(F) + nu(E backslash F) \
    &<= nu(F) + mu(E backslash F) < nu(F) + epsilon.
    $
    Since $epsilon$ is arbitrary, we have $mu(F) <= nu(F)$, hence $mu(F) = nu(F)$. 

    Since we can write $X = union.big_(n=1)^oo E_n$ with $E_n in cal(M)$ pairwise disjoint and $mu(E_n) < oo$ for every $n$, for general $F in cal(M)$, we have
    $ 
    mu(F) = sum_(n=1)^oo mu(F inter E_n) = sum_(n=1)^oo nu(F inter E_n) = nu(F).
    $
    $qed$
]

== Integration

Let $(X, cal(M), mu)$ be a measure space. We will assume that $mu$ is $sigma$-finite. 

#definition[
    A function $f: X -> [-oo, oo]$ is measurable if $f^(-1)([-oo, a)) in cal(M)$ for every $a in RR$.
]

#definition[
    A simple function on $X$ is a function of the form
    $ 
    f = sum_(k=1)^N a_k chi_(E_k),
    $
    where $a_1, ..., a_N$ are real numbers and $E_1, ..., E_N$ are measurable sets of finite measure. 
]

As before, if $f$ is measurable, we can find a sequence of simple functions that converges to $f$ pointwise. We can then define the Lebesgue integral first for simple functions, and then for general measurable functions by taking limits. A measurable function $f$ is integrable if
$ 
integral_X |f(x)|  d mu(x) < oo. 
$
Basic properties such as linearity, monotonicity still holds, as well as limit theorems such as monotone convergence theorem, Fatou's lemma, and dominated convergence theorem.

For $p in [1, oo]$, we can still define the $L^p$-norm of a measurable function $f$ by
$ 
|f|_p = (integral_X |f(x)|^p  d mu(x))^(1/p)
$
and the associated $L^p$-space by
$ 
L^p(X, mu) = {f : X -> CC : f "is measurable and" |f|_p < oo}.
$
As usual, $L^p(X, mu)$ is a Banach space under the $L^p$-norm, and $L^2(X, mu)$ is a Hilbert space under the inner product
$ 
chevron.l f, g chevron.r = integral_X f(x) overline(g(x))  d mu(x).
$

=== Product Measures and Fubini's Theorem

Suppose that $(X_1, cal(M)_1, mu_1)$ and $(X_2, cal(M)_2, mu_2)$ are two measure spaces. We want to construct a measure on the product space $X_1 times X_2$.

Throughout this section, we'll assume that the measure spaces are complete and $sigma$-finite.

#definition[
    A measurable rectangle in $X_1 times X_2$ is a set of the form $A times B$ with $A in cal(M)_1$ and $B in cal(M)_2$. Let $cal(A)$ be the collection of all finite unions of disjoint measurable rectangles in $X_1 times X_2$. Then $cal(A)$ is an algebra on $X_1 times X_2$.
]

For a measurable rectangle $A times B$, define
$ 
mu_0(A times B) = mu_1(A) dot.op mu_2(B).
$
We claim that $mu_0$ is a premeasure. Assume that $A times B = union.big_(j=1)^oo A_j times B_j$, where the rectangles $A_j times B_j$ are pairwise disjoint. If $x_1 in A$, then for each $x_2 in B$, the pair $(x_1, x_2)$ belongs to exactly one $A_j times B_j$, so
$ 
sum_(j=1)^oo chi_(A_j)(x_1) dot.op chi_(B_j)(x_2) = chi_A(x_1) dot.op chi_B(x_2). 
$
Integrating both sides with respect to $mu_2$ gives
$ 
sum_(j=1)^oo chi_(A_j)(x_1) dot.op mu_2(B_j) = chi_A(x_1) dot.op mu_2(B).
$
Integrating both sides with respect to $mu_1$ gives
$ 
sum_(j=1)^oo mu_0(A_j times B_j) = sum_(j=1)^oo mu_1(A_j) dot.op mu_2(B_j) = mu_1(A) dot.op mu_2(B) = mu_0(A times B).
$
Therefore, $mu_0$ is a premeasure. We can then extend $mu_0$ to a measure $mu$ on the $sigma$-algebra generated by $cal(A)$. Thus we have defined the product measure space $(X_1 times X_2, cal(M), mu_1 times mu_2)$.

Given $E in cal(M)$, define the slices
$ 
E_(x_1) = {x_2 in X_2 : (x_1, x_2) in E},  quad  E^(x_2) = {x_1 in X_1 : (x_1, x_2) in E}.
$
Write $cal(A)_sigma$ to be the collection of sets that are countable unions of elements of $cal(A)$, and $cal(A)_(sigma delta)$ to be the collection of sets that are countable intersections of elements of $cal(A)_sigma$. 

#lemma(id: "lm:measurability_of_slices")[
    If $E in cal(A)_(sigma delta)$, then $E^(x_2)$ is $cal(M)_1$-measurable for every $x_2 in X_2$, and $x_2 |-> mu_1(E^(x_2))$ is an $cal(M)_2$-measurable function on $X_2$. Moreover, 
    $ 
    integral_(X_2) mu_1(E^(x_2))  d mu_2(x_2) = (mu_1 times mu_2)(E).
    $
]
#proof[
    If $E = A times B$ is a measurable rectangle, then
    $ 
    E^(x_2) = cases(
        A & "if" x_2 in B, 
        emptyset & "otherwise",
    )
    $
    Also, $x_2 |-> mu_1(E^(x_2)) = mu_1(A) dot.op chi_B(x_2)$ is $cal(M)_2$-measurable and
    $ 
    integral_(X_2) mu_1(E^(x_2))  d mu_2(x_2) = mu_1(A) dot.op mu_2(B) = (mu_1 times mu_2)(E).
    $

    Next, we suppose that $E in A_sigma$. We can write $E$ as a countable disjoint union of measurable rectangles $union.big_(j=1)^oo E_j$, where $E_j in cal(A)$. Note that
    $ 
    E^(x_2) = union.big_(j=1)^oo E_j^(x_2), 
    $
    and since $E_j$ are disjoint, by monotone convergence theorem, we have
    $ 
    integral_(X_2) mu_1(E^(x_2))  d mu_2(x_2) = sum_(j=1)^oo integral_(X_2) mu_1(E_j^(x_2))  d mu_2(x_2) = sum_(j=1)^oo (mu_1 times mu_2)(E_j) = (mu_1 times mu_2)(E).
    $

    Finally, we deal with general $E in cal(A)_(sigma delta)$. Assume $(mu_1 times mu_2)(E) < oo$. By definition of $cal(A)_(sigma delta)$, there exists a sequence $(E_j)$ in $cal(A)_sigma$ such that $E = inter_(j=1)^oo E_j$ and $E_j supset.eq E_(j+1)$ for every $j$. Further assume that $(mu_1 times mu_2)(E_1) < oo$ and each slice also has finite measure $mu_1(E_j^(x_2)) < oo$. Set
    $ 
    f_j(x_2) = mu_1(E_j^(x_2)),  quad  f(x_2) = mu_1(E^(x_2)).
    $
    Since $E^(x_2) = inter_(j=1)^oo E_j^(x_2)$ is the countable intersection of $cal(M)_1$-measurable sets, it is $cal(M)_1$-measurable, so $f$ is well-defined, so for every $x_2$, 
    $ 
    f(x_2) = mu_1(E^(x_2)) = mu_1(inter_(j=1)^oo E_j^(x_2)) = lim_(j -> oo) mu_1(E_j^(x_2))
    $
    is $cal(M)_2$-measurable. Since $(f_j)$ is decreasing and converges to $f$, by monotone convergence theorem, we have
    $ 
    integral_(X_2) mu_1(E^(x_2))  d mu_2(x_2) &= lim_(j -> oo) integral_(X_2) mu_1(E_j^(x_2))  d mu_2(x_2) \
    &= lim_(j -> oo) (mu_1 times mu_2)(E_j) = (mu_1 times mu_2)(E).
    $

    For general $E$, by $sigma$-finiteness, there exists sequences of sets $F_1 subset.eq F_2 subset.eq dots.c subset.eq X_1$ and $G_1 subset.eq G_2 subset.eq dots.c subset.eq X_2$ such that
    $ 
    X_1 = union.big_(j=1)^oo F_j,  quad  X_2 = union.big_(j=1)^oo G_j,  quad  mu_1(F_j) < oo,  quad  mu_2(G_j) < oo
    $
    for every $j$. Replace $E, E_k$ by $E inter (F_j times G_j), E_k inter (F_j times G_j)$ and take limit as $j -> oo$, we have
    $ 
    integral_(X_2) mu_1(E^(x_2))  d mu_2(x_2) = (mu_1 times mu_2)(E).
    $
    $qed$
]

#proposition[
    For all $E in cal(M)$, exists $F in cal(A)_(sigma delta)$ such that $E subset.eq F$ and
    $ 
    (mu_1 times mu_2)(E) = (mu_1 times mu_2)(F).
    $
]

#proposition[
    @lm:measurability_of_slices holds for $E in cal(M)$, except that we now only have $E^(x_2)$ is $cal(M)_1$-measurable for $mu_2$-a.e. $x_2$ and $mu_1(E^(x_2))$ is defined for only $mu_2$-a.e. $x_2$.
]
#proof[
    Follows from the previous proposition and @lm:measurability_of_slices.
    $qed$
]

#theorem[
    Suppose that $f in L^1(X_1 times X_2, mu_1 times mu_2)$. Then

    + For $mu_2$-a.e. $x_2$, the slice $f^(x_2)(x_1) = f(x_1, x_2)$ is in $L^1(X_1, mu_1)$;
    + $x_2 |-> integral_(X_1) f(x_1, x_2)  d mu_1(x_1)$ is integrable on $X_2$;
    + 
        $ 
        integral_(X_2) (integral_(X_1) f(x_1, x_2)  d mu_1(x_1))  d mu_2(x_2) = integral_(X_1 times X_2) f(x_1, x_2)  d(mu_1 times mu_2)(x_1, x_2).
        $
]
#proof[
    By the previous proposition the results holds for $f = chi_E$ with $E in cal(M)$. By linearity, it also holds for simple functions. For nonnegative measurable functions, we can find an increasing sequence of simple functions that converges to $f$ pointwise, so the result follows from monotone convergence theorem. For general integrable functions, we can write $f = f^+ - f^-$, where $f^+, f^- >= 0$ are integrable, so the result follows from the nonnegative case.
    $qed$
]

=== Stieltjes Integrals

Stiltjes integrals are a generalization of Riemann integrals, where the increments $d x$ are replaced by increments $d F(x)$ for some increasing function $F$. 

Since $F$ is increasing, it has at most countably many discontinuities. At a discontinuity $x_0$, the left and right limits of $F$ exist, and we denote them by $F(x_0^-)$ and $F(x_0^+)$ respectively. We modify $F$ at these discontinuities by defining $F(x_0) = F(x_0^+)$, so that $F$ is right-continuous.

#theorem[
    Let $F$ be an increasing right-continuous function on $RR$. Then there exists a unique Borel measure $mu$ on $RR$ such that
    $ 
    mu((a, b]) = F(b) - F(a)
    $
    for every $a < b$. Conversely, if $mu$ is a Borel measure on $RR$ that is finite on all bounded intervals, then $F$ defined by
    $ 
    F(x) = cases(
        mu((0, x]) & x >= 0, 
        0 & x = 0, 
        -mu((x, 0]) & x < 0,
    )
    $
    is an increasing right-continuous function on $RR$. 
]
#proof[
    The proof is similar to the construction of Lebesgue measure. 

    Define
    $ 
    mu_*(E) = inf{sum_(j=1)^oo (F(b_j) - F(a_j)) : E subset.eq union.big_(j=1)^oo (a_j, b_j]}.
        $
    Then $mu_*$ is an outer measure on $RR$. We will show that $mu_*((a, b]) = F(b) - F(a)$ for every $a < b$. Since $(a, b]$ itself is a cover of $(a, b]$, we have $mu_*((a, b]) <= F(b) - F(a)$. Let $epsilon > 0$ and suppose that $union.big_(j=1)^oo (a_j, b_j]$ is a cover of $(a, b]$, then it also covers $[a', b]$ for all $a' in (a, b)$. By right continuity of $F$, $exists b_j' > b_j$ such that $F(b_j') <= F(b_j) + epsilon/2^j$. Then $union.big_(j=1)^oo (a_j, b_j']$ is a cover of $[a', b]$, so
    $ 
    F(b) - F(a') &<= sum_(j=1)^N (F(b_j') - F(a_j)) \
    &<= sum_(j=1)^N (F(b_j) - F(a_j) + epsilon/2^j) \
    &<= sum_(j=1)^N (F(b_j) - F(a_j)) + epsilon.
    $
    Taking limit as $N -> oo$ and then $a' -> a^+$, we have $F(b) - F(a) <= sum_(j=1)^oo (F(b_j) - F(a_j)) + epsilon$. Since $epsilon$ is arbitrary, we have $mu_*((a, b]) = F(b) - F(a)$.

    As before, we can show that $mu_*$ is a metric outer measure. This implies the existence of a Borel measure $mu$ on $RR$ such that $mu((a, b]) = mu_*((a, b]) = F(b) - F(a)$ for every $a < b$. 

    Let $nu$ be another Borel measure on $RR$ such that $nu((a, b]) = F(b) - F(a)$ for every $a < b$. We can write an open interval $(a, b)$ as a countable union of $(a_j, b_j]$, hence by continuity of measures, we have $nu((a, b)) = F(b) - F(a) = mu((a, b))$. Then by outer regularity, they agree on all Borel sets.

    For the converse, increasingness of $F$ is trivial. For right continuity, let $x > 0$ and define $E_n = (0, x + 1/n]$, then $E_n$ decreases to $(0, x] =: E$. Since $mu(E_n) < oo$, we have
    $ 
    lim_(n -> oo) F(x + 1/n) = lim_(n -> oo) mu(E_n) = mu(E) = F(x),
    $
    so $F$ is right-continuous at $x$. The case $x < 0$ is similar.
    $qed$
]

#remark[
    Alternatively, we can show that $mu_0((a, b]) = F(b) - F(a)$ is a premeasure on the algebra of finite unions of disjoint intervals of the form $(a, b]$, and then extend $mu_0$ to a measure $mu$ on the $sigma$-algebra generated by these intervals, which is the Borel $sigma$-algebra. 
]

If $F$ is an increasing right-continuous function on $RR$, from the previous theorem, we obtain the corresponding Borel measure $mu$ on $RR$. We can then define the Stieltjes integral of a measurable function $f$ with respect to $F$ by
$ 
integral_a^b f(x)  d F(x) = integral_a^b f(x)  d mu(x).
$

#remark[
    +   We can extend the results to $F$ that is of bounded variation, by decomposing into real and imaginary parts, then as differences of two increasing functions. 
    +   If $F$ is absolutely continuous, then $F$ is differentiable a.e. and
        $ 
        integral_a^b f(x)  d F(x) = integral_a^b f(x) F'(x)  d x
        $
        for all functions $f$ Borel measurable and integrable with respect to $mu$. 
    +   Suppose that $F$ is a right-continuous, pure jump function on $[a, b]$ with jumps $alpha_n$ at points $x_n$, then whenever $f$ is continuous and has compact support, we have
        $ 
        integral_a^b f(x)  d F(x) = sum_(n=1)^oo alpha_n f(x_n).
        $
        This corresponds to the measure $mu$ such that $mu({x_n}) = alpha_n$ and $mu(E) = 0$ for any $E$ that does not contain any $x_n$. A special case is the Heaviside function $H = chi_([0, oo))$, which has a jump of $1$ at $0$, so
        $ 
        integral_(-oo)^oo f(x)  d H(x) = f(0).
        $
]

== Absolute Continuity of Measures

=== Signed Measures

A signed measure possesses all the properties of a measure except that it can take negative values.

#definition[
    A signed measure on a $sigma$-algebra $cal(M)$ is a function $nu: cal(M) -> (-oo, oo]$ such that $nu(emptyset) = 0$ and if $(E_n)$ is a sequence of pairwise disjoint sets in $cal(M)$, then
    $
    nu(union.big_(n=1)^oo E_n) = sum_(n=1)^oo nu(E_n).
    $
]

From the definition, for the equality to hold, the sum on the right hand side must be independent of rearrangement. In particular, if the left hand side is finite, then the sum must converge absolutely. 

If $f$ is a real-valued measurable function with $integral f^- d mu < oo$, then
$
nu(E) = integral_E f d mu
$
defines a signed measure on $cal(M)$. We can also define complex measures in a similar way. 

#definition[
    Let $nu$ be a signed measure on a $sigma$-algebra $cal(M)$. The total variation $|nu|$ of $nu$ is defined by
    $
    |nu|(E) = sup sum_(j=1)^oo |nu(E_j)|,
    $
    where the supremum is taken over all countable partitions $E = union.big_(j=1)^oo E_j$ of $E$ into disjoint measurable sets. 
]

#proposition[
    Let $nu$ be a signed measure on a $sigma$-algebra $cal(M)$. Then $|nu|$ is a measure on $cal(M)$, and for every $E in cal(M)$, we have
    $
    |nu(E)| <= |nu|(E).
    $
]
#proof[
    Clearly $|nu|(emptyset) = 0$. To show countable additivity, let $E_1, E_2, ...$ be a sequence of disjoint sets in $cal(M)$ and $E = union.big_(n=1)^oo E_n$, then it suffices to show that
    $
    sum_(n=1)^oo |nu|(E_n) <= |nu|(E) quad "and" quad |nu|(E) <= sum_(n=1)^oo |nu|(E_n).
    $
    For the first inequality, let $alpha_j$ be a real number such that $alpha_j < |nu|(E_j)$ or $alpha_j = 0$ if $|nu|(E_j) = 0$. Then by definition of total variation, we can find a partition $E_j = union.big_(k=1)^oo E_(j, k)$ such that
    $
    sum_(k=1)^oo |nu(E_(j, k))| >= alpha_j
    $
    for every $j$. Since $E = union.big_(j=1)^oo union.big_(k=1)^oo E_(j, k)$, we have
    $
    |nu|(E) >= sum_(j=1)^oo sum_(k=1)^oo |nu(E_(j, k))| >= sum_(j=1)^oo alpha_j.
    $
    Taking supremum over all $alpha_j$, we have $|nu|(E) >= sum(n=1)^oo |nu|(E_n)$. 

    For the second inequality, let $(F_k)$ be a partition of $E$, then $F_k = union.big_(j=1)^oo (F_k inter E_j)$, so
    $
    sum_(k=1)^oo |nu(F_k)| &= sum_(k=1)^oo abs(nu(union.big_(j=1)^oo (F_k inter E_j))) \
    &<= sum_(k=1)^oo sum_(j=1)^oo abs(nu(F_k inter E_j)) \
    &= sum_(j=1)^oo sum_(k=1)^oo abs(nu(F_k inter E_j)) <= sum_(j=1)^oo |nu|(E_j).
    $
    Taking supremum over all partitions $(F_k)$ of $E$ gives the desired inequality. 
    $qed$
]

#definition[
    Let $nu$ be a signed measure on a $sigma$-algebra $cal(M)$. The positive variation and negative variation are
    $
    nu^+(E) = (|nu|(E) + nu(E))/2,  quad  nu^-(E) = (|nu|(E) - nu(E))/2.
    $
    If $nu(E) = |nu|(E) = oo$, we define $nu^-(E) = 0$. 
]

Since $|nu|$ is a measure, $nu^+$ and $nu^-$ are also measures. Moreover, we have $nu = nu^+ - nu^-$ and $|nu| = nu^+ + nu^-$.

#definition[
    A signed measure $nu$ is $sigma$-finite if $|nu|$ is $sigma$-finite
]

Since $nu <= |nu|$ and $|-nu| = |nu|$, we have
$
-|nu| <= nu <= |nu|.
$
If $nu$ is $sigma$-finite, then so are $nu^+$ and $nu^-$. 

=== Mutual Singularity and Absolute Continuity

#definition[
    + A signed measure $nu$ is supported on a set $A in cal(M)$ if $nu(E) = nu(E inter A)$ for all $E in cal(M)$.
    + Two signed measures $nu$ and $mu$ on $cal(M)$ are mutually singular, denoted by $nu perp mu$, if there exists disjoint sets $A, B in cal(M)$ such that $nu$ is supported on $A$ and $mu$ is supported on $B$. 
    + If $nu$ is a signed measure and $mu$ is a (positive) measure, we say that $nu$ is absolutely continuous with respect to $mu$, denoted by $nu << mu$, if $mu(E) = 0$ implies $nu(E) = 0$ for all $E in cal(M)$.
]

#example[
    - Let $m$ be the Lebesgue measure on $RR$ and $delta_0$ be the Dirac measure at $0$, i.e. $delta_0(E) = 1$ if $0 in E$ and $delta_0(E) = 0$ otherwise. Then $m$ and $delta_0$ are mutually singular, since $delta_0$ is supported on ${0}$ and $m$ is supported on $RR backslash {0}$.
    - Let $f$ be a $mu$-measurable function with $integral f^- d mu < oo$, then the signed measure defined by
    $
    nu(E) = integral_E f d mu
    $
    is absolutely continuous with respect to $mu$, since if $mu(E) = 0$, then $nu(E) = integral_E f d mu = 0$.
]

#proposition[
    If for each $epsilon > 0$ there exists $delta > 0$ such that $|nu(E)| < epsilon$ whenever $mu(E) < delta$, then $nu << mu$. The converse holds when $|nu|$ is a finite measure, i.e. $|nu|(X) < oo$.
]
#proof[
    If $mu(E) = 0$, then for every $epsilon > 0$, we have $|nu(E)| < epsilon$, so $nu(E) = 0$. 

    Conversely, suppose that $nu << mu$ and $|nu|(X) < oo$. By replacing $nu$ with $|nu|$, we may assume that $nu$ is a positive measure. If the conclusion does not hold, then there exists $epsilon > 0$ such that for every $delta > 0$, we can find $E in cal(M)$ such that $mu(E) < delta$ and $nu(E) >= epsilon$. We can then find a sequence of sets $E_1, E_2, ...$ such that $mu(E_n) < 2^(-n)$ and $nu(E_n) >= epsilon$ for every $n$. Let
    $
    E = limsup_(n -> oo) E_n = inter.big_(n=1)^oo union.big_(k=n)^oo E_k,
    $
    then for each $n$, $mu(union.big_(k=n)^oo E_k) < 2^(-n)$, so $mu(E) = 0$. On the other hand, since $nu(E_n) >= epsilon$ for every $n$, we have $nu(union.big_(k=n)^oo E_k) >= epsilon$ for every $n$, so $nu(E) >= epsilon$. This contradicts the assumption that $nu << mu$.
    $qed$
]

#theorem(name: "Radon-Nikodym Theorem")[
    Suppose that $mu$ is a $sigma$-finite positive measure and $nu$ is a $sigma$-finite signed measure on $(X, cal(M))$. Then there exists a unique decomposition $nu = nu_a + nu_s$ into signed measures $nu_a$ and $nu_s$ such that $nu_a << mu$ and $nu_s perp mu$. Moreover, $d nu_a = f d mu$, i.e.
    $
    nu_a (E) = integral_E f d mu
    $
    for some $mu$-measurable function $f$ with $integral f^- d mu < oo$.
]
#proof[
    First consider the case that both $nu$ and $mu$ are positive and finite. Let $lambda = nu + mu$. Define the linear functional $ell: L^2(X, lambda) -> CC$ by
    $
    ell(psi) = integral_X psi d nu.
    $
    Note that
    $
    ell(psi) &<= integral_X |psi| d nu <= integral_X |psi| d lambda \
    &<= (integral_X |psi|^2 d lambda)^(1/2) (integral_X 1^2 d lambda)^(1/2) = |psi|_2 (lambda(X))^(1/2),
    $
    so $ell$ is a bounded linear functional on $L^2(X, lambda)$. By Riesz representation theorem, there exists $g in L^2(X, lambda)$ such that
    $
    ell(psi) = integral_X psi d nu = integral_X psi g d lambda
    $
    for every $psi in L^2(X, lambda)$. 

    Let $E in cal(M)$ with $lambda(E) > 0$, then $0 <= (mu(E)) / (lambda(E)) <= 1$. Consider $psi = chi_E$, then
    $
    ell(E) = mu(E) = integral_E g d lambda ~> 0 <= 1/(lambda(E)) integral_E g d lambda <= 1.
    $
    Since $E$ is arbitrary, we have $0 <= g <= 1$ $lambda$-a.e. Note that
    $
    integral_X psi d nu = integral_X psi g d lambda = integral_X psi g d nu + integral_X psi g d mu,
    $
    so
    $
    integral_X psi (1 - g) d nu = integral_X psi g d mu.
    $ <eq:1>
    Consider the sets
    $
    A = {x in X : 0 <= g(x) < 1},  quad  B = {x in X : g(x) = 1}.
    $
    Define $nu_a$ and $nu_s$ on $cal(M)$ by
    $
    nu_a(E) = nu(E inter A),  quad  nu_s(E) = nu(E inter B).
    $

    #claim[
        $nu_s perp mu$
    ]
    #proof[
        Substituting $psi = chi_B$ into @eq:1, we have
        $
        0 = integral_X chi_B (1 - g) d nu = integral_X chi_B g d mu = mu(B),
        $
        so $nu_s$ is supported on $B$ and $mu$ is supported on $X backslash B$, hence $nu_s perp mu$.
        $qed$
    ]

    #claim[
        $nu_a << mu$ and $nu_a(E) = integral_E f d mu$ for some $mu$-integrable function $f$.
    ]
    #proof[
        Substituting $psi = chi_E (1 + g + dots.c + g^n)$ into @eq:1, we have
        $
        integral_E (1 - g^(n+1)) d nu = integral_E g (1 + g + dots.c + g^n) d mu.
        $
        By dominated convergence theorem the left hand side converges to $integral_E chi_A d nu = nu_a(E)$, and since $1 + g + dots.c + g^n$ converges to $1/(1 - g)$, by monotone convergence theorem, we have
        $
        nu_a(E) = integral_E g/(1 - g) d mu.
        $
        Let $f = g/(1 - g)$, then $f$ is $mu$-integrable since $nu_a(X) <= nu(X) < oo$.
        $qed$
    ]

    If $mu$ and $nu$ are $sigma$-finite and positive, we can write $X = union.big_(j=1)^oo E_j$ with $E_j in cal(M)$ and $nu(E_j), mu(E_j) < oo$ for every $j$. Define positive finite measures on $cal(M)$ by
    $
    nu_j(E) = nu(E inter E_j),  quad  mu_j(E) = mu(E inter E_j).
    $
    By the previous case, we can find decompositions $nu_j = nu_(j, a) + nu_(j, s)$ such that $nu_(j, s) perp mu_j$ and $nu_(j, a) = f_j d mu_j$ for some $mu_j$-integrable function $f_j$. It suffices to set
    $
    nu_a = sum_(j=1)^oo nu_(j, a),  quad  nu_s = sum_(j=1)^oo nu_(j, s) quad "and" quad f = sum_(j=1)^oo f_j. 
    $

    If $nu$ is signed, we can apply the above argument separately to $nu^+$ and $nu^-$. 

    For uniqueness, suppose $nu = nu_a' + nu_s'$ is another decomposition with the same properties, then
    $
    nu_a - nu_a' = nu_s' - nu_s.
    $
    The left hand side is absolutely continuous with respect to $mu$, while the right hand side is singular with respect to $mu$, so both sides must be $0$, hence $nu_a = nu_a'$ and $nu_s = nu_s'$. 
    $qed$
]

#remark[
    The above $f$ is unique up to a $mu$-null set. $f$ is also called the Radon-Nikodym derivative of $nu_a$ with respect to $mu$ and is denoted by $(d nu_a)/(d mu)$.
]

= Fractal Geometry

== Self-similarity

Informally, a set is self-similar if it is the union of several scaled down copies of itself. 

#example[
    - The Cantor set is self-similar, since it is the union of two copies of itself scaled down by a factor of $1/3$.
    - The Sierpinski triangle is self-similar, since it consists of three copies of itself scaled down by a factor of $1/2$.
    - the unit interval $[0, 1]$ is self-similar, since it consists of two copies of itself scaled down by a factor of $1/2$.
]

#definition[
    Let $(X, d)$ be a metric space. A function $phi: X -> X$ is a similitude if there exists $r in (0, 1)$ such that
    $
    d(phi(x), phi(y)) = r d(x, y)
    $
    for every $x, y in X$. 
]
Note that a similitude is a contraction. It's straightforward to verify that $"diam"(phi(A)) = r "diam"(A)$ for every $A subset.eq X$.

#definition[
    A family $(phi_1, ..., phi_n)$ of finitely many contractions is called an iterated function system (IFS). A compact set $K subset.eq X$ is called an attractor of the IFS $(phi_1, ..., phi_n)$ if
    $
    K = union.big_(k=1)^n phi_k(K).
    $
    A set is called self-similar in the wider sense in $X$ if it is the attractor of some IFS on $X$. A set is called self-similar (in the strict sense) if it is the attractor of some IFS in which each $phi_k$ is a similitude.

    If $c_1, dots, c_n$ are the contraction ratios of $phi_1, dots, phi_n$ respectively, then we say that the IFS has contraction ratio $c = max{c_1, dots, c_n}$.
]

#example[
    - $[0, 1]$ is self-similar with similitudes
    $
    phi_1(x) = x/2,  quad  phi_2(x) = x/2 + 1/2.
    $
    - The Cantor set is self-similar with similitudes
    $
    phi_1(x) = x/3,  quad  phi_2(x) = x/3 + 2/3.
    $
    - Every finite set is self-similar in the wider sense, since we can define $phi_k(x) = x_k$ for every $k$, where $x_1, dots, x_n$ are the points in the set. However, a finite set is self-similar in the strict sense if and only if it is a singleton. 
]

=== Coding Theorem

Recall that for the middle-thirds Cantor set, there is a function $pi: {0, 2}^NN -> C$ defined by
$
pi((x_k)) = sum_(k=1)^oo x_k / 3^k,
$
which is a homeomorphism. The following definition generalizes this result to arbitrary attractors. 

#definition[
    Let $sum_n = {1, dots, n}^NN$ be the set of all sequences with values in ${1, dots, n}$, called the code space in $n$ symbols. For any two distinct sequences $(x_k), (y_k) in sum_n$, define
    $
    d_n((x_k), (y_k)) = 2^(-m),  quad  m = min{k : x_k != y_k}.
    $
    Then $d_n$ is a metric on $sum_n$ and makes $sum_n$ a compact metric space. 
]

#theorem(name: "Coding Theorem")[
    Let $K$ be the attractor of an IFS $(phi_1, ..., phi_n)$ on a metric space $(X, d)$. Then there exists a continuous surjective function $pi: sum_n -> K$ defined by
    $
    pi((y_k)) = lim_(k -> oo) phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_k)(x)
    $
    for any $x in K$, such that for all $(y_1, dots, y_k) in {1, dots, n}^k$, 
    $
    pi({(x_k) in sum_n : x_1 = y_1, dots, x_k = y_k}) = phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_k)(K).
    $
    If additionally, all the $phi_k$ are injective and $phi_i(K) inter phi_j(K) = emptyset$ for all $i != j$, then $pi$ is a homeomorphism.
]
#proof[
    Since $K$ is the attractor of the IFS, we have $K = union.big_(i=1)^n phi_i(K)$, so in particular $phi_i(K) subset.eq K$ for every $i$. Let
    $
    K_k = inter.big_(i=1)^k phi_(y_i) compose phi_(y_2) compose dots.c compose phi_(y_k)(K),
    $
    then $K_k$ in a nonempty compact set and $K_k subset.eq K_(k-1)$ for every $k$, so $A := inter.big_(k=1)^oo K_k$ is a nonempty compact set. Also, 
    $
    "diam" (A) <= "diam" (K_k) <= c^k "diam" (K) -> 0
    $ 
    as $k -> oo$, so $A$ is a singleton. Define $pi((y_k))$ to be the unique element in $A$. We first show that $pi$ is surjective. Let $x in K$. Construct a sequence $(y_k)$ inductively as follows: since $x in K = union.big_(i=1)^n phi_i(K)$, there exists $y_1$ such that $x in phi_(y_1)(K)$, let $x_1 in K$ such that $x = phi_(y_1)(x_1)$. Since $x_1 in K = union.big_(i=1)^n phi_i(K)$, there exists $y_2$ such that $x_1 in phi_(y_2)(K)$, let $x_2 in K$ such that $x_1 = phi_(y_2)(x_2)$. Continuing this process, we can find a sequence $(y_k)$ such that
    $
    x in inter.big_(k=1)^oo phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_k)(K),
    $
    so $x = pi((y_k))$.

    Let $(y_1, dots, y_k) in {1, dots, n}^k$. Suppose $x in phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_k)(K)$. Then there exists $tilde(x) in K$ such that $x = phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_k)(tilde(x))$. By the construction above, there exists a sequence $(tilde(x_k))$ such that $tilde(x) = pi((tilde(x_k)))$, then
    $
    pi((y_1, dots, y_k, tilde(x_1), tilde(x_2), dots)) &= inter.big_(m=1)^oo phi_(y_1) compose dots.c compose phi_(y_k) compose phi_(tilde(x_1)) compose dots.c compose phi_(tilde(x_m))(K) \
    &supset.eq phi_(y_1) compose dots.c compose phi_(y_k) compose (inter.big_(m=1)^oo phi_(tilde(x_1)) compose dots.c compose phi_(tilde(x_m))(K)) \
    &= phi_(y_1) compose dots.c compose phi_(y_k)({tilde(x)}) = {x},
    $
    so
    $
    phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_k)(K) subset.eq pi({(x_k) in sum_n : x_1 = y_1, dots, x_k = y_k}).
    $
    Conversely, we have
    $
    & pi({(x_k) in sum_n : x_1 = y_1, dots, x_k = y_k}) \
    subset.eq & union.big_(x_1 = y_1, dots, x_k = y_k) inter.big_(m=1)^oo phi_(x_1) compose dots.c compose phi_(x_m)((x_k)) \
    subset.eq & phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_k)(K).
    $

    Next, we show that $pi$ is uniformly continuous. Let $epsilon > 0$. Fix $m$ large such that $c^m "diam"(K) < epsilon$. Then for any $(x_k), (y_k) in sum_n$ with $d_n((x_k), (y_k)) < 2^(-m)$, we have $x_i = y_i$ for all $1 <= i <= m$, so by the previous result, 
    $
    pi((x_k)), pi((y_k)) in phi_(x_1) compose phi_(x_2) compose dots.c compose phi_(x_m)(K),
    $
    so $d(pi((x_k)), pi((y_k))) <= c^m "diam"(K) < epsilon$.

    Finally, assume that all the $phi_k$ are injective and the images $phi_i(K)$ are pairwise disjoint. We will show that $pi$ is injective, then by compactness of $sum_n$ and Hausdorffness of $X$, $pi$ is a homeomorphism. Suppose that $(x_k), (y_k) in sum_n$ are distinct, then there exists a minimal $j >= 1$ such that $x_j != y_j$, then by disjointness of $phi_i(K)$, we have
    $
    phi_(x_1) compose phi_(x_2) compose dots.c compose phi_(x_(j))(K) inter phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_(j))(K) = emptyset.
    $
    Since $pi((x_k)) in phi_(x_1) compose phi_(x_2) compose dots.c compose phi_(x_(j))(K)$ and $pi((y_k)) in phi_(y_1) compose phi_(y_2) compose dots.c compose phi_(y_(j))(K)$, we have $pi((x_k)) != pi((y_k))$, so $pi$ is injective.
    $qed$
]

The elements in $sum_n$ can be thought of as "addresses" of points in $K$. The coding theorem says that every point in $K$ has at least one address, and the set of points with a given prefix in their addresses is exactly the image of $K$ under the corresponding composition of the $phi_k$. If the $phi_k$ are injective and their images are disjoint, then every point in $K$ has a unique address, and the coding map is a homeomorphism.

== Hausdorff Metric

Let $cal(K)$ be the set of all nonempty compact subsets of $X$. We can define a metric on $cal(K)$, called the Hausdorff metric, which measures how far two compact sets are from each other. Moreover, if $X$ is complete, then so is $(cal(K), cal(D))$. This allows us to apply the Banach fixed point theorem to show the existence and uniqueness of attractors of IFS.

#definition[
    Let $(X, d)$ be a metric space. If $K$ is a nonempty compact subset of $X$ and $delta > 0$, we define
    $
    K[delta] = {x in X : exists y in K "such that" d(x, y) <= delta}.
    $
    For $K, L in cal(K)$, we define their Hausdorff distance by
    $
    cal(D) = inf {delta > 0 : K subset.eq L[delta] "and" L subset.eq K[delta]}.
    $
]

#lemma[
    $cal(D)$ defines a metric on $cal(K)$, called the Hausdorff metric. Moreover, if $X$ is complete, then so is $(cal(K), cal(D))$.
]
#proof[
    Clearly $cal(D)$ is nonnegative and symmetric. Suppose that $cal(D)(K, L) = 0$, then $L subset.eq K[delta]$ for all $delta > 0$. Since $K$ is closed, $inter.big_(delta > 0) K[delta] = K$, hence $L subset.eq K$. By symmetry, we also have $K subset.eq L$, so $K = L$. Triangle inequality follows from the fact that if $K subset.eq L[delta_1]$ and $L subset.eq M[delta_2]$, then $K subset.eq M[delta_1 + delta_2]$.

    Let $(K_n)$ be a Cauchy sequence in $(cal(K), cal(D))$. By passing to a subsequence if necessary, we can assume that $cal(D)(K_m, K_n) < 2^(-n)$ for every $m >= n$. Define
    $
    K = inter.big_(n=1)^oo overline(union.big_(m=n)^oo K_m).
    $
    Clearly $overline(union.big_{m=n}^oo K_m)$ is nonempty and closed, and
    $
    overline(union.big_(m=n)^oo K_m) subset.eq K_n[2^(-n)]
    $
    for every $n$, so $overline(union.big_(m=n)^oo K_m)$ is a nonempty compact set, implying that $K$ is a nonempty compact set. From the above inclusion, we have $K subset.eq K_n [2^(-n)]$ for every $n$. On the other hand, given $x in K_n$, for all $m >= n$, there exists $y_m in K_m$ such that $d(x, y_m) < 2^(-n)$. Since $(y_m)$ is contained in a compact set, there exists a convergent subsequence with limit $y in X$, then $y in union.big_(i=m)^oo K_i$ for all $m >= n$, so $y in K$ and $d(x, y) <= 2^(-n)$. This shows that $K_n subset.eq K[2^(-n)]$ for every $n$, so $cal(D)(K_n, K) <= 2^(-n)$ for every $n$, hence $K_n -> K$ in $(cal(K), cal(D))$. 
    $qed$
]

#theorem[
    Let $(phi_1, dots, phi_k)$ be an IFS on a nonempty closed subset $X subset.eq RR^d$, then there exists a unique nonempty compact set $K subset.eq X$ such that $K$ is the attractor of the IFS.
]
#proof[
    Define the map $Phi: cal(K) -> cal(K)$ by
    $
    Phi(K) = union.big_(k=1)^n phi_k(K).
    $
    For $A, B in cal(K)$, we have
    $
    cal(D)(Phi(A), Phi(B)) &= cal(D)(union.big_(k=1)^n phi_k(A), union.big_(k=1)^n phi_k(B)) \
    &<= max_(1 <= k <= n) cal(D)(phi_k(A), phi_k(B)) <= c dot cal(D)(A, B),
    $
    so $Phi$ is a contraction on $(cal(K), cal(D))$. By Banach fixed point theorem, there exists a unique $K in cal(K)$ such that $Phi(K) = K$, i.e. $K$ is the attractor of the IFS.
    $qed$
]

Banach fixed point theorem also tells us that starting from any nonempty compact set $A subset.eq X$, the sequence defined by $A_1 = A$ and $A_(n+1) = Phi(A_n)$ converges to $K$ in the Hausdorff metric. 

=== Self-similar Measures

#definition[
    A vector $(p_1, dots, p_n) in RR^n$ is called a probability vector if its entries are nonnegative and $sum_(i=1)^n p_i = 1$.
]

#theorem(id: "thm:self_similar_measures")[
    Let $phi = (phi_1, dots, phi_n)$ be an IFS on a nonempty closed subset $X subset.eq RR^d$ with attractor $K subset.eq X$. Let $p = (p_1, dots, p_n)$ be a probability vector. Then there exists a unique Borel probability measure $mu$ on $K$ such that
    $
    mu = sum_(k=1)^n p_k dot mu compose phi_k^(-1).
    $
    This measure is called the self-similar measure associated to $p$ and $phi$. Moreover, we have
    $
    mu(phi_(y_1) compose dots.c compose phi_(y_k)(K)) >= product_(i=1)^k p_(y_i). 
    $
    If additionally, all the $phi_k$ are injective and $phi_i(K) inter phi_j(K) = emptyset$ for all $i != j$, then the above inequality is an equality. If all $p_i > 0$, then the support of $mu$ is $K$.
]
#proof[
    Let $cal(M)$ be the set of all Borel probability measure on $K$. Define the map $Phi: cal(M) -> cal(M)$ by
    $
    Phi(nu) = sum_(k=1)^n p_k dot nu compose phi_k^(-1).
    $
    Define
    $
    cal(D)(nu_1, nu_2) = sup {|integral f d nu_1 - integral f d nu_2| : f: K -> RR "is 1-Lipschitz"}, 
    $
    then $cal(D)$ is a metric on $cal(M)$ and $(cal(M), cal(D))$ is complete. Note that
    $
    integral g thin d Phi(nu) = sum_(k=1)^n p_k dot integral g thin d (nu compose phi_k^(-1)) = sum_(k=1)^n p_k dot integral g compose phi_k d nu, 
    $
    and also since
    $
    |g compose phi_k(x) - g compose phi_k(y)| <= d(phi_k(x), phi_k(y)) <= c dot d(x, y)
    $
    so $c^(-1) dot g compose phi_k$ is a 1-Lipschitz function, hence
    $
    & cal(D)(Phi(nu_1), Phi(nu_2)) \
    =& sup {abs(integral g d Phi(nu_1) - integral g d Phi(nu_2)) : g "is 1-Lipschitz"} \
    =& sup {abs(sum_(k=1)^n p_k dot (integral g compose phi_k d nu_1 - integral g compose phi_k d nu_2)) : g "is 1-Lipschitz"} \
    <=& sum_(k=1)^n p_k dot sup {abs(integral g compose phi_k d nu_1 - integral g compose phi_k d nu_2) : g "is 1-Lipschitz"} \
    =& c dot sum_(k=1)^n p_k dot sup {abs(integral c^(-1) dot g compose phi_k d nu_1 - integral c^(-1) dot g compose phi_k d nu_2) : g "is 1-Lipschitz"} \
    <=& c dot sum_(k=1)^n p_k dot cal(D)(nu_1, nu_2) = c dot cal(D)(nu_1, nu_2),
    $
    so $Phi$ is a contraction on $(cal(M), cal(D))$. By Banach fixed point theorem, there exists a unique $mu in cal(M)$ such that $Phi(mu) = mu$, i.e. $mu$ is the self-similar measure associated to $p$ and $phi$.

    Let $(y_k) in sum_n$, then
    $
    mu(phi_(y_1) compose dots.c compose phi_(y_k)(K)) &= sum_(i=1)^n p_i dot mu(phi_i^(-1) compose phi_(y_1) compose dots.c compose phi_(y_k)(K)) \
    &>= p_(y_1) dot mu(phi_(y_2) compose dots.c compose phi_(y_k)(K)) >= dots.c >= product_(i=1)^k p_(y_i).
    $
    If all the $phi_k$ are injective and their images are disjoint, then since the total measure of $K$ is $1$, we must have equality in the above inequality. If all $p_i > 0$, then $mu(phi_(y_1) compose dots.c compose phi_(y_k)(K)) > 0$ for every $(y_k) in sum_n$. Let $cal(U) subset.eq X$ be open and $K inter cal(U) != emptyset$, then $cal(U)$ must contain some $phi_(y_1) compose dots.c compose phi_(y_k)(K)$ for sufficiently large $k$, so $mu(cal(U)) > 0$. Since every open set intersecting $K$ has positive $mu$-measure, the support of $mu$ is $K$.
    $qed$
]

== Dimensions

For a $n$-dimensional cube with side length $1$, observe that it consists of $2^n$ smaller cubes of side length $1/2$. More generally, this notion of dimension can be extended to self-similar sets. For example, the middle-thirds Cantor set consists of two copies of itself scaled down by a factor of $1/3$, so we can think of it as a "fractal" with dimension $log_3(2)$. The Sierpinski triangle consists of three copies of itself scaled down by a factor of $1/2$, so we can think of it as a "fractal" with dimension $log_2(3)$.

However, the above definition of dimension only applies to self-similar sets with certain properties. To define a more general notion of dimension that applies to arbitrary subsets of $RR^d$, we need to use the concept of Hausdorff measure.

=== Minkowski Dimension

Suppose that $E$ is a bounded metric space with metric $d$. For $epsilon > 0$, define
$
M(E, epsilon) = min {k : exists x_1, dots, x_k in 
E "such that" E subset.eq union.big_(i=1)^k B(x_i, epsilon)}.
$

#definition[
    Let $E$ be a bounded metric space. The lower and upper Minkowski dimensions of $E$ are defined by
    $
    underline(dim)_M (E) = liminf_(epsilon -> 0) (log M(E, epsilon)) / (-log epsilon),  quad  overline(dim)_M (E) = limsup_(epsilon -> 0) (log M(E, epsilon)) / (-log epsilon).
    $
    If the lower and upper dimensions coincide, we define the Minkowski dimension of $E$ to be their common value, denoted by $dim_M (E)$.
]

#proposition[
    The Minkowski dimension of the middle-thirds Cantor set is $log_3(2)$.
]
#proof[
    To upper bound the Minkowski dimension of $C$, we only need to find an efficient cover of $C$. Let $epsilon in (0, 1)$, and choose $n$ such that $3^(-n) < epsilon <= 3^(-(n-1))$. Consider the sets
    $
    [sum_(i=1)^n x_i / 3^i, sum_(i=1)^n x_i / 3^i + epsilon] quad "for" (x_1, dots, x_n) in {0, 2}^n,
    $
    then these $2^n$ sets cover $C$, so
    $
    M(C, epsilon) <= 2^n = 3^(n log_3(2)) < 3^(log_3(2) - log_3(epsilon)) = epsilon^(-log_3(2)),
    $
    hence $overline(dim)_M (C) <= log_3(2)$.

    For the lower bound, assume that we have a cover by open balls $B(x_k, epsilon)$ where $epsilon in (0, 1)$. Let $n$ be the integer such that $3^(-(n+1)) <= epsilon < 3^(-n)$. Write
    $
    x_k = sum_(i=1)^oo x_(i, k) / 3^i
    $
    for the ternary expansion of $x_k$. Note that
    $
    B(x_k, epsilon) inter C subset.eq {sum_(i=1)^n x_(i, k) / 3^i + sum_(i=n+1)^oo y_i / 3^i : y_i in {0, 2} "for every" i}
    $
    for every $k$, so we need at least $2^n$ such balls to cover $C$, hence
    $
    M(C, epsilon) >= 2^n = 3^(n log_3(2)) = 3^(-log_3(2)) dot 3^((n+1) log_3(2)) >= 3^(-log_3(2)) dot epsilon^(-log_3(2)),
    $
    so $underline(dim)_M (C) >= log_3(2)$.
    $qed$
]

However, the Minkowski dimension has some drawbacks. For example, it is not stable under countable unions. 

#proposition[
    Let $E = {1/n : n in NN} union {0} subset.eq RR$, then $dim_M (E) = 1/2$. 
]
#proof[
    Let $epsilon in (0, 1)$. Choose $n$ such that $1/(n+1)^2 <= epsilon < 1/n^2$. The tail ${1/k: k > n} union {0}$ can be covered by $n+1$ balls of radius $epsilon$ since $(n+1)epsilon >= 1/(n+1)$, and the remaining $n$ points can be covered by $n$ balls of radius $epsilon$, so
    $
    M(E, epsilon) <= 2n + 1 <= (2n + 1)/n dot epsilon^(-1/2), 
    $
    hence $overline(dim)_M (E) <= 1/2$. On the other hand, the distance between two neighboring points is
    $
    1/k - 1/(k+1) = 1/(k(k+1)) >= 1/(k+1)^2, 
    $
    so we need at least $n$ balls of radius $epsilon$ to cover the $n$ points $1, 1/2, dots, 1/n$, hence
    $
    M(E, epsilon) >= n >= n/(n+1) dot epsilon^(-1/2),
    $
    so $underline(dim)_M (E) >= 1/2$.
    $qed$
]

Define
$
M^s (E) = inf {k epsilon^s : B(x_1, epsilon), dots , B(x_k, epsilon) "is a cover of" E},
$

#proposition[
    $
    underline(dim)_M (E) = inf {s >= 0 : M^s (E) = 0} = sup {s >= 0 : M^s (E) > 0}.
    $
]
#proof[
    Suppose that $underline(dim)_M (E) < s$, then for all $eta in (underline(dim)_M (E), s)$, exists arbitrarily small $epsilon > 0$ and a cover by $k$ balls of radius $epsilon$ with $k <= epsilon^(-eta)$. Hence
    $
    M^s (E) <= k epsilon^s <= epsilon^(s - eta) -> 0
    $
    as $epsilon -> 0$, so $M^s (E) = 0$. 

    On the other hand, if $underline(dim)_M (E) > s$, then for all $eta in (s, underline(dim)_M (E))$ and all sufficiently small $epsilon$, every cover of balls of radius $epsilon$ has at least $k >= epsilon^(-eta)$ balls, so
    $
    M^s (E) >= k epsilon^s >= epsilon^(s - eta) -> oo
    $
    as $epsilon -> 0$, so $M^s (E) = oo$. 

    If $underline(dim)_M (E) = t$, then $M^s (E) = 0$ for all $s > t$ and $M^s (E) = oo$ for all $s < t$, so the above equalities hold.
    $qed$
]

=== Hausdorff Dimension

We extend the definition of Minkowski dimension by allowing more general covers, specifically, balls of varying radii.

Let $B(x_k, r_k)$ be a cover of $E$ by open balls, then we define the $s$-value of the cover by $sum_k r_k^s$. 

#definition[
    For every $alpha >= 0$, the (spherical) $alpha$-Hausdorff content of a metric space $E$ is defined by
    $
    cal(C)^alpha (E) = inf {sum_k r_k^alpha : B(x_k, r_k) "is a cover of" E}.
    $
]

#definition[
    For a metric space $E$, define the Hausdorff dimension of $E$ by
    $
    dim_H (E) = inf {alpha >= 0 : cal(C)^alpha (E) = 0} = sup {alpha >= 0 : cal(C)^alpha (E) > 0}.
    $
]

From the definition, we can see that the Hausdorff dimension of a set is always less than or equal to its Minkowski dimension. 

#lemma[
    Hausdorff dimension is stable under countable unions, i.e. for every sequence of sets $(E_n)$, we have
    $
    dim_H (union.big_(n=1)^oo E_n) = sup_(n >= 1) dim_H (E_n).
    $
]
#proof[
    Clearly Hausdorff dimension is monotone, so
    $
    dim_H (union.big_(n=1)^oo E_n) >= sup_(n >= 1) dim_H (E_n).
    $
    
    For $alpha >= 0$, 
    $
    cal(C)^alpha (union.big_(n=1)^oo E_n) &<= inf {sum_(k=1)^oo sum_j r_(j, k)^alpha : B(x_(j, k), r_(j, k)) "is a cover of" E_k} \
    &= sum_(k=1)^oo inf {sum_j r_(j, k)^alpha : B(x_(j, k), r_(j, k)) "is a cover of" E_k} = sum_(k=1)^oo cal(C)^alpha (E_k),
    $
    hence
    $
    dim_H (union.big_(n=1)^oo E_n) &= sup {alpha >= 0 : cal(C)^alpha (union.big_(n=1)^oo E_n) > 0} \
    &<= sup {alpha >= 0 : sum_(k=1)^oo cal(C)^alpha (E_k) > 0} \
    &= sup_(n >= 1) sup {alpha >= 0 : cal(C)^alpha (E_n) > 0} \
    &= sup_(n >= 1) dim_H (E_n). 
    $
    $qed$
]

#definition[
    Let $X$ be a metric space and $E subset.eq X$. For each $alpha >= 0$ and $delta > 0$, we define
    $
    cal(H)^alpha_delta (E) = inf {sum_(k=1)^oo "diam"(F_k)^alpha : E subset.eq union.big_(k=1)^oo F_k "and" "diam"(F_k) <= delta},
    $
    and the outer $alpha$-Hausdorff measure of $E$ by
    $
    cal(H)_*^alpha (E) = sup_(delta > 0) cal(H)^alpha_delta (E) = lim_(delta -> 0) cal(H)^alpha_delta (E) in [0, oo]. 
    $
]

Clearly $cal(H)_*^alpha$ is monotone and countably subadditive. 

#proposition[
    For $E_1, E_2 subset.eq X$, if $d(E_1, E_2) > 0$, then
    $
    cal(H)_*^alpha (E_1 union E_2) = cal(H)_*^alpha (E_1) + cal(H)_*^alpha (E_2).
    $
]
#proof[
    It suffices to show that $cal(H)_*^alpha (E_1 union E_2) >= cal(H)_*^alpha (E_1) + cal(H)_*^alpha (E_2)$, since the opposite inequality follows from subadditivity. Let $epsilon in (0, d(E_1, E_2))$. Let $delta in (0, epsilon)$, and let $F_k$ be a cover of $E_1 union E_2$ with $"diam"(F_k) <= delta$ for every $k$. Set $F_k' = F_k inter E_1$ and $F_k'' = F_k inter E_2$, then $(F_k')_{k=1}^oo$ is a cover of $E_1$ and $(F_k'')_{k=1}^oo$ is a cover of $E_2$. Moreover, the sets $F_k'$ and $F_k''$ are disjoint since $d(E_1, E_2) > epsilon > delta >= "diam"(F_k)$ for every $k$, so
    $
    sum_(k=1)^oo "diam"(F_k)^alpha >= sum_(k=1)^oo "diam"(F_k')^alpha + sum_(k=1)^oo "diam"(F_k'')^alpha. 
    $
    Taking infimum over all such covers and letting $delta -> 0$, we have
    $
    cal(H)_*^alpha (E_1 union E_2) >= cal(H)_*^alpha (E_1) + cal(H)_*^alpha (E_2).
    $
    $qed$
]

The above implies that $cal(H)_*^alpha$ is countably additive on Borel sets, hence defines a Borel measure on $X$. Write $cal(H)^alpha (E) = cal(H)_*^alpha (E)$ when $E$ is a Borel set, then $cal(H)^alpha$ is called the $alpha$-dimensional Hausdorff measure on $X$.

#proposition[
    - $cal(H)^alpha (E + h) = cal(H)^alpha (E)$ for every $E subset.eq RR^d$ and $h in RR^d$.
    - $cal(H)^alpha (O E) = cal(H)^alpha (E)$ for every $E subset.eq RR^d$ and orthogonal transformation $O$ on $RR^d$.
    - $cal(H)^alpha (lambda E) = lambda^alpha cal(H)^alpha (E)$ for every $E subset.eq RR^d$ and $lambda > 0$.
    - $cal(H)^0 (E)$ is the counting measure on $X$. 
    - $cal(H)^1 (RR)$ is the Lebesgue measure on $RR$.
    - If $alpha$ is an integer and if $E$ is an embedded $alpha$-dimensional submanifold, then $cal(H)^alpha (E)$ equals the $alpha$-dimensional volume of $E$ up to a constant factor. 
]

#proposition[
    If $cal(H)^alpha (E) < oo$ for some $alpha >= 0$, then $cal(H)^beta (E) = 0$ for every $beta > alpha$. If $cal(H)^alpha (E) > 0$ for some $alpha >= 0$, then $cal(H)^beta (E) = oo$ for every $beta < alpha$.
]
#proof[
    Suppose that $cal(H)^alpha (E) < oo$ for some $alpha >= 0$. Let $beta > alpha$. If $"diam"(F) <= delta$, then
    $
    "diam"(F)^beta = "diam"(F)^(beta - alpha) dot "diam"(F)^alpha <= delta^(beta - alpha) dot "diam"(F)^alpha,
    $
    so
    $
    cal(H)^beta_delta (E) <= delta^(beta - alpha) dot cal(H)^alpha_delta (E) <= delta^(beta - alpha) dot cal(H)^alpha (E). 
    $
    Letting $delta -> 0$, we have $cal(H)^beta (E) = 0$.

    The second statement is just the contrapositive of the first statement, so we are done.
    $qed$
]

#proposition[
    If $E$ is a metric space, then
    $
    dim_H (E) &= inf {alpha >= 0 : cal(H)^alpha (E) = 0} = inf {alpha >= 0 : cal(H)^alpha (E) < oo} \
    &= sup {alpha >= 0 : cal(H)^alpha (E) > 0} = sup {alpha >= 0 : cal(H)^alpha (E) = oo}.
    $
]
#proof[
    By the previous proposition, we only need to prove the first equality. Suppose that $dim_H (E) = sup {alpha >= 0 : cal(C)^alpha (E) > 0} > alpha$, then for all $beta <= alpha$, we have $cal(C)^beta (E) > 0$, hence
    $
    cal(H)^beta_delta (E) >= cal(C)^beta (E) > 0
    $
    for every $delta > 0$, so $cal(H)^beta (E) >= cal(C)^beta (E) > 0$ for every $beta <= alpha$, hence $inf {alpha >= 0 : cal(H)^alpha (E) = 0} >= alpha$. On the other hand, suppose that $dim_H (E) = inf {alpha >= 0 : cal(H)^alpha (E) = 0} < alpha$, then $cal(C)^alpha (E) = 0$. For all $delta > 0$, exists a cover of $E$ by sets $E_1, E_2, dots$ with $sum_k "diam"(E_k)^alpha < delta$, so $"diam"(E_k) < delta^(1/alpha)$ for every $k$, hence $cal(H)^alpha_(delta^(1/alpha)) (E) <= delta$
    for every $delta > 0$. Taking $delta -> 0$, we have $cal(H)^alpha (E) = 0$, so $inf {alpha >= 0 : cal(H)^alpha (E) = 0} <= alpha$.
    $qed$
]

=== Packing Dimension

For a metric space $E$, we define
$
dim_P (E) = inf {sup_(n >= 1) overline(dim)_M (E_n) : E = union.big_(n=1)^oo E_n "and each" E_n "is bounded"}.
$
If $E$ is bounded, then we can just take $E_1 = E$ and $E_n = emptyset$ for $n > 1$, so $dim_P (E) <= overline(dim)_M (E)$. 

#proposition[
    For every metric space $E$, we have
    $
    dim_P (E) >= dim_H (E).
    $
]
#proof[
    For each decomposition $E = union.big_(n=1)^oo E_n$ with each $E_n$ bounded, we have
    $
    sup_(n >= 1) overline(dim)_M (E_n) >= sup_(n >= 1) dim_H (E_n) = dim_H (E),
    $
    where the last equality follows from the countable stability of Hausdorff dimension. Taking infimum over all such decompositions, we have $dim_P (E) >= dim_H (E)$.
    $qed$
]

#definition[
    For all $delta > 0$, a $delta$-packing of $A subset.eq E$ is a countable collection of disjoint balls $B(x_k, r_k)$ with $x_k in A$ and $r_k <= delta$ for every $k$. For $s >= 0$, we define the $s$-value of the packing by $sum_k r_k^s$. The $alpha$-packing number of $A$ is defined by
    $
    P^alpha (A) = lim_(delta -> 0) P^alpha_delta (A), 
    $
    where
    $
    P^alpha_delta (A) = sup {sum_k r_k^alpha : B(x_k, r_k) "is a "delta"-packing of" A}.
    $
]

Since $P^alpha$ is not a measure, we modify it to obtain the packing measure
$
cal(P)^alpha (A) = inf {sum_k P^alpha (A_k) : A = union.big_(k=1)^oo A_k}.
$

#theorem[
    For every metric space $E$, we have
    $
    dim_P (E) &= inf {alpha >= 0 : cal(P)^alpha (E) = 0} = inf {alpha >= 0 : cal(P)^alpha (E) < oo} \
    &= sup {alpha >= 0 : cal(P)^alpha (E) > 0} = sup {alpha >= 0 : cal(P)^alpha (E) = oo}.
    $
]
#proof[
    Again, we only show the first equality. Recall that
    $
    M(E, epsilon) = min {k : exists x_1, dots, x_k in E "such that" E subset.eq union.big_(i=1)^k B(x_i, epsilon)}.
    $
    Analogously, for each $A subset E$, define
    $
    P(A, epsilon) = max {k : exists x_1, dots, x_k in A "such that" B(x_i, epsilon) "are disjoint for every" i}.
    $
    We claim that
    $
    P(A, 4epsilon) <= M(A, 2epsilon) <= P(A, epsilon).
    $
    If $k = P(A, epsilon)$, then there exist $x_1, dots, x_k in A$ such that $B(x_i, epsilon)$ are disjoint for every $i$. Suppose that $exists x in A$ such that $x in.not union.big_(i=1)^k B(x_i, 2epsilon)$, then $d(x, x_i) > 2epsilon$ for every $i$, so $B(x, epsilon)$ is disjoint from every $B(x_i, epsilon)$, contradicting the maximality of $k$. Hence $A subset.eq union.big_(i=1)^k B(x_i, 2epsilon)$, so $M(A, 2epsilon) <= k = P(A, epsilon)$.

    For the other inequality, let $m = M(A, 2epsilon)$ and $k = P(A, 4epsilon)$. Choose $x_1, dots, x_m in A$ and $y_1, dots, y_k in A$ such that $A subset.eq union.big_(i=1)^m B(x_i, 2epsilon)$ and $B(y_j, 4epsilon)$ are disjoint for every $j$. Each $y_j$ belongs to some $B(x_i, 2epsilon)$, but since $d(y_j, y_{j'}) > 4epsilon$ for every $j != j'$, each $B(x_i, 2epsilon)$ can contain at most one $y_j$, so $k <= m$.
    
    Suppose that $inf {alpha >= 0 : cal(P)^alpha (E) = 0} < beta$, then $exists alpha < beta$ and $E = union.big_(n=1)^oo A_n$ such that $P^alpha (A_n) < 1$ for every $n$. Note that
    $
    P_epsilon^alpha (A_i) >= P(A_i, epsilon) dot epsilon^alpha
    $
    for all $epsilon > 0$, so
    $
    lim_(epsilon -> 0) M(A_i, epsilon) dot epsilon^alpha <= lim_(epsilon -> 0) P(A_i, epsilon/2) dot epsilon^alpha <= 2^alpha dot P^alpha (A_i) < 2^alpha < oo
    $
    hence
    $
    overline(dim)_M (A_i) = limsup_(epsilon -> 0) (log M(A_i, epsilon)) / (-log epsilon) <= alpha < beta, 
    $
    so $dim_P (E) <= overline(dim)_M (A_i) < beta$.

    For the other side, let
    $
    0 < alpha < beta < inf {gamma: cal(P)^gamma (E) = 0}.
    $
    Let $A_i subset.eq E$ be bounded with $E = union.big_(i=1)^oo A_i$. It suffices to show that $overline(dim)_M (A_i) >= alpha$ for some $i$. 

    Just like in Hausdorff dimension, we can show that $cal(P)^beta (E) > 0$, so $sum_i P^beta (A_i) = cal(P)^beta (E) > 0$, hence $P^beta (A_i) > 0$ for some $i$. Pick some $s in (0, P^beta (A_i))$ such that $P^beta_delta (A_i) > s$ for all sufficiently small $delta$. For each such $delta$, there exists a $delta$-packing of $A_i$ by balls $B(x_i, r_i)$ with $sum_i r_i^beta >= s$. For each $m$, let $k_m$ be the number of indices $i$ such that $r_i in (2^(-m-1), 2^(-m)]$, then
    $
    sum_(m=0)^oo k_m dot 2^(-m beta) >= sum_i r_i^beta >= s. 
    $
    Note that
    $
    sum_(m=0)^oo 2^(m alpha) (1 - 2^(alpha - beta)) 2^(-m beta) = 1, 
    $
    so there must exist some $N$ such that $k_N >= 2^(N alpha) (1 - 2^(alpha - beta)) s$. Since $r_j <= delta$ for all $j$, we have $2^(-N-1) < delta$. Moreover, 
    $
    sup_(0 <= epsilon <= delta) P(A_i, epsilon) epsilon^alpha &>= P(A_i, 2^(-N-1)) dot 2^(-(N+1) alpha) \
    &>= k_N dot 2^(-(N+1) alpha) >= 2^(-alpha) (1 - 2^(alpha - beta)) s > 0. 
    $
    Letting $delta -> 0$, we have
    $
    limsup_(delta -> 0) M(A_i, epsilon) dot epsilon^alpha >= limsup_(delta -> 0) P(A_i, epsilon/2) dot epsilon^alpha > 0,
    $
    so $overline(dim)_M (A_i) >= alpha$.
    $qed$
]

=== Hausdorff Dimension of Self-similar Sets

A Borel measure $mu$ on a metric space $E$ is called a mass distribution on $E$ if $0 < mu(E) < oo$.

#theorem(id: "thm:mass_distribution", name: "Mass distribution principle")[
    Suppose that $E$ is a metric space and $alpha >= 0$. If there exists a mass distribution $mu$ on $E$ and constants $C, delta > 0$ such that
    $
    mu(cal(U)) <= C dot "diam"(cal(U))^alpha
    $
    for all closed $cal(U)$ with $0 < "diam"(cal(U)) <= delta$, then
    $
    cal(H)^alpha (E) >= mu(E) / C > 0,
    $
    hence $dim_H (E) >= alpha$.
]
#proof[
    Suppose that $(cal(U_i))$ is a cover of $E$ with $"diam"(cal(U_i)) <= delta$ for all $i$. Set $V_i = overline(cal(U_i))$, then $V_i$ is closed and $"diam"(V_i) = "diam"(cal(U_i)) <= delta$. Moreover, $E subset.eq union.big_i V_i$, so
    $
    0 < mu(E) <= sum_i mu(V_i) <= C dot sum_i "diam"(V_i)^alpha = C dot sum_i "diam"(cal(U_i))^alpha.
    $
    Taking infimum over all such covers, we have $cal(H)^alpha (E) >= cal(H)^alpha_delta (E) >= mu(E) / C > 0$.
    $qed$
]

#remark[
    - The mass distribution principle is a powerful tool for proving lower bounds on the Hausdorff dimension of a set in combination with self-similar measures. 
    - The converse of the mass distribution principle is called the Frostman's lemma: Suppose that $E$ is a complete separable metric space and $cal(H)^alpha (E) > 0$, then there exists a mass distribution $mu$ on $E$ such that $mu(B) <= "diam"(B)^alpha$ for every bounded Borel set $B subset.eq E$. The difficulty of this lemma is that if $cal(H)^alpha (E) = oo$, then we need to find some subset $A$ with $0 < cal(H)^alpha (A) < oo$ and construct the measure on $A$ instead of $E$.
]

#proposition[
    Let $(phi_1, dots, phi_n)$ be an IFS on a nonempty closed subset $X subset.eq RR^d$ with contraction ratios $(c_1, dots, c_n)$. Then $exists ! alpha >= 0$ such that
    $
    sum_(i=1)^n c_i^alpha = 1.
    $
    If $K$ is the attractor of the IFS, then $cal(H)^alpha (K) < "diam"(K)^alpha$, hence $dim_H (K) <= alpha$. 
]
#proof[
    The function $f: [0, oo) -> RR$ defined by $f(x) = sum_(i=1)^n c_i^x$ is continuous and strictly decreasing, with $f(0) = n > 1$ and $lim_(x -> oo) f(x) = 0$, so there exists a unique $alpha >= 0$ such that $f(alpha) = 1$. Recall that
    $
    K = union.big_(i=1)^n phi_i(K),
    $
    so by induction, 
    $
    K = union.big_((x_1, dots, x_k) in {1, dots, n}^k) phi_(x_1) compose dots.c compose phi_(x_k)(K). 
    $
    Let $c = max_{1 <= i <= n} c_i < 1$, then
    $
    "diam"(phi_(x_1) compose dots.c compose phi_(x_k)(K)) <= c^k dot "diam"(K). 
    $
    Let $delta > 0$ and choose $k$ such that $c^k dot "diam"(K) <= delta$, then
    $
    {phi_(x_1) compose dots.c compose phi_(x_k)(K) : (x_1, dots, x_k) in {1, dots, n}^k}
    $
    is a cover of $K$ by sets of diameter at most $delta$, and
    $
    sum_(x_1, dots, x_k) "diam"(phi_(x_1) compose dots.c compose phi_(x_k)(K))^alpha &<= sum_(x_1, dots, x_k) c_(x_1)^alpha dot dots.c dot c_(x_k)^alpha dot "diam"(K)^alpha \
    &= (sum_(i=1)^n c_(x_1)^alpha) dots (sum_(i=1)^n c_(x_k)^alpha) dot "diam"(K)^alpha \
    &= "diam"(K)^alpha < oo,
    $
    so $cal(H)^alpha_delta (K) < "diam"(K)^alpha$ for every $delta > 0$. Letting $delta -> 0$, we have $cal(H)^alpha (K) <= "diam"(K)^alpha < oo$, so $dim_H (K) <= alpha$.
    $qed$
]

#definition[
    We say that an IFS $(phi_1, dots, phi_n)$ consisting of similitudes satisfies the open set condition if there exists a nonempty bounded open set $cal(U) subset.eq RR^d$ such that $phi_i (cal(U)) subset.eq cal(U)$ for every $i$ and $phi_i (cal(U)) inter phi_j (cal(U)) = emptyset$ for every $i != j$.
]

An IFS such that $phi_i (K) inter phi_j (K) = emptyset$ for every $i != j$ is said to satisfy the strong separation condition, which implies the open set condition by taking an open $epsilon$-neighborhood of $K$ as the open set.

#lemma[
    Let $(V_i)$ be a collection of pairwise disjoint open subsets of $RR^d$ such that each $V_i$ contains a ball of radius $a_1 r$ and is contained in a ball of radius $a_2 r$. Then any ball of radius $r$ intersects with at most $(1 + 2a_2)^d a_1^(-d)$ of the closures of $V_i$.
]
#proof[
    Let $B = B(x, r)$ be a ball with radius $r$. Suppose that $B inter overline(V_i) != emptyset$ for some $i$, then $V_i subset.eq B(x, (1 + 2a_2) r)$ since $V_i$ is contained in a ball of radius $a_2 r$ and intersects with $B$. Suppose that $k$ of the sets $overline(V_i)$ intersect with $B$, then
    $
    m(B(x, (1 + 2a_2) r)) >= sum_{i: B inter overline(V_i) != emptyset} m(V_i) >= k dot m(B(0, a_1 r)),
    $
    where $m$ is the Lebesgue measure on $RR^d$, so $k <= (1 + 2a_2)^d a_1^(-d)$.
    $qed$
]

#theorem(name: "Hutchinson")[
    Let $K$ be a self-similar set that is the attractor of an IFS $(phi_1, dots, phi_n)$ consisting of similitudes with contraction ratios $(r_1, dots, r_n)$ satisfying the open set condition. Then $dim_H (K) = alpha$, where $alpha$ is the unique solution to the equation
    $
    sum_(i=1)^n r_i^alpha = 1.
    $
    Moreover, $0 < cal(H)^alpha (K) < oo$.
]
#proof[
    It suffices to show that $cal(H)^alpha (K) > 0$. By @thm:self_similar_measures, there exists a self-similar measure $mu$ associated to the IFS with probability vector $(r_1^alpha, dots, r_n^alpha)$, which is a mass distribution on $K$. Write
    $
    E[x_1, dots, x_k] = phi_(x_1) compose dots.c compose phi_(x_k)(E). 
    $
    Let $V$ be the bounded open set from the open set condition. Choose $a_1, a_2 > 0$ such that $V$ contains a ball of radius $a_1$ and is contained in a ball of radius $a_2$. Fix $0 < rho < 1$. For every $(x_i) in sum_n$, there is exactly one $k$ such that
    $
    r_(x_1) dot dots.c dot r_(x_k) <= rho < r_(x_1) dot dots.c dot r_(x_(k-1)). 
    $
    Set
    $
    cal(S) = union.big_k {(x_1, dots, x_k) : r_(x_1) dot dots.c dot r_(x_k) <= rho < r_(x_1) dot dots.c dot r_(x_(k-1))}. 
    $
    By the open set condition, the sets $V[x_1, dots, x_k]$ are pairwise disjoint for $(x_1, dots, x_k) in cal(S)$, and each $V[x_1, dots, x_k]$ contains a ball of radius
    $
    a_1 r_(x_1) dot dots.c dot r_(x_k) >= a_1 rho dot min_{1 <= i <= n} r_i
    $
    and is contained in a ball of radius
    $
    a_2 r_(x_1) dot dots.c dot r_(x_k) <= a_2 rho. 
    $
    By the previous lemma, any ball of radius $rho$ intersects with at most
    $
    M := (1 + 2a_2)^d a_1^(-d) min_{1 <= i <= n} r_i^(-d)
    $
    of the sets from the collection
    $
    {overline(V[x_1, dots, x_k]) : (x_1, dots, x_k) in cal(S)}. 
    $

    Define
    $
    Phi: cal(K) -> cal(K), quad Phi(E) = union.big_(i=1)^n phi_i (E),
    $
    then $Phi$ is a contraction on $(cal(K), cal(D))$. Since $V supset.eq Phi(V)$, we have $overline(V) supset.eq Phi(overline(V)) supset.eq Phi^2(overline(V)) supset.eq dots.c$, and also $lim_(n -> oo) Phi^n (overline(V)) = K$ in the Hausdorff metric, so $overline(V) supset.eq K$, and hence $overline(V[x_1, dots, x_k]) supset.eq K[x_1, dots, x_k]$. Note that ${K[x_1, dots, x_k] : (x_1, dots, x_k) in cal(S)}$ covers $K$, so the collection ${overline(V[x_1, dots, x_k]) : (x_1, dots, x_k) in cal(S)}$ also covers $K$. 

    Let $cal(U)$ be a closed set with diameter $rho$, then there exists a ball $cal(B)$ with radius $2rho$ that contains $cal(U)$. Recall from @thm:self_similar_measures that
    $
    mu(K[x_1, dots, x_k]) >= r_(x_1)^alpha dot dots.c dot r_(x_k)^alpha. 
    $
    In fact, the equality holds when $phi$ satisfies the open set condition, so
    $
    mu(cal(U)) &<= mu(cal(B)) = mu(K inter cal(B)) \
    &<= sum_{(x_1, dots, x_k) in cal(S): overline(V[x_1, dots, x_k]) inter cal(B) != emptyset} mu(K[x_1, dots, x_k]) \
    &<= sum_{(x_1, dots, x_k) in cal(S): overline(V[x_1, dots, x_k]) inter cal(B) != emptyset} r_(x_1)^alpha dot dots.c dot r_(x_k)^alpha \
    &<= M dot rho^alpha = M dot "diam"(cal(U))^alpha.
    $
    By @thm:mass_distribution, we have $cal(H)^alpha (K) >= mu(K) / M > 0$.
    $qed$
]

#example[
    + Since the unit interval is the attractor of the IFS consisting of two similitudes
        $
        phi_1(x) = x/2,  quad  phi_2(x) = x/2 + 1/2,
        $
        the Hausdorff dimension of the unit interval is the unique solution to
        $
        (1/2)^alpha + (1/2)^alpha = 1,
        $
        which is $alpha = 1$. 
    + The middle-thirds Cantor set is the attractor of the IFS consisting of two similitudes
        $
        phi_1(x) = x/3,  quad  phi_2(x) = x/3 + 2/3,
        $
        so its Hausdorff dimension is the unique solution to
        $
        (1/3)^alpha + (1/3)^alpha = 1,
        $
        which is $alpha = log_3(2)$.
    + The Sierpinski triangle is the attractor of the IFS consisting of three similitudes of contraction ratio $1/2$ and satisfies the open set condition, so its Hausdorff dimension is the unique solution to
        $
        (1/2)^alpha + (1/2)^alpha + (1/2)^alpha = 1,
        $
        which is $alpha = log_2(3)$.
    + The von Koch curve is the attractor of the IFS consisting of four similitudes of contraction ratio $1/3$ and satisfies the open set condition, so its Hausdorff dimension is the unique solution to
        $
        (1/3)^alpha + (1/3)^alpha + (1/3)^alpha + (1/3)^alpha = 1,
        $
        which is $alpha = log_3(4)$.
]

== The Geometry of Fractals

We want to compare the geometry of a fractal set with that of a smooth manifold. 

=== Projections of Self-similar Sets

We call a set $C subset.eq R^d$ a $1$-set if $0 < cal(H)^1 (C) < oo$, in particular $dim_H (C) = 1$. 

Suppose that $C subset.eq R^2$ is a self-similar set, which is the attractor of $n$ similitudes $phi_1, dots, phi_n$ with contraction rations $1/n$ and satisfies the strong separation condition. Assume that the similitudes do not involve rotations, i.e. $phi_i (x) = x/n + a_i$ for some $a_i in R^2$ for every $i$. By Hutchinson's theorem, $C$ is a $1$-set. Clearly, smooth curves are $1$-sets, but not all $1$-sets are smooth curves. For example, the attractor of the IFS consisting of four similitudes
$
phi_1(x) = x/4,  quad  phi_2(x) = x/4 + (3/4, 0),  quad  phi_3(x) = x/4 + (0, 3/4),  quad  phi_4(x) = x/4 + (3/4, 3/4)
$
is a $1$-set, but it is not a smooth curve since it contains four disjoint copies of itself.

We say a set $S subset.eq R^2$ is invisible from direction $theta in [0, pi)$ if the orthogonal projection $"proj"_theta$ of $S$ onto the line with angle $theta$ has zero Lebesgue measure. 

The projection of a differentiable curve $gamma$ gives an interval (possibly degenerate) for every direction. This interval is degenerate if and only if $gamma$ is a straight line and the direction is perpendicular to $gamma$. In particular, a smooth curve is invisible from at most one direction. 

#theorem(id: "thm:invisible_1-set")[
    Let $C subset.eq R^2$ be a self-similar set that is the attractor of $n$ similitudes
    $
    phi_i(x) = x/n + a_i,  quad  a_i in R^2,
    $
    satisfying the strong separation condition. Then $C$ is invisible for Lebesgue-almost every direction.
]
#proof[
    Let $C(theta) := "proj"_theta (C)$ for every $theta in [0, pi)$. If $a_i(theta)$ is the projection of $a_i$ onto the line with angle $theta$, then
    $
    C(theta) = union.big_(i=1)^n (C(theta)/n + a_i (theta)),
    $
    so $C(theta)$ is a self-similar set of similarity dimension $1$. 

    Let $b_1, dots, b_n in RR$, $psi_i(x) = x/n + b_i$ and $K subset.eq RR$ be the attractor of the IFS $(psi_1, dots, psi_n)$. Write $K_i = psi_i(K)$ for each $i$. 

    #claim[
        $m(K_i inter K_j) = 0$ for $i != j$, where $m$ is the Lebesgue measure on $RR$.
    ]
    #proof[
        Fix $i != j$, then
        $
        m(K) = m(union.big_(l=1)^n K_l) <= sum_(l=1)^n m(K_l) - m(K_i inter K_j) = m(K) - m(K_i inter K_j),
        $
        so $m(K_i inter K_j) = 0$.
        $qed$
    ]

    #claim(id: "clm:not_pairwise_disjoint")[
        Exists $i != j$ such that $K_i inter K_j != emptyset$. 
    ]
    #proof[
        Suppose that all $K_i$ are pairwise disjoint. By compactness, there exists $epsilon > 0$ such that the epsilon-neighborhoods $K_i [epsilon]$ are still pairwise disjoint. But
        $
        m(K[epsilon]) = sum_(i=1)^n m(K_i [epsilon]) = n dot m(1/n (K[epsilon n])) = m(K[epsilon n]). 
        $
        Since $n > 1$, this is a contradiction.
        $qed$
    ]

    #claim[
        If $m(K) > 0$ and $eta in (0, 1)$, then $exists$ an interval $J$ such that $m(K inter J) > eta m(J)$. 
    ]
    #proof[
        Suppose that $m(K) > 0$ and $eta in (0, 1)$. By outer regularity of Lebesgue measure, we can find an open set $U supset.eq K$ such that $m(U) < m(K) / eta$. Since $U$ is open, we can write $U$ as a countable union of disjoint open intervals. If $m(E inter J) < eta m(J)$ for every such interval $J$, then
        $
        m(K) = m(U inter K) <= sum_J m(U inter J) < eta sum_J m(J) = eta m(U) < m(K),
        $
        which is a contradiction.
        $qed$
    ]

    For a word $u = (u_1, dots, u_k)$, define
    $
    K_u = psi_(u_1) compose dots.c compose psi_(u_k)(K), 
    $
    then
    $
    K = union.big_(u : |u| = m) K_u. 
    $
    For two distinct words $u$ and $v$ of length $m$, we call $K_u$ and $K_v$ $epsilon$-close if $K_u = K_v + x$ for some $x$ with $|x| <= epsilon n^(-m)$. 

    #lemma(name: "Bandt-Graf")[
        If for all $epsilon > 0$, there exists two distinct words $u$ and $v$ of the same length such that $K_u$ and $K_v$ are $epsilon$-close, then $m(K) = 0$.
    ]
    #proof[
        Suppose $m(K) > 0$, then there exists an interval $J$ such that $m(K inter J) > 0.9 m(J)$. Let $epsilon = 0.1 m(J) > 0$. By assumption, exists $K_u, K_v$ that are $epsilon$-close. Write
        $
        K_u = 1/(n^m) K + b_u,  quad  K_v = 1/(n^m) K + b_v. 
        $
        Set
        $
        J_u = psi_(u_1) compose dots.c compose psi_(u_k)(J),  quad  J_v = psi_(v_1) compose dots.c compose psi_(v_k)(J),
        $
        then
        $
        m(K_u inter J_u) = 1/(n^m) m(K inter J) > 0.9 m(J_u), \ 
        m(K_v inter J_v) = 1/(n^m) m(K inter J) > 0.9 m(J_v).
        $
        Since $K_u$ and $K_v$ are $epsilon$-close, we have
        $
        & |b_u - b_v| <= epsilon n^(-m) = 0.1 m(J) n^(-m) = 0.1 m(J_u) \
        ==> & m(J_u inter J_v) >= m(J_u) - |b_u - b_v| - |b_v - b_u| >= 0.8 m(J_u) \
        ==> & m(K_u inter K_v) >= m(J_u inter J_v) - m(J_u inter K_u^c) - m(J_v inter K_v^c) \
        &>= 0.8 m(J_u) - 0.1 m(J_u) - 0.1 m(J_v) = 0.6 m(J_u) > 0,
        $
        contradicting the previous claim.
        $qed$
    ]

    Let $epsilon > 0$. Define
    $
    Theta(epsilon) = {theta in [0, pi) : exists u != v "such that" C(theta)_u "and" C(theta)_v "are" epsilon"-close"}.
    $
    By Bandt-Graf lemma, if $theta in Theta(epsilon)$ for all $epsilon > 0$, then $m(C(theta)) = 0$. It suffices to show that $Theta(epsilon)$ has full measure for every $epsilon > 0$.

    #lemma[
        Suppose that $I$ is an interval and $B subset.eq I$ is a Borel subset such that $exists a, b > 0$ such that the porosity condition holds for all $theta in I$, i.e. for every $delta > 0$, the interval $[theta - a delta, theta + a delta]$ contains a subinterval of length $b delta$ that is disjoint from $I without B$. Then $m(I without B) = 0$.
    ]
    #proof[
        Divide $I$ into finitely many subintervals of length $2 a delta$. For each such interval we can remove an interval of length $b delta$ that is disjoint from $I without B$. The remainder is a union of intervals of total length $m(I) (1 - b/(2a))$. Repeating this process indefinitely, we have $m(I without B) <= m(I) (1 - b/(2a))^n$ for every $n$, so $m(I without B) = 0$.
        $qed$
    ]

    WLOG assume that $C subset.eq [0, 1]^2$. We will show that for every $epsilon > 0$, the porosity condition holds for $[0, pi) without Theta(epsilon)$. It suffices to for $delta$ of form $n^(-m)$. Fix $theta_0 in [0, pi)$. By @clm:not_pairwise_disjoint, there exist $i != j$ such that $C(theta_0)_i inter C(theta_0)_j != emptyset$. In particular, for each $m$, $exists$ words $u = (i, u_2, dots, u_m)$ and $v = (j, v_2, dots, v_m)$ such that
    $
    C(theta_0)_u inter C(theta_0)_v != emptyset.
    $
    Note that for all words $w$ of length $m$, exists some $a_w$ such that
    $
    C_w = 1/(n^m) C + a_w.
    $
    Since $C subset.eq [0, 1]^2$, we have
    $
    C_w subset.eq Q_w := 1/(n^m) [0, 1]^2 + a_w.
    $
    Let $theta_1$ be the angle of the line orthogonal to $overline(a_u a_v)$, then $Q_u$ and $Q_v$ have the same projection onto $L_(theta_1)$, and same for $C_u$ and $C_v$. Since the two squares $Q_u$ and $Q_v$ have distance $<= 1$ and the projection is Lipschitz, there exists a universal constant $c > 0$ such that for every $epsilon > 0$ and every $theta in (theta_1 - c epsilon n^(-m), theta_1 + c epsilon n^(-m))$, one has $Q_u(theta) = Q_v(theta) + x$ for some $|x| <= epsilon n^(-m)$, i.e. $(theta_1 - c epsilon n^(-m), theta_1 + c epsilon n^(-m)) subset.eq Theta(epsilon)$. By strong separation condition and compactness, we can choose $r > 0$ such that $d(C_k, C_l) > r$ for every distinct $k, l = 1, dots, n$. By basic geometry, $exists A > 0$ such that
    $
    |theta_1 - theta_0| <= A (n^(-m))/(d(C_i, C_j)) <= A (n^(-m))/r <= (A/r + c epsilon) n^(-m).
    $
    Therefore, the interval $[theta_0 - (A/r + c epsilon) n^(-m), theta_0 + (A/r + c epsilon) n^(-m)]$ contains a subinterval of length $2 c epsilon n^(-m)$ that is contained in $Theta(epsilon)$, so the porosity condition holds for $[0, pi) without Theta(epsilon)$. By the previous lemma, we have $m([0, pi) without Theta(epsilon)) = 0$.
    $qed$
]

#theorem[
    Let $C$ be a self-similar $1$-set in $R^2$ that is the attractor of $n$ similitudes satisfying the strong separation condition. Then for all Lipscitz curves $gamma: RR -> RR^2$, $gamma(RR) inter C$ has zero $1$-Hausdorff measure. 
]
#proof[
    If $cal(H)^1 (gamma(RR) inter C) > 0$, then we can find a small interval $I$ such that the segment $gamma(I)$ is almost covered by $C$. The projections of $gamma(I) inter C$ and $gamma(I)$ are almost the same. $gamma(I)$ projects on a nondegenerate interval in all but at most one direction, but $C$ is invisible for almost every direction, so we have a contradiction.
    $qed$
]

#remark[
    - This property is sometimes taken as the definition of a fractal (or irregular set) in geometric measure theory. Analogous definitions hold for $m$-sets for $m in NN$, replacing curves by manifolds. 
    - Besicovitch projection theorem states that the above alternative definition is equivalent to the invisibility of self-similar $1$-sets. 
]

== The Besicovitch Problem

The Besicovitch problem asks the following question: what is the size of the smallest set in $RR^2$ that contains a unit line segment in every direction?

#lemma[
    There exists a compact $C subset.eq [0, 1]^2$ with $0 < cal(H)^1(C) < oo$ such that the projection of $C$ onto the $x$-axis is $[0, 1]$, but $C$ is invisible from almost all directions. 
]
#proof[
    Consider the IFS consisting of four similitudes
    $
    phi_1(x) = x/4,  quad  phi_2(x) = x/4 + (1/4, 3/4), \
    phi_3(x) = x/4 + (1/2, 0),  quad  phi_4(x) = x/4 + (3/4, 3/4).
    $
    Let $C$ be the attractor of this IFS, then $C$ is a $1$-set by Hutchinson's theorem. Moreover, the projection of $C$ onto the $x$-axis is $[0, 1]$, but $C$ is invisible from almost all directions by @thm:invisible_1-set. 
    $qed$
]

#theorem(name: "Besicovitch")[
    There exists a Borel set $B subset.eq RR^2$ with $m(B) = 0$ containing an infinite line in every direction. 
]
#proof[
    Take $C$ from the previous lemma. For each point $(a, b) in C$, consider the lines
    $
    ell(a, b) = {(x, y) in RR^2 : y = a x + b}.
    $
    Define
    $
    B' = union.big_((a, b) in C) ell(a, b). 
    $
    Note that the function $f(a, b, x) = (x, a x + b)$ is continuous. Since $RR$ is $sigma$-compact,  $B' = f(C times RR)$ is a countable union of compact sets, hence Borel. From the construction of $C$, for all $a in [0, 1]$, there exists $b in [0, 1]$ such that $(a, b) in C$, so for each $theta in [0, pi/4]$, there exists a line with angle $theta$ contained in $B'$. Taking $B$ as the union of $B'$ and its rotations by angles $pi/4, pi/2$ and $3pi/4$, we have that $B$ contains a line in every direction. It remains to show that $m(B) = 0$, or equivalently $m(B') = 0$. By Fubini's theorem, it suffices to show that almost every vertical line intersects with $B'$ on a set of zero Lebesgue measure. For each $x in RR$, the intersection of $B'$ with the vertical line $\{x\} times RR$ is
    $
    B' inter (\{x\} times RR) = {f(a, b, x) : (a, b) in C} = {x} times {a x + b : (a, b) in C},
    $
    but ${a x + b : (a, b) in C}$ is the projection of $C$ onto the line with slope $1/x$, which has zero Lebesgue measure for almost every $x$ since $C$ is invisible from almost every direction, so $m(B' inter (\{x\} times RR)) = 0$ for almost every $x$. Therefore, $m(B') = 0$.
    $qed$
]

#remark[
    - In higher dimensions, the problem of finding the smallest set containing a unit line segment in every direction is still open. 
    - Another natural question is to ask the minimal dimension of such a set in $RR^d$. Kakeya's conjectiure states that the Hausdorff dimension of such a set in $RR^d$ is $d$. 
        - In $1971$, the case $d = 2$ was proved by Davies. 
        - In $1995$, Wolff proved that the Hausdorff dimension of such a set has dimension at least $(d + 2)/2$. 
        - In $2000$, Katz, Laba and Tao improved the lower bound to $5/2 + epsilon$ for $d = 3$. 
        - In $2002$, Katz and Tao improved the lower bound to $(2 - sqrt(2))(d - 4) + 3$. 
        - In $2019$, Katz and Zahl improved KLT's bound. 
        - In $2025$, Wang and Zahl proved the Kakeya conjecture in $RR^3$.
]

= Ergodic Theory

#definition[
    Let $(X, cal(M), mu)$ be a probability space (which means that $mu(X) = 1$). 
    - A measurable function $T: X -> X$ is called measure-preserving if
    $
    mu(T^(-1)(A)) = mu(A)
    $
    for every $A in cal(M)$.
    - A measure-preserving transformation $T$ is called ergodic if for every $A in cal(M)$, if $T^(-1)(A) = A$, then $mu(A) = 0$ or $1$.
    - Let $phi: X -> [0, oo)$ be bounded and measurable. The time average of $phi$ along the trajectory $x, T(x), T^2 (x), ...$ at time $n-1$ is defined as
    $
    1/n sum_(k=0)^(n-1) phi(T^k (x)).
    $
    The space average of $phi$ is defined as
    $
    integral_X phi d mu.
    $
]

#theorem(name: "Birkhoff")[
    Let $T: X -> X$ be measure-preserving. Suppose that $phi: X -> [0, oo)$ is bounded and measurable. The the limit
    $
    psi(x) := lim_(k -> oo) 1/k sum_(j=0)^(k-1) phi(T^j (x))
    $
    exists and satisfies $psi compose T = psi$ for $mu$-a.e. $x in X$, and
    $
    integral_X phi d mu = integral_X psi d mu.
    $
    If furthermore $T$ is ergodic, then $psi$ is constant $mu$-a.e. with value $integral_X phi d mu$.
]
#proof[
    Let $M$ be an upper bound for $phi$. Write
    $
    alpha_k (x) = 1/k sum_(j=0)^(k-1) phi(T^j (x)). 
    $
    Let $overline(alpha)(x) = limsup_(k -> oo) alpha_k (x)$, then $overline(alpha)$ is measurable and
    $
    overline(alpha)(T(x)) &= limsup_(k -> oo) 1/k sum_(j=0)^(k-1) phi(T^(j+1) (x)) \
    &= limsup_(k -> oo) 1/k (sum_(j=0)^(k-1) phi(T^j (x)) - phi(x) + phi(T^k (x))) = overline(alpha)(x).
    $
    By induction, $overline(alpha)(T^n (x)) = overline(alpha)(x)$ for every $n$. 

    We claim that $integral_X overline(alpha) d mu <= integral_X phi d mu$. Fix $epsilon > 0$. Define
    $
    tau(x) = min {k in NN : alpha_k (x) >= overline(alpha)(x) - epsilon}.
    $
    By definition, $tau(x) < oo$ for every $x$ and is measurable. Assume first that $tau(x) <= S$ for every $x$ for some $S in NN$. For each $x$, define a sequence $k_1, k_2, ...$ recursively by setting $k_1 = tau(x)$ and
    $
    k_i := tau(T^(k_1 + dots.c + k_(i-1)) (x)).
    $
    Then for each $i$,
    $
    sum_(j=k_1 + dots.c + k_(i-1))^(k_1 + dots.c + k_i - 1) phi(T^j (x)) &= k_i alpha_(k_i) (T^(k_1 + dots.c + k_(i-1)) (x)) \
    &>= k_i (overline(alpha)(T^(k_1 + dots.c + k_(i-1)) (x)) - epsilon) = k_i (overline(alpha)(x) - epsilon).
    $
    Summing over $i$, if $k$ is of the form $k_1 + dots.c + k_i$, then
    $
    sum_(j=0)^(k-1) phi(T^j (x)) >= sum_(i=1)^i k_i (overline(alpha)(x) - epsilon) >= k (overline(alpha)(x) - epsilon). 
    $
    For arbitrary $k$, let $l$ be the largest integer such that $k_1 + dots.c + k_l <= k$, then $0 <= k - (k_1 + dots.c + k_l) < S$. Also, 
    $
    sum_(j=0)^(k-1) phi(T^j (x)) &>= sum_(j=0)^(k_1 + dots.c + k_l - 1) phi(T^j (x)) \
    &>= (k_1 + dots.c + k_l) (overline(alpha)(x) - epsilon) >= (k - S) (overline(alpha)(x) - epsilon).
    $
    Therefore, 
    $
    integral phi compose T^j d mu &= integral phi d (mu compose T^(-j)) = integral phi d mu \
    &>= integral (k - S)/k (overline(alpha) - epsilon) d mu. 
    $
    Letting $k -> oo$ and then $epsilon -> 0$, we have
    $
    integral_X phi d mu >= integral_X overline(alpha) d mu.
    $
    In general, $tau$ may not be bounded. Define $A = {x : tau(x) > S}$, then $mu(A) -> 0$ as $S -> oo$. Choose $S$ large enough such that $mu(A) < epsilon$. We'll modify the definition of $phi$ on $A$ and apply the previous argument to the modified function. Define
    $
    phi^*(x) = cases(
        phi(x) & "if" x in.not A,
        M & "if" x in A.
    )
    $
    Consider
    $
    alpha_k^* (x) = 1/k sum_(j=0)^(k-1) phi^*(T^j (x)), quad tau^*(x) = min {k in NN : alpha_k^* (x) >= overline(alpha)(x) - epsilon}.
    $
    If $x in A$, then $alpha^*_1 (x) = phi^*(x) = M >= overline(alpha)(x) - epsilon$, so $tau^*(x) = 1$. Also, $alpha_k^* (x) >= alpha_k (x)$ for every $x$ and $k$, so $tau^*(x) <= tau(x)$ for every $x$. In particular, $tau^*(x) <= S$ for every $x$. The previous argument applied to $phi^*$ and $tau^*$ gives
    $
    integral_X overline(alpha) d mu &<= integral_X phi^* d mu + epsilon \
    &= integral_X phi d mu + epsilon (M - integral_X phi d mu) + epsilon \
    &<= integral_X phi d mu + epsilon M + epsilon.
    $
    Taking $epsilon -> 0$, we have $integral_X overline(alpha) d mu <= integral_X phi d mu$. Similarly, we can show that
    $
    integral_X underline(alpha) d mu >= integral_X phi d mu,
    $
    where $underline(alpha)(x) = liminf_(k -> oo) alpha_k (x)$, so
    $
    integral_X (underline(alpha) - overline(alpha)) d mu >= 0,
    $
    so $underline(alpha) = overline(alpha) = psi = psi(T)$ $mu$-a.e., and
    $
    integral_X phi d mu = integral_X overline(alpha) d mu = integral_X psi d mu.
    $

    Now suppose that $T$ is ergodic. For every $a >= 0$, define
    $
    L(a) = {x : psi(x) <= a}.
    $
    Note that
    $
    T(x) in L(a) iff psi(x) = psi(T(x)) <= a iff x in L(a),
    $
    so $T^(-1)(L(a)) = L(a)$, and hence $mu(L(a)) = 0$ or $1$. Let
    $
    c = sup {a : mu(L(a)) = 0} = inf {a : mu(L(a)) = 1},
    $
    then $psi(x) <= c$ for $mu$-a.e. $x$ and $psi(x) >= c$ for $mu$-a.e. $x$, so $psi(x) = c$ for $mu$-a.e. $x$. Since
    $
    c = integral_X psi d mu = integral_X phi d mu,
    $
    we have $psi(x) = integral_X phi d mu$ for $mu$-a.e. $x$.
    $qed$
]

== Chaos Game

Chaos game is a stochastic method to generate self-similar sets. Given an IFS $phi_1, dots, phi_n$ on $RR^d$, let $K$ be the attractor of this IFS. Choose a probability vector $(p_1, dots, p_n)$ such that $p_i > 0$ for every $i$ and $sum_(i=1)^n p_i = 1$. Pick an arbitrary point $y_0 in RR^d$ and define a sequence $y_1, y_2, ...$ recursively by choosing $X_k in {1, dots, n}$ independently with distribution $(p_1, dots, p_n)$ and setting $y_k = phi_(X_k) (y_(k-1))$ for every $k >= 1$. This algorithm produces a random sequence of points ${y_0, y_1, y_2, ...}$ in $RR^d$.

#theorem[
    Suppose that $X subset.eq RR^d$ is compact. Let $phi_1, dots, phi_n$, $K$, $mu$ be as above. Let $g: X -> [0, oo)$ be continuous. Then, with probability $1$, 
    $
    lim_(k -> oo) 1/k sum_(i=0)^(k-1) g(y_i) = integral_K g d mu.
    $
]
#proof[
    We first show that the limit does not depend on the starting point. If we choose two starting points $y_0$ and $y_0'$, let $(y_i)$ and $(y_i')$ be the corresponding sequences generated by the same sequence of random choices $X_1, X_2, ...$. Then
    $
    d(y_k, y_k') <= c^k d(y_0, y_0') -> 0
    $
    as $k -> oo$, where $c < 1$ is the maximum of the contraction ratios of the $phi_i$'s. Let $epsilon > 0$ and choose $N$ large such that
    $
    |g(y_k) - g(y_k')| < epsilon
    $
    for every $k >= N$. Then
    $
    & limsup_(k -> oo) abs(1/k sum_(i=0)^(k-1) g(y_i) - 1/k sum_(i=0)^(k-1) g(y_i')) \
    <= & limsup_(k -> oo) 1/k sum_(i=0)^(N-1) abs(g(y_i) - g(y_i')) + limsup_(k -> oo) 1/k sum_(i=N)^(k-1) abs(g(y_i) - g(y_i')) <= epsilon.
    $

    Next, we define appropriate probability space and measure-preserving transformation to apply Birkhoff's ergodic theorem. In order to make the operation deterministic, a point in our space will represent to a point in $K$ together with all future random choices. 

    Consider the code space $sum_n = {1, dots, n}^NN$, where each point represents a sequence of random choices. By coding theorem, each point in $K$ can also be represented by a sequence in $sum_n$. Let $pi: sum_n -> K$ be the coding map. Take the space of double-sided sequences $sum_n^*$, where each $(x_k)_{k in ZZ} in sum_n^*$ represents the point $pi((x_(-1), x_(-2), ...))$ in $K$ together with the future random choices $(x_0, x_1, ...)$. By coding theorem, 
    $
    phi_(x_0) (pi((x_(-1), x_(-2), ...))) = pi((x_0, x_(-1), x_(-2), ...)).
    $
    At the same time, after applying $phi_(x_0)$, the future random choices are shifted by one step, so we can define a transformation $T: sum_n^* -> sum_n^*$ by
    $
    T((x_k)_(k in ZZ)) = (x_(k+1))_(k in ZZ).
    $
    Define $phi: sum_n^* -> [0, oo)$ by
    $
    phi((x_k)_(k in ZZ)) = g(pi((x_(-1), x_(-2), ...))).
    $
    If $y_0 = pi((x_(-1), x_(-2), ...))$, then
    $
    phi(T((x_k))) = g(pi((x_0, x_(-1), x_(-2), ...))) = g(phi_(x_0) (pi((x_(-1), x_(-2), ...)))) = g(y_1),
    $
    and by induction, $phi(T^j ((x_k))) = g(y_j)$ for every $j >= 0$.

    Consider the $sigma$-algebra $cal(M)$ on $sum_n^*$ generated by the cylinder sets
    $
    {(x_k)_(k in ZZ) : x_i = y_i forall i in I}
    $
    for every finite set $I subset.eq ZZ$ and every $y_i in {1, dots, n}$ for $i in I$. Let $nu$ be the product measure on $sum_n^*$ such that
    $
    nu({(x_k) : x_i = y_i forall i in I}) = product_(i in I) p_(y_i)
    $
    for every finite set $I subset.eq ZZ$ and every $y_i in {1, dots, n}$ for $i in I$, which extends uniquely to a probability measure on $cal(M)$. 

    We claim that $T$ is measure-preserving and ergodic with respect to $nu$. Indeed, for every cylinder set $A = {(x_k) : x_i = y_i forall i in I}$, we have
    $
    T^(-1)(A) = {(x_k) : x_(i+1) = y_i forall i in I} = {(x_k) : x_i = y_(i-1) forall i in I},
    $
    so $nu(T^(-1)(A)) = nu(A)$. Since the cylinder sets generate $cal(M)$, we have $nu(T^(-1)(A)) = nu(A)$ for every $A in cal(M)$. Note that for all $A in cal(M)$ and $epsilon > 0$, there exists a finite collection of cylinder sets $C_1, ..., C_m$ such that
    $
    nu(A triangle union.big_(i=1)^m C_i) < epsilon. 
    $
    We can show this by considering the collection of all $A in cal(M)$ that satisfies the above property, which is a $sigma$-algebra containing all cylinder sets, so it must be $cal(M)$. Let $A in cal(M)$ with $A = T^(-1)(A)$ and $nu(A) > 0$. We'll show $nu(A inter E) = nu(A)nu(E)$ for all cylinder sets $E$. Fix a cylinder set $E = {(x_k) : x_i = y_i forall i in I}$. Fix $epsilon > 0$, and find an approximation of cylinder sets $C_1, ..., C_m$ such that $nu(A triangle union.big_(i=1)^m C_i) < epsilon$, then
    $
    nu(A inter E) &= nu(T^(-N)(A) inter E) = nu(A inter T^N (E)) \
    &in [nu((union.big_(i=1)^m C_i) inter T^N (E)) - epsilon, nu((union.big_(i=1)^m C_i) inter T^N (E)) + epsilon]. 
    $
    Consider
    $
    C = {(x_k) : x_l = y_l ' forall l in L}
    $
    where $L subset.eq ZZ$ is finite. Choose $N$ large such that $max I - N < min L$, then
    $
    nu(C inter T^N (E)) &= nu({(x_k) : x_l = y_l ' forall l in L, x_(i-N) = y_i forall i in I}) \
    &= product_(l in L) p_(y_l ') product_(i in I) p_(y_i) = nu(C) nu(E).
    $
    Therefore, when $N$ is large, 
    $
    nu((union.big_(i=1)^m C_i) inter T^N (E)) &= sum_(i=1)^m nu(C_i inter T^N (E)) \
    &in [sum_(i=1)^m nu(C_i) nu(E) - m epsilon, sum_(i=1)^m nu(C_i) nu(E) + m epsilon] \
    &in [nu(A) nu(E) - (m + 1) epsilon, nu(A) nu(E) + (m + 1) epsilon].
    $
    Letting $epsilon -> 0$, we have $nu(A inter E) = nu(A)nu(E)$ for every cylinder set $E$. We then define
    $
    lambda(E) = nu(A inter E) / nu(A),
    $
    which gives $lambda(E) = nu(E)$ for every cylinder set $E$, so $lambda = nu$, implying that $nu(A) = lambda(A) = 1$.

    Finally, by apply Birkhoff's ergodic theorem to $phi$ and $T$, we get
    $
    lim_(k -> oo) 1/k sum_(i=0)^(k-1) g(y_i)
    &= lim_(k -> oo) 1/k sum_(i=0)^(k-1) g(phi_(x_(i-1)) compose dots.c compose phi_(x_0) (pi((x_(-1), x_(-2), ...))) \
    &= lim_(k -> oo) 1/k sum_(i=0)^(k-1) g(pi((x_(i-1), x_(i-2), ...))) \
    &= lim_(k -> oo) 1/k sum_(i=0)^(k-1) phi(T^i ((x_k))) \
    &= integral phi d nu = integral_K g d mu
    $
    holds for $nu$-a.e. $(x_k) in sum_n^*$, i.e. the equation holds with probability $1$ for the sequence $(y_i)$ generated by the chaos game.
    $qed$
]

#remark[
    By approximating characteristic functions by continuous functions, we can show that with probability $1$, for every Borel set $A subset.eq K$ with $mu(partial A) = 0$, we have
    $
    lim_(k -> oo) 1/k sum_(j=0)^(k-1) chi_A (y_j) = mu(A).
    $
]

== Normal Numbers

Every real number $x in [0, 1)$ has a binary expansion
$
x = sum_(i=1)^oo (x_i)/(2^i), quad x_i in {0, 1}. 
$
A number $x in [0, 1)$ is called _normal_ in base $2$ if in its binary exponsion, the frequency of appearances of any finite sequence of digits $a_1a_2 dots.c a_n$ is $2^(-n)$. More precisely, 
$
lim_(k -> oo) (\#{1 <= i <= k : x_i = a_1, x_(i+1) = a_2, dots.c, x_(i+n-1) = a_n})/k = 1/(2^n). 
$
Although this looks restrictive, it turns out that almost every number in $[0, 1)$ is normal in base $2$.

#lemma[
    Define $T: [0, 1) -> [0, 1)$ by $T(x) = 2x mod 1$. Then $T$ is measure-preserving and ergodic with respect to the Lebesgue measure on $[0, 1)$.
]
#proof[
    Define
    $
    phi_1(x) = x/2, quad  phi_2(x) = x/2 + 1/2.
    $
    Then $T^(-1)(A) = phi_1(A) union.sq phi_2(A)$ for every Borel set $A subset.eq [0, 1)$, hence
    $
    m(T^(-1)(A)) = m(phi_1(A)) + m(phi_2(A)) = m(A),
    $
    so $T$ is measure-preserving. 

    To show ergodicity, first consider dyadic intervals $cal(D)_(n, k) = [k/(2^n), (k+1)/(2^n))$ for $n in NN$ and $0 <= k < 2^n$. We claim that for all measurable $A$, 
    $
    m(T^(-n)(A) inter cal(D)_(n, k)) = 1/(2^n) m(A) = m(A) m(cal(D)_(n, k)).
    $
    When $n = 1$, $T^(-1)(A) inter [0, 1/2) = phi_1(A)$, so
    $
    m(T^(-1)(A) inter cal(D)_(1, 0)) = m(phi_1(A)) = m(A)/2 = m(A) m(cal(D)_(1, 0)).
    $
    Similar for $cal(D)_(1, 1)$. Assume that the claim holds for $n$. Consider the interval $cal(D)_(n+1, k)$. We can write $k = r 2^n + j$, where $r = 0$ or $1$ and $0 <= j < 2^n$. If $r = 0$, then $cal(D)_(n+1, k) subset.eq [0, 1)$, so by induction hypothesis, 
    $
    m(T^(-n-1)(A) inter cal(D)_(n+1, k)) &= m(T^(-1)(T^(-n)(A) inter cal(D)_(n, j))) \
    &= m(phi_1(T^(-n)(A) inter cal(D)_(n, j))) \
    &= 1/2 m(T^(-n)(A) inter cal(D)_(n, j)) \
    &= 1/2 m(A) m(cal(D)_(n, j)) = m(A) m(cal(D)_(n+1, k)). 
    $
    Similar for $r = 1$. Therefore, the claim holds for every $n$ and $k$. This implies that
    $
    m(A inter cal(D)_(n, k)) = m(A) m(cal(D)_(n, k))
    $
    for $A$ measurable with $m(A) > 0$ and $T^(-1)(A) = A$ and for every $n$ and $k$. Set $lambda(E) = m(A inter E)/m(A)$ for every measurable $E subset.eq [0, 1)$, then $lambda(cal(D)_(n, k)) = m(cal(D)_(n, k))$ for every $n$ and $k$, so by $pi$-$lambda$ theorem, $lambda = m$, implying that $T$ is ergodic.
    $qed$
]

#theorem(name: "Borel's normal number theorem")[
    Lebesgue almost every number in $[0, 1)$ is normal in base $2$.
]
#proof[
    If $x = sum_(i=1)^oo (x_i)/(2^i)$, then $T(x) = sum_(i=1)^oo (x_(i+1))/(2^i)$, so $T$ shifts the binary expansion of $x$ to the left by one digit. Therefore, 
    $
    T^(i-1)(x) in cal(D)_(n,k) iff x_i = a_1, x_(i+1) = a_2, dots.c, x_(i+n-1) = a_n,
    $
    where $a_1a_2 dots.c a_n$ are the first $n$ digits of the binary expansion of $k/(2^n)$. Thus, $x$ is normal in base $2$ if and only if for every $n$ and $k$, 
    $
    lim_(l -> oo) 1/l sum_(i=0)^(l-1) chi_(cal(D)_(n,k)) (T^i (x)) = m(cal(D)_(n,k)) = 1/(2^n).
    $
    By Birkhoff's ergodic theorem, for almost every $x in [0, 1)$, the limit on the left-hand side equals the right-hand side. Therefore, almost every number in $[0, 1)$ is normal in base $2$.
    $qed$
]

== Weyl's equidistribution theorem

#lemma[
    Let $T$ be measure-preserving and let $A, B, E, F$ be measurable sets such that $A subset.eq E$, $B subset.eq F$. Then for every $n >= 0$,
    $
    mu(T^(-n)(A) inter B) >= mu(T^(-n)(E) inter F) - mu(E without A) - mu(F without B).
    $
]
#proof[
    Note that
    $
    T^(-n)(E) inter F subset.eq (T^(-n)(A) inter B) union (T^(-n)(E) without T^(-n)(A)) union (F without B),
    $
    so
    $
    mu(T^(-n)(E) inter F) &<= mu(T^(-n)(A) inter B) + mu(T^(-n)(E) without T^(-n)(A)) + mu(F without B) \
    &= mu(T^(-n)(A) inter B) + mu(E without A) + mu(F without B).
    $
    $qed$
]

#proposition[
    Let $T: [0, 1) -> [0, 1)$ be defined by
    $
    T(x) = (x + alpha) mod 1,
    $
    where $alpha$ is irrational. Then $T$ is measure-preserving and ergodic with respect to the Lebesgue measure on $[0, 1)$.
]
#proof[
    Clearly $T$ is measure-preserving. Let $E, F$ be any measurable sets with positive measure. Exists dyadic intervals $I, J$ such that
    $
    m(E inter I) > 3/4 m(I), quad m(F inter J) > 3/4 m(J).
    $
    By dividing the intervals, we may assume that $m(I) = m(J)$. Write $I = [a, b)$ and $J = [c, d)$. WLOG assume that $a <= c$. Recall that the orbit of $b$ under $T$ is dense in $[0, 1)$, so there exists $n >= 0$ such that
    $
    d - (d-c)/4 < T^n (b) < d.
    $
    Since $T$ is an isometry, $T^n (I) = [T^n (a), T^n (b))$, so
    $
    m(T^n (I) inter J) = m([T^n (a), T^n (b)) inter [c, d)) >= m([c, d - (d-c)/4)) = 3/4 m(J)]). 
    $
    By the previous lemma, taking $A = E inter I$, $B = F inter J$, $E = T^n (I)$, $F = J$, we have
    $
    mu(T^(-n)(A) inter B) &>= mu(T^(-n)(E) inter F) - mu(E without A) - mu(F without B) \
    &> 3/4 m(J) - 1/4 m(I) - 1/4 m(J) > 0.
    $

    We've concluded that if $m(E), m(F) > 0$, then there exists $n >= 1$ such that $m(T^n (E) inter F) > 0$. Now let $E$ be such that $E = T^(-1)(E)$. Set $F = E^c$. If $m(E), m(F) > 0$, then there exists $n >= 1$ such that $m(T^n (E) inter F) > 0$, contradicting the fact that $T^n (E) = E$. Therefore, $m(E) = 0$ or $1$, so $T$ is ergodic.
    $qed$
]

#corollary[
    For every interval $I subset.eq [0, 1)$, 
    $
    lim_(n -> oo) 1/n sum_(i=0)^(n-1) chi_I (T^i (x)) = m(I)
    $
    for every $x in [0, 1)$. 
]
#proof[
    By Birkhoff's ergodic theorem, given an interval $I$, exists a Lebesgue measure zero set $Z_I$ such that the above equation holds for every $x in [0, 1) without Z_I$. Consider the dyadic intervals. Since there are only countably many dyadic intervals, the union of the corresponding measure zero sets is still a measure zero set, in particular there exists $x in [0, 1)$ such that the above convergence holds for all dyadic intervals $J$. Let $I$ be an arbitrary interval and $epsilon > 0$. We can find two (disjoint unions of) dyadic intervals $J, K$ such that $J subset.eq I subset.eq K$ and $m(J) - m(K) < epsilon$. Then
    $
    sum_(i=0)^(n-1) chi_(J) (T^i (x)) <= sum_(i=0)^(n-1) chi_I (T^i (x)) <= sum_(i=0)^(n-1) chi_(K) (T^i (x)), \
    => m(J) <= liminf_(n -> oo) 1/n sum_(i=0)^(n-1) chi_I (T^i (x)) <= limsup_(n -> oo) 1/n sum_(i=0)^(n-1) chi_I (T^i (x)) <= m(K), \
    => lim_(n -> oo) 1/n sum_(i=0)^(n-1) chi_I (T^i (x)) = m(I).
    $
    Finally, for any given interval $I$ and any $y in [0, 1)$, exists an interval $I'$ such that $m(I') = m(I)$ and
    $
    T^i (y) in I iff T^i (x) in I'
    $
    for every $i >= 0$, so
    $
    lim_(n -> oo) 1/n sum_(i=0)^(n-1) chi_I (T^i (y)) = lim_(n -> oo) 1/n sum_(i=0)^(n-1) chi_(I') (T^i (x)) = m(I') = m(I).
    $
    $qed$
]

== Mean Ergodic Theorem

#theorem(name: "von Neumann")[
    Let $T$ be an isometry on a Hilbert space $X$, and let $P$ be the orthogonal projection onto the $T$-invariant subspace $Y := {x in X : T x = x}$. Let
    $
    A_n = 1/n (I + T + dots.c + T^(n-1)),
    $
    then $A_n(x) -> P(x)$ in norm for every $x in X$.
]
#proof[
    Consider the subspaces
    $
    Y_* = {x in X : T^* x = x}, quad Z = {x - T x : x in X}.
    $
    We claim that $Y = Y_*$ and $Y perp overline(Z)$. Since $T$ is an isometry, $T^* T = I$, so if $x in Y$, then
    $
    T^* x = T^* T x = x,
    $
    so $Y subset.eq Y_*$. Conversely, if $x in Y_*$, then
    $
    chevron.l x , T^* x - x chevron.r = 0 => chevron.l T x , x chevron.r = chevron.l x , x chevron.r = norm(x)^2,
    $
    so $T x = x$, and hence $Y_* subset.eq Y$. If $x in overline(Z)^perp$, then
    $
    & chevron.l x, y - T y chevron.r = 0 forall y in X \
    ==> & chevron.l x - T^* x, y chevron.r = 0 forall y in X \
    ==> & x = T^* x => x in Y_* = Y.
    $

    Let $x in X$. We can write $x = y + z$ for some $y in Y$ and $z in overline(Z)$. Fix $epsilon > 0$. Let $z' in Z$ be such that $norm(z - z') < epsilon$. Write
    $
    A_n (x) = A_n (y) + A_n (z') + A_n (z - z').
    $
    Since $T y = y$, $A_n (y) = y = P(x)$. Since $z' in Z$, we can write $z' = v - T v$ for some $v in X$, so
    $
    A_n (z') = 1/n sum_(k=0)^(n-1) (v - T v) = 1/n (v - T^n v),
    $
    and since $T$ is an isometry, $norm(A_n (z')) <= 2/n norm(v) -> 0$. Finally, $norm(A_n (z - z')) <= norm(z - z') < epsilon$. Therefore, $A_n (x) -> P(x)$ in norm.
    $qed$
]

#remark[
    Take $X = L^2(Omega, mu)$ and $Phi: Omega -> Omega$ is measure-preserving. Define $T: X -> X$ by
    $
    T f(x) = f(Phi(x)),
    $
    then $T$ is an isometry. The mean ergodic theorem implies that
    $
    1/n sum_(k=0)^(n-1) f(Phi^k (x)) -> P(f)(x)
    $
    in $L^2$ norm. If $Phi$ is ergodic, then the only $T$-invariant functions are constant functions, so $P(f)$ is the constant function with value $integral f d mu$, so this can be viewed as a generalization of Birkhoff's ergodic theorem in $L^2$ norm.
]