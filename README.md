# Zeckendorf's Theorem

This work formalizes Zeckendorf's theorem in Isabelle/HOL. The theorem states that every positive integer can be uniquely represented as a sum of one or more non-consecutive Fibonacci numbers. More precisely, if 
$N$ is a positive integer, there exist unique positive integers $c_i \ge 2$ with $c_i + 1 < c_{i+1}$, such that
$
\begin{equation}
    N = \sum_{i=0}^{k} F_{c_i} \nonumber
\end{equation}
$
where $F_n$ is the $n$-th Fibonacci number.