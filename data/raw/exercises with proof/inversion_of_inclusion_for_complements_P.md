let $A$ and $B$ subsets of a Universal set R, then $A \subseteq B$ if and only if $ B^{c} \subseteq A^{c}$

Proof: $\Rightarrow)$ if $x\in B^c$, then $x \in R$ and $ x \notin B$. This implies that $x \notin A$, because if $x \in A$ then $x \in B$, which is a contradiction. Thus,  we obtain $x\in R$ and $ x \notin A$, which means $A^c$.Therefore, $B^c \subseteq A^c$.

$\Leftarrow)$ By contradiction, suppose that $B^c \subseteq A^c$ and $A \not\subseteq B$, then there exista an element $y \in A$ such that $ y \notin B$. since $A$ is a subset of $R$, we have $y \in R$ and $y \notin B$, this means $y \in B^c$. By the hypothesis, it follows that $y \in A^c$, then $y \notin A$, and this is a contradiction because we assumed $y \in A$. Therefore, $A \subseteq B$
