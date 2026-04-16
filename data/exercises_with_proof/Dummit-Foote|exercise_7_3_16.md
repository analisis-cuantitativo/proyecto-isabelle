Let $\varphi: R \rightarrow S$ be a surjective homomorphism of rings. Prove that the image of the center of $R$ is contained in the center of $S$.

Proof:
\begin{proof}

    Suppose $r \in \varphi[Z(R)]$. Then $r=\varphi(z)$ for some $z \in Z(R)$. Now let $x \in S$. Since $\varphi$ is surjective, we have $x=\varphi y$ for some $y \in R$. Now

$$

x r=\varphi(y) \varphi(z)=\varphi(y z)=\varphi(z y)=\varphi(z) \varphi(y)=r x .

$$

Thus $r \in Z(S)$.

\end{proof}
