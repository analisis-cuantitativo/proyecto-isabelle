Let me think about this problem. We need to prove that a function f: A → B is injective if and only if there exists a function g: B → A such that g ∘ f = id_A.

The forward direction: If f is injective, then we can construct g such that g(f(a)) = a for all a in A. For elements in B that are not in the image of f, we can choose an arbitrary value (if A is non-empty).

The backward direction: If there exists g such that g ∘ f = id_A, then f is injective because if f(a₁) = f(a₂), then g(f(a₁)) = g(f(a₂)), which means a₁ = a₂.

In Isabelle, I'll need to formalize this carefully. The tricky part is the forward direction where we need to construct g. We'll need to handle the case where A might be empty or not.

Let me write the Isabelle proof:
