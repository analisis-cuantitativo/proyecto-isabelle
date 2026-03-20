(*<*)
theory T11EnumFormulasP
imports T10MaximalHintikkaP EnumArbolesBinariosP
begin
(*>*)

subsection \<open> Enumeración de fórmulas proposicionales \<close>

text \<open>

  Para enumerar las fórmulas de un lenguaje proposicional, mostramos
  inicialmente cómo asignar una fórmula a cada árbol binario que sea una
  hoja con valor $n\geq 0$ y, de forma recursiva, a cada árbol binario
  cuyo hijo izquierdo esté compuesto por una hoja con valor entre 0 y 4,
  del cual dependerá el tipo de fórmula que se le asocie.

  Sea $g$ una sucesión de símbolos proposicionales:
 \begin{enumerate}
  \item
  \begin{enumerate}
    \qtreecenterfalse
    \item Al árbol compuesto por la hoja 0 le corresponde la fórmula $\bot$.
    \item Al árbol compuesto por la hoja 1 le corresponde la fórmula $\top$.
    \item Al árbol compuesto por la hoja $n+2$  le corresponde la
      fórmula atómica $P$, donde $g(n)= P.$
    \end{enumerate}
  \item
   \begin{enumerate}
    \item Al árbol,
      {\begin{center}
       \qtreecenterfalse
      \Tree [ $n$  [ \qroof{árbol  binario $T_1$}.{\textbullet}
                     \qroof{árbol  binario $T_2$}.{\textbullet} ] ]
       \end{center}}
      le corresponde una de las fórmulas $F \wedge G$, $F \vee G$,
      $F \rightarrow G$ dependiendo si $n=1$, $n=2$ ó $n=3$,
      respectivamente. Donde $F,G$ son las fórmulas corres\-pondientes a
      los árboles $T_1, T_2$.
    \item Al árbol,
      {\begin{center}
        \qtreecenterfalse
        \Tree [ $4$   \qroof{árbol  binario $T$}.{\textbullet} ]
       \end{center}}
      le corresponde la fórmula $\neg F$. Donde $F$ es la fórmula
      correspondiente al árbol $T$.
   \end{enumerate}
  \end{enumerate}

  Obsérvese que no todos los árboles binarios tienen una fórmula asociada.
  La si\-guiente función {\em parcial} formaliza la correspondencia
  anterior.
\<close>

fun formulaP_del_arbolb :: "(nat \<Rightarrow> 'b) \<Rightarrow> arbolb \<Rightarrow> 'b formula" where
  "formulaP_del_arbolb g (Hoja 0) = FF"
| "formulaP_del_arbolb g (Hoja (Suc 0)) = TT"
| "formulaP_del_arbolb g (Hoja (Suc (Suc n))) = (Atomo (g n))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc 0)) (Arbol T1 T2)) =
   ((formulaP_del_arbolb g T1) \<and>. (formulaP_del_arbolb g T2))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc (Suc 0))) (Arbol T1 T2)) =
   ((formulaP_del_arbolb g T1) \<or>. (formulaP_del_arbolb g T2))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc (Suc (Suc 0)))) (Arbol T1 T2)) =
   ((formulaP_del_arbolb g T1) \<rightarrow>. (formulaP_del_arbolb g T2))"
| "formulaP_del_arbolb g (Arbol (Hoja (Suc (Suc (Suc (Suc 0))))) T) =
   (\<not>. (formulaP_del_arbolb g T))"
(*<*)

lemma "formulaP_del_arbolb  (\<lambda>n. n) (Hoja  0) = FF"
by simp
(*
normal_form
  "formulaP_del_arbolb (\<lambda>n. n) (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0)))"
*)
lemma
  "formulaP_del_arbolb
   (\<lambda>n. n) (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0))) = FF \<and>. FF"
by simp
(*
normal_form
  "formulaP_del_arbolb g (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0)))"
*)
lemma
  "formulaP_del_arbolb g (Arbol (Hoja (Suc 0)) (Arbol (Hoja 0) (Hoja 0)))
   = FF \<and>. FF"
by simp
(*
normal_form  "formulaP_del_arbolb (\<lambda>n. n) (Hoja  0) = FF"
normal_form  "formulaP_del_arbolb (\<lambda>n. n) (Hoja  0)"
normal_form
  "formulaP_del_arbolb
   (\<lambda>n. n) (Arbol (Hoja (Suc (Suc (Suc (Suc 0))))) (Hoja 0))"
*)
lemma
  "formulaP_del_arbolb
  (\<lambda>n. n) (Arbol (Hoja (Suc (Suc (Suc (Suc 0))))) (Hoja 0)) = (\<not>. FF)"
by simp
(*>*)

text \<open>
  De manera recíproca, la siguiente función formaliza la inversa de la
  correspon\-dencia anterior: dada una función $g$ del conjunto de símbolos
  proposicionales al conjunto de números naturales, a cada fórmula
  proposicional se le asigna un árbol binario.
\<close>

primrec arbolb_de_la_formulaP :: "('b \<Rightarrow> nat) \<Rightarrow>  'b formula \<Rightarrow> arbolb" where
  "arbolb_de_la_formulaP  g FF = Hoja 0"
| "arbolb_de_la_formulaP g TT = Hoja (Suc 0)"
| "arbolb_de_la_formulaP g (Atomo P) = Hoja (Suc (Suc (g P)))"
| "arbolb_de_la_formulaP g (F \<and>. G) = Arbol (Hoja (Suc 0))
   (Arbol (arbolb_de_la_formulaP g F) (arbolb_de_la_formulaP g G))"
| "arbolb_de_la_formulaP g (F \<or>. G) = Arbol (Hoja (Suc (Suc 0)))
   (Arbol (arbolb_de_la_formulaP g F) (arbolb_de_la_formulaP g G))"
| "arbolb_de_la_formulaP g (F \<rightarrow>. G) = Arbol (Hoja (Suc (Suc (Suc 0))))
   (Arbol (arbolb_de_la_formulaP g F) (arbolb_de_la_formulaP g G))"
| "arbolb_de_la_formulaP g (\<not>. F) = Arbol (Hoja (Suc (Suc (Suc (Suc 0)))))
   (arbolb_de_la_formulaP g F)"

text \<open>
  Con base a lo anterior, y usando la enumeración @{text "diag_arbolb"}
  del conjunto de árboles binarios, tenemos que en cualquier lenguaje
  proposicional y por cada enumeración $g$ del conjunto $\mathcal{P}$ de
  símbolos proposicionales, podemos construir una enumeración $\Delta_{g}$ del
  co\-rrespondiente conjunto de fórmulas $\mathcal{F}$:

  \begin{definicion}\label{enumformulasP}
  La función $\Delta_{g} : \mathbb{N} \to \mathcal{F}$ está definida
  por,
  $$\Delta_{g}(n) =
    (formulaP\mbox{-}de\mbox{-}arbolb\ g)(diag\mbox{-}arbolb\ n).$$
  \end{definicion}

  \begin{teorema}\label{enumformulas1}
  Sea $g:\mathbb{N} \to \mathcal{P}$ una enumeración de los símbolos
  proposicionales del lenguaje $\mathbf{L}$. Entonces, $\Delta_{g}$ es
  una enumeración del conjunto de fórmulas de $\mathbf{L}$.
  \end{teorema}

  \begin{demostracion}
  Por hipótesis y el lema \ref{enumera}, existe $g':\mathcal{P}\to
  \mathbb{N}$ inversa a derecha de $g$. Entonces, la función
  $\Delta'_{g'} : \mathcal{F}\to \mathbb{N}$ definida por,
  $$\Delta'_{g'}(F) = undiag\mbox{-}arbolb\
  (arbolb\mbox{-}de\mbox{-}la\mbox{-}formulaP\ g'\ F),$$ es inversa por
  derecha de $\Delta_{g}$. Es decir, $\Delta_{g}(\Delta'_{g'}(F)) = F$
  para toda fórmula $F$.
  \end{demostracion}

  Para la formalización del teorema anterior, definimos en Isabelle la
  función $\Delta_{g}$ y su inversa $\Delta'_{g}$ de la siguiente manera.
\<close>

definition \<Delta>P :: "(nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> 'b formula" where
  "\<Delta>P g n = formulaP_del_arbolb g (diag_arbolb n)"

definition \<Delta>P' :: "('b \<Rightarrow> nat) \<Rightarrow> 'b formula \<Rightarrow> nat" where
  "\<Delta>P' g' F = undiag_arbolb (arbolb_de_la_formulaP g' F)"

theorem enumeracionformulasP[simp]:
  assumes "\<forall>x. g(g' x) = x"
  shows "\<Delta>P g (\<Delta>P' g' F) = F"
using assms
by (induct F)(simp_all add: \<Delta>P_def \<Delta>P'_def)

text \<open>
  Los siguientes corolarios muestran otras formas de expresar la
  propiedad de enumerabilidad anterior.

  \begin{corolario}\label{enumformulasP}
  Sea $g:\mathbb{N} \to \mathcal{P}$ tal que, $\forall P \exists n\, (P
  = g(n))$. Entonces, $\forall F \exists n\, (F = \Delta_{g}(n))$.
  \end{corolario}

\begin{demostracion}
  Sea $g':\mathcal{P} \to \mathbb{N}$ definida de la siguiente manera:
  dado $P\in \mathcal{P}$, definimos $g'(P)=n$, donde $n$ es tal que $P
  = g(n)$.

  De las definición anterior se tiene que $g(g'(P)) = P$ para todo $P\in
  \mathcal{P}$. Luego, por el teorema anterior, $\Delta_{g}
  (\Delta'_{g'}(F))=F$ para toda fórmula $F$. De esta forma, para toda
  fórmula $F$ existe $n$ tal que, $F = \Delta_{g}(n)$, donde
  $n=\Delta'_{g'}(F)$.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

corollary EnumeracionFormulasP:
  assumes "\<forall>P. \<exists> n. P = g n"
  shows "\<forall>F. \<exists>n. F = \<Delta>P g n"
proof (rule allI)
  fix F
  { have "\<forall>P. P = g (SOME n. P = (g n))"
    proof(rule allI)
      fix P
      obtain n where n: "P=g(n)" using assms by auto
      thus "P = g (SOME n. P = (g n))" by (rule someI)
    qed }
  hence "\<forall>P. g((\<lambda>P. SOME n. P = (g n)) P) = P" by simp
  hence "F = \<Delta>P g (\<Delta>P' (\<lambda>P. SOME n. P = (g n)) F)"
    using enumeracionformulasP by simp
  thus "\<exists>n. F = \<Delta>P g n"
    by (rule_tac x= "(\<Delta>P' (\<lambda>P. SOME n. P = (g n)) F)" in exI)
qed

text \<open>
  \begin{corolario}\label{EnumeracionFormulas}
  Si $g:\mathbb{N} \to \mathcal{P}$ es una enumeración del conjunto de
  símbolos proposicionales $\mathcal{P}$ de un lenguaje $\mathbf{L}$,
  entonces la función $\Delta_{g} : \mathbb{N} \to \mathcal{F}$
  (definición \ref{enumformulasP}) es una enumeración del
  corres\-pondiente conjunto de fórmulas proposicionales $\mathcal{F}$.
  \end{corolario}

  \begin{demostracion}
  Es consecuencia del corolario anterior y la definición de enumeración.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

corollary EnumeracionFormulasP1:
  assumes "enumeracion (g:: nat \<Rightarrow> 'b)"
  shows "enumeracion ((\<Delta>P g):: nat \<Rightarrow> 'b formula)"
proof -
  have "\<forall>P. \<exists> n. P = g n" using assms by(unfold enumeracion_def)
  hence "\<forall>F. \<exists>n. F = \<Delta>P g n" using EnumeracionFormulasP by auto
  thus ?thesis by(unfold enumeracion_def)
qed
text\<open> Por ejemplo,
\begin{corolario}\label{EnumeracionFormulasNat}
El lenguaje proposicional con símbolos proposicionales
los números naturales es enumerable.
\end{corolario}
\begin{demostracion}
Puesto que la función identidad es una enumeración de los números
naturales (\ref{enumidentidad}), por el teorema anterior, se tiene el resultado.
\end{demostracion}
\<close>
corollary EnumeracionFormulasNat:
  shows "\<exists> f. enumeracion (f:: nat \<Rightarrow> nat formula)"
  proof -
    obtain g where g: "enumeracion (g:: nat \<Rightarrow> nat)" using enum_nat by auto
    thus  "\<exists> f. enumeracion (f:: nat \<Rightarrow> nat formula)"
      using  enum_nat EnumeracionFormulasP1 by auto
qed
(*<*)
end
(*>*)
