(*<*)
theory T7ConjuntoMaximalP
imports T6CFinitoP
begin
(*>*)
section \<open> Conjuntos consistentes maximales\<close>

text \<open>
  \label{sucP}
  En esta sección precisamos en Isabelle, cómo extender un conjunto
  consistente $S$ de fórmulas proposicionales a un conjunto consistente
  maximal de acuerdo a lo expuesto en la página 61 de \cite{Fitting}.
\<close>

subsection \<open> Conjuntos maximales\<close>

text \<open>
  \begin{definicion}\label{defmaximal}
  Sea $\mathcal{C}$ una colección de conjuntos. El conjunto $S$ es un
  elemento {\bf{maximal}} de $\mathcal{C}$ si, para cualquier
  $S' \in \mathcal{C}$ tal que $S \subseteq S'$ implica que $S = S'$.
\end{definicion}

  \noindent Su formalización es:
\<close>

definition maximal :: "'a set \<Rightarrow> 'a set set \<Rightarrow> bool" where
  "maximal S \<C> = (\<forall>S'\<in> \<C>. S \<subseteq> S' \<longrightarrow> S = S')"

text \<open>
  La construcción, a partir de $S$ de un conjunto consistente maximal
  está basada en la siguiente sucesión creciente (por inclusión) de
  conjuntos.

  \begin{definicion}\label{sucesion}
  Sean $S$ un conjunto de fórmulas, $\mathcal{C}$ una colección de
  conjuntos de fórmulas y $f$ una sucesión de fórmulas.  Definimos la
  siguiente sucesión de conjuntos, $\{S^{n}_{S,\mathcal{C},f}\}_n$.
  \[
  \begin{array}{l}
   S^{0}_{S,\mathcal{C},f} = S \\
   S^{n+1}_{S,\mathcal{C},f} =
     \left\{\begin{array}{ll}
           S^{n}_{S,\mathcal{C},f} \cup \{f_n\}, &
           \mbox{si $S^{n}_{S,\mathcal{C},f} \cup \{f_n\} \in \mathcal{C}$} \\
           S^{n}_{S,\mathcal{C},f}\; , & \mbox{en otro caso.}
     \end{array}\right.
   \end{array}
  \]
  \end{definicion}

  La formalización de la sucesión $\{S^{n}_{S,\mathcal{C},f}\}_n$ es:
\<close>

primrec sucP :: "'b formula set \<Rightarrow> 'b formula set set \<Rightarrow> (nat \<Rightarrow> 'b formula) \<Rightarrow> nat \<Rightarrow> 'b formula set"
where
  "sucP S \<C> f 0 = S"
| "sucP S \<C> f (Suc n) =
    (if sucP S \<C> f n \<union> {f n} \<in> \<C>
     then sucP S \<C> f n \<union> {f n}
     else sucP S \<C> f n)"

text \<open>
  Consideremos ahora la unión de los elementos $S^{n}_{S,\mathcal{C},f}$,
  $$S_{S,\mathcal{C},f}= \bigcup_{n} S^{n}_{S,\mathcal{C},f}.$$

  \noindent Su formalización en Isabelle es:
\<close>

definition MsucP :: "'b formula set \<Rightarrow> 'b formula set set \<Rightarrow> (nat \<Rightarrow> 'b formula) \<Rightarrow> 'b formula set"
where
"MsucP S \<C> f = (\<Union>n. sucP S \<C> f n)"

text \<open>
  En lo que sigue demostraremos que para cualquier lenguaje
  proposicional $\mathbf{L}$, si $\mathcal{C}$ es una propiedad de
  consistencia proposicional de carácter finito, $S\in \mathcal{C}$ y
  $f$ es una {\em numeración} del conjunto de fórmulas de $\mathbf{L}$
  entonces, $S_{S,\mathcal{C},f}$ es un elemento maximal de
  $\mathcal{C}$ que pertenece a $\mathcal{C}$ y extiende a $S$.

  Por definición, se tiene que el conjunto $S_{S,\mathcal{C},f}$ es una
  extensión de $S$:

  \begin{teorema}\label{MaxSubconjuntoP}
  $S \subseteq S_{S,\mathcal{C},f}.$
  \end{teorema}
\<close>

(*<*)
text \<open>
  \begin{demostracion}
  Por definición,
  $S_{S,\mathcal{C},f}= \bigcup n.\, S^{n}_{S,\mathcal{C},f}$.
  Luego por propiedades de conjuntos
  $S = S^{0}_{S,\mathcal{C},f}\subseteq S_{S,\mathcal{C},f}$.
  \end{demostracion}
\<close>
(*>*)

text \<open>
  \noindent Su formalización es:

\<close>
theorem Max_subconjuntoP: "S \<subseteq> MsucP S \<C> f"
(*<*)
proof (rule subsetI)
  fix x
  assume "x \<in> S"
  hence "x \<in> sucP S \<C> f 0" by simp
  hence  "\<exists>n. x \<in> sucP S \<C> f n" by (rule exI)
  thus "x \<in> MsucP S \<C> f" by (simp add: MsucP_def)
qed
(*>*)

text \<open>

  La demostración de que $S_{S,\mathcal{C},f}$ es un elemento de
  $\mathcal{C}$ está basada en que $\mathcal{C}$ sea de carácter finito
  y que los elementos ${S^{n}_{S,\mathcal{C},f}}$ formen una cadena
  (ascendente) de elementos de $\mathcal{C}$, es decir,
  $S^{n}_{S,\mathcal{C},f} \in \mathcal{C}$ y
  $S^{n}_{S,\mathcal{C},f}\subseteq S^{n+1}_{S,\mathcal{C},f}$, para
  todo $n$.  A continuación demostraremos de forma más general, que si
  $\mathcal{C}$ es una colección de conjuntos de carácter finito
  entonces la unión de los elementos de una cadena de conjuntos de
  $\mathcal{C}$ es también un conjunto de $\mathcal{C}$.

  \begin{definicion}\label{cadena}
  Una cadena de conjuntos es cualquier sucesión $\{S_n\}_n$ de conjuntos
  ordenada por inclusión, $S_0\subseteq S_1\subseteq S_2\subseteq\ldots$.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition es_cadena :: "(nat \<Rightarrow> 'a set) \<Rightarrow> bool" where
  "es_cadena S = (\<forall>n. S n \<subseteq> S (Suc n))"

text \<open>
  La unión $\bigcup_n S_n$ de los elementos de una cadena $\{S_n\}_n$ ,
  es llamada el límite de la cadena. La propiedad fundamental de las
  colecciones de conjuntos de carácter finito es que son cerradas bajo
  límites. Es decir, si $\mathcal{C}$ es una colección de conjuntos de
  carácter finito y $\{S_n\}_n$ es una cadena de elementos de
  $\mathcal{C}$ entonces, el límite $\bigcup_n S_n\in \mathcal{C}$.
\<close>

(*<*)
text \<open>
  Para la demostración de esta propiedad, usamos el siguiente lema.

  \begin{lema}\label{indicecadena}
  Sea $\{S_n\}_n$ una cadena y $A$ un conjunto finito. Supongamos que
  $A\subseteq \bigcup_n S_n$ entonces, $A\subseteq S_n$ para algún $n$.
  \end{lema}

  \begin{demostracion}
  La demostración es por inducción finita sobre $A$.

  {\bf{Caso base}}. Sea $A=\emptyset$, se tiene trivialmente que
  $\emptyset \subseteq S_n$ para cualquier $n$.

  {\bf{Paso de inducción}}. Hipótesis de inducción: sea $A$ un conjunto
  finito, si $A\subseteq \bigcup_n S_n$ entonces $A\subseteq S_n$ para
  algún $n$. Hay que demostrar que si
  $A\cup\{x\} \subseteq \bigcup_n S_n$, en donde $x\notin A$, entonces
  $A\cup\{x\} \subseteq S_n$ para algún $n$.

  Supongamos que $A\cup\{x\} \subseteq \bigcup_n S_n$ en donde
  $x\notin A$.  Entonces $x\in S_m$ para algún $m$ y
  $A\subseteq \bigcup_nS_n$. Por lo tanto, $x\in S_m$ para algún $m$ y,
  por hipótesis de inducción, $A \subseteq S_n$ para algún $n$. Sea $r$
  el máximo entre $m$ y $n$ entonces, como $f$ es una cadena, es fácil
  demostrar que $S_m\subseteq S_r$ y $S_n\subseteq S_r$. Luego,
  $A \subseteq S_r$ y $x\in S_r$. Así, $A \cup\{x\}\subseteq S_r$.
  \end{demostracion}

  Para la formalización del lema anterior, demostramos los siguientes
  dos resultados preliminares.
\<close>
(*>*)

(*<*)
lemma es_cadenaD:
  assumes "es_cadena S" and "x \<in> S m"
  shows "x \<in> S (m + n)"
proof -
  show ?thesis using assms by (induct n)(auto simp add: es_cadena_def)
qed

lemma es_cadenaD':
  assumes hip1: "es_cadena S" and hip2: "x \<in> S m" and hip3: "m \<le> k"
  shows "x \<in> S k"
proof -
  have "\<exists>n. k = m + n" using hip3 by arith
  then obtain n where n: "k = m + n" by (rule exE)
  moreover
  have "x \<in> S (m + n)" using hip1 hip2 by (rule es_cadenaD)
  thus ?thesis using n by simp
qed

lemma cadena_indice:
  assumes ch: "es_cadena S" and fin: "finite F"
  shows "F \<subseteq> (\<Union>n. S n) \<Longrightarrow> \<exists>n. F \<subseteq> S n" using fin
proof (induct rule: finite_induct)
  assume "{} \<subseteq> (\<Union>n. S n)"
  show "\<exists>n.{} \<subseteq> S n"  by simp
  next
    fix x F
    assume
      h1: "finite F"
      and h2: "x \<notin> F"
      and h3: "F \<subseteq> (\<Union>n. S n)\<Longrightarrow> \<exists>n. F \<subseteq> S n"
      and h4: "insert x F \<subseteq> (\<Union>n. S n)"
  show "\<exists>n. insert x F \<subseteq> S n"
  proof -
    have "\<exists>m. x \<in> S m" using h4 by simp
    then obtain m where m: "x \<in> S m" by (rule exE)
    have "F \<subseteq> (\<Union>n. S n)" using h4 by simp
    hence  "\<exists>n. F \<subseteq> S n" using h3 by simp
    then obtain n where n: "F \<subseteq> S n" by (rule exE)
    have "m \<le> (max m n)"  by (simp add: max_def)
    with ch m  have 1: "x \<in> S (max m n)" by (rule es_cadenaD')
    have 2:  "F \<subseteq> S (max m n)"
    proof (rule subsetI)
      fix y
      assume "y \<in> F"
      hence "y \<in> S n" using n by blast
      moreover
      have "n \<le> (max m n)" by simp
      ultimately
      show "y \<in> S (max m n)"  by (rule es_cadenaD'[OF ch _ _])
    qed
    have "insert x F  \<subseteq> S (max m n)" using 1 2 by simp
    thus ?thesis by (rule exI)
  qed
qed
(*>*)

text \<open>
  \begin{teorema}\label{limitecadenaP}
  Si $\mathcal{C}$ es una colección de conjuntos de carácter finito y
  $\{S_n\}_n$ es una cadena de elementos de $\mathcal{C}$ entonces, el
  límite de $\{S_n\}_n$ pertenece a $\mathcal{C}$.
  \end{teorema}
\<close>

(*<*)
text \<open>
  \begin{demostracion}

  Puesto que $\mathcal{C}$ es de carácter finito, para mostrar que
  $\bigcup_n S_n\in \mathcal{C}$, es suficiente mostrar que cada
  subconjunto finito de $\bigcup_n S_n$ pertenece a
  $\mathcal{C}$. Supongamos que $T$ es un conjunto finito y
  $T\subseteq \bigcup_n S_n$. Entonces, como $\{S_n\}_n$ es una cadena,
  por el lema \ref{indicecadena} existe $n$ tal que $T\subseteq S_n$ y
  como por hipótesis $S_n\in \mathcal{C}$ entonces se tiene que
  $T \in S_n$, ya que $\mathcal{C}$ es cerrada por subconjuntos por ser
  de carácter finito (teorema \ref{CaracterFinitoCerrada}).
  \end{demostracion}
\<close>

(*>*)
text\<open>
  \noindent Su formalización es:
\<close>

theorem cadena_union_cerrado:
  assumes hip1: "caracter_finito \<C>"
  and hip2:"es_cadena S"
  and hip3: "\<forall>n. S n \<in> \<C>"
  shows "(\<Union>n. S n) \<in> \<C>"
(*<*)
proof -
  have "\<forall>S. (S \<in> \<C>) = (\<forall>T. finite T \<longrightarrow> T \<subseteq> S \<longrightarrow> T \<in> \<C>)"
  using hip1 by (unfold caracter_finito_def)
  hence 1: "(\<Union>n. S n) \<in> \<C> = (\<forall>T. finite T \<longrightarrow> T \<subseteq> (\<Union>n. S n) \<longrightarrow> T \<in> \<C>)"
  by (rule allE)
  thus "(\<Union>n. S n) \<in> \<C>"
  proof -
    have "(\<forall>T. finite T \<longrightarrow> T \<subseteq> (\<Union>n. S n) \<longrightarrow> T \<in> \<C>)"
    proof (rule allI impI)+
      fix T
      assume h1: "finite T" and h2: "T \<subseteq> (\<Union>n. S n)"
      have "\<exists>n. T \<subseteq> S n" using hip2 h1 h2 by (rule cadena_indice)
      moreover
      have "subconj_cerrada \<C>" using hip1 by (rule caracter_finito_cerrado)
      hence "\<forall>S\<in>\<C>. \<forall>S'\<subseteq>S. S' \<in> \<C>"  by (unfold subconj_cerrada_def)
      ultimately
      show "T \<in> \<C>" using hip3 by auto
    qed
    thus "(\<Union>n. S n) \<in> \<C>" using 1 by simp
  qed
qed
(*>*)

text \<open>
  De esta forma, para demostrar que
  $\bigcup_{n} S^{n}_{S,\mathcal{C},f}\in \mathcal{C}$ como consecuencia
  del teorema anterior, basta probar que los elementos
  $S^{n}_{S,\mathcal{C},f}$ forman una cadena de elementos de $\mathcal{C}$.

  \begin{lema}\label{cadenasucP}
  Sean $S$ un conjunto de fórmulas, $\mathcal{C}$ una colección de
  conjuntos de fórmulas y $f$ una sucesión de fórmulas. Entonces, la
  sucesión $\{S^{n}_{S,\mathcal{C},f}\}_n$ es una cadena.
  \end{lema}

  \noindent Su formalización es:
\<close>

(*<*)
text \<open>
  \begin{demostracion}
  Por la definición de $S^{n}_{S,\mathcal{C},f}$, se tiene que
  $\forall n. S^{n}_{S,\mathcal{C},f} \subseteq S^{n+1}_{S,\mathcal{C},f}$.
  Por lo tanto, por definición de cadena, la sucesión
  $S^{n}_{S,\mathcal{C},f}}$ es una cadena.
  \end{demostracion}
\<close>

(*>*)

lemma es_cadena_suc: "es_cadena (sucP S \<C> f)"
by (simp add: es_cadena_def) blast

text \<open>
  Por último formalizamos el siguiente teorema que afirma que si
  $\mathcal{C}$ es una propiedad de consistencia de carácter finito y
  $S$ está en $\mathcal{C}$ entonces, $S_{S,\mathcal{C},f}$ también está
  en $\mathcal{C}$.

  \begin{teorema}\label{MaxP-in-C}
  Si $\mathcal{C}$ es una propiedad de consistencia proposicional de
  carácter finito, $S\in \mathcal{C}$ y $f$ una sucesión de fórmulas,
  entonces $S_{S,\mathcal{C},f}\in \mathcal C$.
  \end{teorema}

  \begin{demostracion}
  Por el lema \ref{cadenasucP}, $\{S^{n}_{S,\mathcal{C},f}\}_n$ es una
  cadena. Además, de la hipótesis $S\in \mathcal{C}$, por inducción se
  demuestra que $S^{n}_{S,\mathcal{C},f}\in \mathcal{C}$, para todo
  $n$. De lo anterior y como $\mathcal{C}$ es una colección de carácter
  finito, usando el lema \ref{limitecadenaP} se concluye que
  $S_{S,\mathcal{C},f} \in \mathcal{C}$.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

theorem MaxP_en_C:
  assumes hip1: "caracter_finito \<C>" and hip2: "S \<in> \<C>"
  shows  "MsucP S \<C> f \<in> \<C>"
proof (unfold MsucP_def)
  have "es_cadena (sucP S \<C> f)" by (rule es_cadena_suc)
  moreover
  have "\<forall>n. sucP S \<C> f n \<in> \<C>"
  proof (rule allI)
    fix n
    show "sucP S \<C> f n \<in> \<C>" using hip2
      by (induct n)(auto simp add: sucP_def)
  qed
  ultimately
  show "(\<Union> n. sucP S \<C> f n) \<in> \<C>" by (rule cadena_union_cerrado[OF hip1])
qed

text \<open>
  Para demostrar que $S_{S,\mathcal{C},f}$ es un elemento maximal de
  $\mathcal{C}$ no es necesario que $\mathcal{C}$ sea de carácter
  finito, sólo es necesario suponer que la colección $\mathcal{C}$ sea
  cerrada por subconjuntos. Sin embargo la sucesión $f$ de fórmulas debe
  corresponder a una {\em enumeración} del conjunto de fórmulas del
  lenguaje proposicional que estemos considerando. Así, en el siguiente
  teorema demostramos que si tenemos una enumeración del conjunto de
  fórmulas de un lenguaje proposicional entonces, para cualquier
  colección de conjuntos de fórmulas $\mathcal{C}$ que sea cerrada por
  subconjuntos, se tiene que el límite $S_{S,\mathcal{C},f}$, es un
  elemento maximal de $\mathcal{C}$.

 \begin{definicion}\label{enumerar}
Un conjunto $A$ es \textbf{enumerable} si es vacío o existe una función sobreyectiva
$f\colon \mathbb{N}\to A$ del conjunto de los números naturales en el conjunto $A$.
 En este caso, se dice que $f$ es una enumeración de $A$, y se puede listar como una sucesión infinita:
$f(0),f(1),f(2), \ldots , $
en la cual aparecen todos los elementos de $A$, con posibles repeticiones, y solo elementos de $A$.
En particular, cualquier conjunto finito es enumerable.
\par\par
\end{definicion}

  \noindent Su formalización es:
\<close>

definition enumeracion :: "(nat \<Rightarrow>'b) \<Rightarrow> bool" where
  "enumeracion f = (\<forall>y.\<exists>n. y = (f n))"

text \<open>
  Por ejemplo, la función identidad $i\colon \mathbb{N}\to \mathbb{N}$
  es sobreyectiva. Luego es una numeración de $\mathbb{N}$.

  \begin{lema}\label{enumidentidad}
  Existe una enumeración $g$ de $\mathbb{N}$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma enum_nat: "\<exists>g. enumeracion (g:: nat \<Rightarrow> nat)"
proof -
  have "\<forall>y. \<exists> n. y = (\<lambda>n. n) n" by simp
  hence "enumeracion (\<lambda>n. n)" by (unfold enumeracion_def)
  thus ?thesis by auto
qed

text \<open>
  \begin{teorema}\label{suc-maximalP}
  Sean $\mathbf{L}$ un lenguaje proposicional, $S$ un conjunto de
  fórmulas de $\mathbf{L}$, $\mathcal{C}$ una colección de conjuntos de
  fórmulas de $\mathbf{L}$ cerrada por subconjuntos y $f$ una enumeración
  del conjunto de fórmulas de $\mathbf{L}$. Entonces
  $S_{S,\mathcal{C},f}$ es un elemento maximal de $\mathcal{C}$.
  \end{teorema}

  \begin{demostracion}

  Sea $S'\in \mathcal{C}$. Supongamos que
  $S_{S,\mathcal{C},f} \subseteq S'$, entonces $\forall n$
  $S^{n}_{S,\mathcal{C},f} \subseteq S'$. Demostramos por contradicción
  que $\bigcup_{n} S^{n}_{S,\mathcal{C},f} = S'$.  Supongamos que
  $\bigcup_{n} S^{n}_{S,\mathcal{C},f} \neq S'$. Entonces, existe
  $z\in S'$ tal que $z\notin \bigcup_{n} S^{n}_{S,\mathcal{C},f}$.
  Luego, existe $n$ tal que $z=f_n$, puesto que $f$ es una numeración
  del conjunto de fórmulas.  Por lo tanto, $f_n\in S'$ y como
  $S^{n}_{S,\mathcal{C},f} \subseteq S'$, tenemos que
  $S^{n}_{S,\mathcal{C},f} \cup \{f_n\}\subseteq S'$. Luego,
  $S^{n}_{S,\mathcal{C},f} \cup \{f_n\}\in \mathcal{C}$, puesto que
  $\mathcal{C}$ es cerrada por subconjuntos y $S'\in \mathcal{C}$. Así,
  por definición de la sucesión
  $S^{n}_{S,\mathcal{C},f}$, $f_n \in S^{n+1}_{S,\mathcal{C},f}$.
  Por otro lado, $f_n \notin S^{n+1}_{S,\mathcal{C},f}$, ya que
  $f_n=z$ y por hipótesis $z\notin \bigcup_{n} S^{n}_{S,\mathcal{C},f}$.
  De esta forma obtenemos una contradicción.
  \end{demostracion}

  \noindent Su formalización es:
\<close>

theorem suc_maximalP:
  assumes hip1: "enumeracion f" and hip2: "subconj_cerrada \<C>"
  shows "maximal (MsucP S \<C> f) \<C>"
proof (simp add: maximal_def MsucP_def)
  show "\<forall>S'\<in>\<C>. (\<Union>x. sucP S \<C> f x) \<subseteq> S' \<longrightarrow> (\<Union>x. sucP S \<C> f x) = S'"
  proof (rule ballI impI)+
    fix S'
    assume h1: "S' \<in> \<C>" and h2: "(\<Union>x. sucP S \<C> f x) \<subseteq> S'"
    show "(\<Union>x. sucP S \<C> f x) = S'"
    proof (rule ccontr)
      assume "(\<Union>x. sucP S \<C> f x) \<noteq> S'"
      hence  "\<exists>z. z \<in> S' \<and> z \<notin> (\<Union>x. sucP S \<C> f x)" using h2 by blast
      then obtain z where z: "z \<in> S' \<and> z \<notin> (\<Union>x. sucP S \<C> f x)" by (rule exE)
      have "\<exists>n. z = f n" using hip1 h1 by (unfold enumeracion_def) simp
      then obtain n where n: "z = f n" by (rule exE)
      have "sucP S \<C> f n \<union> {f n} \<subseteq> S'"
      proof -
        have "f n \<in> S'" using z n  by simp
        moreover
        have "sucP S \<C> f n \<subseteq> (\<Union>x. sucP S \<C> f x)" by auto
        ultimately
        show ?thesis using h2 by simp
      qed
      hence "sucP S \<C> f n \<union> {f n} \<in> \<C>"
        using h1 hip2 by (unfold subconj_cerrada_def) simp
      hence "f n \<in> sucP S \<C> f (Suc n)" by simp
      moreover
      have "\<forall>x. f n \<notin> sucP S \<C> f x" using z n by simp
      hence "f n \<notin> sucP S \<C> f (Suc n)" by (rule_tac x = "Suc n" in allE)
      ultimately
      show False by simp
    qed
  qed
qed

text \<open>
  \begin{corolario}\label{ExtensionConsistenteP}
  Sean $\mathbf{L}$ un lenguaje proposicional, $\mathcal{C}$ una
  colección de conjuntos de fórmulas de $\mathbf{L}$ de carácter finito,
  $S$ un elemento de $\mathcal{C}$ y $f$ una enumeración del conjunto de
  fórmulas de $\mathbf{L}$. Entonces,
  \begin{itemize}
  \item[(a)] $S\subseteq S_{S,\mathcal{C},f}$.
  \item[(b)] $S_{S,\mathcal{C},f} \in \mathcal{C}$.
  \item[(c)] $S_{S,\mathcal{C},f}$ es un elemento maximal de $\mathcal{C}$.
  \end{itemize}
  \end{corolario}

  \begin{demostracion}
  \begin{itemize}
  \item[(a)] Por el teorema \ref{MaxSubconjuntoP}.

  \item[(b)] Por el teorema \ref{MaxP-in-C}, pues $\mathcal{C}$ es de
  carácter finito y $S$ está en $\mathcal{C}$.

  \item[(c)] Dado que $\mathcal{C}$ es de carácter finito, por el teorema
  \ref{CaracterFinitoCerradaP}, se tiene que $\mathcal{C}$ es cerrada
  por subconjuntos. De esto último y puesto que $f$ es una enumeración
  del conjunto de fórmulas de $\mathbf{L}$, por el teorema
  \ref{suc-maximalP}, obtenemos $(c)$.
  \end{itemize}
  \mbox{}
  \end{demostracion}

  \noindent Su formalización es:
\<close>

corollary ExtensionConsistenteP:
  assumes hip1: "caracter_finito \<C>"
  and hip2: "S \<in> \<C>"
  and hip3:  "enumeracion f"
  shows "S \<subseteq> MsucP S \<C> f"
  and "MsucP S \<C> f \<in> \<C>"
  and "maximal (MsucP S \<C> f) \<C>"
proof -
  show "S \<subseteq> MsucP S \<C> f" using Max_subconjuntoP by auto
next
  show "MsucP S \<C> f \<in> \<C>" using  MaxP_en_C[OF hip1 hip2] by simp
next
  show "maximal (MsucP S \<C> f) \<C>"
    using caracter_finito_cerrado[OF hip1] and hip3 suc_maximalP
    by auto
qed

(*<*)
end
(*>*)
