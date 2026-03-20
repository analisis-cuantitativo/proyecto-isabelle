
(*<*)
theory T1SintaxisSemanticaP
imports Main
begin
(*>*)

text \<open>
  \label{cap4}
\<close>

section \<open> Sintaxis y semántica proposicional \<close>

text \<open>
  \label{sintaxsemanticaP}
  En la lógica proposicional que estudiaremos, las fórmulas se construiran a partir de las
  conectivas  @{text "\<bottom>, \<top>, \<not>, \<and>, \<or>, \<longrightarrow>"}.
  Más precisamente, la sintaxis y semántica de los lenguajes
  proposicionales que consi\-deraremos y su formalización es la siguiente.

  \begin{definicion}
    El \textbf{alfabeto} de un lenguaje proposicional se compone de los
    siguientes símbolos.
    \begin{enumerate}
      \item \textbf{Símbolos lógicos:}
        \begin{itemize}
          \item conectivas: @{text "\<bottom>, \<top>, \<not>, \<and>, \<or>, \<longrightarrow>"}
          \item símbolos de puntuación: '(' , ')'\, , ','
        \end{itemize}
     \item \textbf{Símbolos no lógicos:}
         \begin{itemize}
           \item símbolos proposicionales $P_0, P_1, \dots$
         \end{itemize}
   \end{enumerate}
  \end{definicion}
  Las {\em fórmulas} de un lenguaje proposicional se definen de la
  si\-guiente manera.
   \begin{definicion}
     El conjunto de {\bf{fórmulas}} es el conjunto más pequeño que
      satisface las si\-guientes condiciones:
         \begin{enumerate}
           \item Los símbolos $\bot$ y $\top$ son fórmulas.
           \item Cualquier símbolo proposicional es una fórmula.
           \item Si $F$ es una fórmula, entonces $\neg F$ es
                 una fórmula.
           \item Si $F$ y $G$ son fórmulas, entonces
                  $(F \wedge G), (F \vee G), (F \rightarrow G)$ son fórmulas.
        \end{enumerate}
  \end{definicion}
  Los símbolos proposicionales son llamados {\bf{fórmulas atómicas}}.

  El siguiente tipo de datos define en Isabelle las fórmulas de un
  lenguaje proposicional.
\<close>

datatype 'b formula =
    FF
  | TT
  | Atomo 'b                 (* ("P_" [1000]) *)
  | Nega "'b formula"                   ("\<not>.(_)" [110] 110)
  | Conju "'b formula" "'b formula"    (infixl "\<and>."  109)
  | Disya "'b formula" "'b formula"    (infixl "\<or>."  108)
  | Implica "'b formula" "'b formula" (infixl "\<rightarrow>." 100)

text \<open>
  \begin{nota}
    En la representación de las fórmulas se observa que:
    \begin{enumerate}
      \item El tipo de dato genérico $'b$ representa los símbolos
        proposicionales del lenguaje.
      \item para distinguir el lenguaje objeto del metalenguaje, se ha
        puesto un punto al final de las conectivas del lenguaje objeto.
      \item La negación tiene precedencia sobre el condicional.
      \item El condicional asocia por la izquierda.
    \end{enumerate}
 \end{nota}
Con estos convenios, se tiene por ejemplo, el siguiente lema.
\<close>

lemma "(\<not>.\<not>. Atom P \<rightarrow>. Atom Q  \<rightarrow>. Atom R) =
       (((\<not>. (\<not>. Atom P)) \<rightarrow>. Atom Q) \<rightarrow>. Atom R)"
by simp

text \<open>
  En lo que sigue  presentamos la formalización de los conceptos
  semánticos de la lógica proposicional.  Comenzamos formalizando el
  concepto del valor de una fórmula en una interpretación (\ref{valor}),
  para lo que se necesitan los conceptos de valores de verdad
  (\ref{vverdad}) y de interpretaciones (\ref{interpretacion}).
  \label{semanticap}

  \begin{definicion}\label{vverdad}
    Los \textbf{valores de verdad} de la lógica proposicional clásica
    son $\V$ (que se interpreta como \textbf{verdadero}) y $\F$ (que se
    interpreta como \textbf{falso}).
  \end{definicion}

  En la formalización se identifica el conjunto de los valores de verdad
  con el tipo \emph{v-verdad}, el valor $\V$ con la constante
  \emph{Verdad} y el valor $\F$ con la constante \emph{Falso}
  respectivamente.

\<close>
datatype v_verdad = Verdad | Falso

text \<open>
  \begin{definicion}\label{interpretacion}
    Una \textbf{interpretación} es una aplicación del conjunto de los
    símbolos proposicionales en el conjunto de los valores de verdad.
  \end{definicion}

  La representación en Isabelle del concepto de interpretación es una
  función de la forma @{text "I  :: 'b \<Rightarrow>  v_verdad"}.

  Ahora se puede definir el valor de una fórmula respecto de una
  interpretación por recursión.

 \begin{definicion}
    El \textbf{valor} de una fórmula proposicional $F$ en una interpretación $I$
    (representado por $I'(F)$) se define por recursión como sigue:
    \begin{itemize}
    \item $I'(P) = I(P)$ si $P$ es un símbolo proposicional
    \item $I'(\neg F) = \begin{cases}
                         \V, & \text{si $I'(F) = \F$}\\
                         \F, & \text{si $I'(F) = \V$}
                        \end{cases}$
    \item $I'(F \wedge G)= \begin{cases}
                            \V, & \text{si $I'(F)=\V$ y $I'(G)=\V$}\\
                            \F, & \text{en caso contrario.}
                           \end{cases}$
    \item $I'(F \vee G)= \begin{cases}
                          \F, & \text{si $I'(F)=\F$ y $I'(G)=\F$}\\
                          \V, & \text{en caso contrario.}
                         \end{cases}$
     \item $I'(F \rightarrow G) = \begin{cases}
                                   \F, & \text{si $I'(F)=\V$ y $I'(G)=\F$}\\
                                   \V, & \text{en caso contrario.}
                                  \end{cases}$
    \end{itemize}
  \end{definicion}

  Para formalizarlo, definimos las funciones de verdad de las conectivas.
\<close>

definition v_negacion :: "v_verdad \<Rightarrow> v_verdad" where
 "v_negacion x \<equiv> (if x = Verdad then Falso else Verdad)"

definition v_conjuncion ::  "v_verdad \<Rightarrow> v_verdad \<Rightarrow> v_verdad" where
 "v_conjuncion x y \<equiv> (if x = Falso then Falso else y)"

definition v_disyuncion ::  "v_verdad \<Rightarrow> v_verdad \<Rightarrow> v_verdad" where
 "v_disyuncion x y \<equiv> (if x = Verdad then Verdad else y)"

definition v_implicacion :: "v_verdad \<Rightarrow> v_verdad \<Rightarrow> v_verdad" where
 "v_implicacion x y \<equiv> (if x = Falso then Verdad else y)"

text\<open> La formalización del valor de una fórmula es: \<close>

primrec valor :: "('b \<Rightarrow>  v_verdad) \<Rightarrow> 'b formula  \<Rightarrow> v_verdad"
where
   "valor I FF = Falso"
|  "valor I TT = Verdad"
|  "valor I (Atomo p) = I p"
|  "valor I (\<not>. F) = (v_negacion (valor I F))"
|  "valor I (F \<and>. G) = (v_conjuncion (valor I F) (valor I G))"
|  "valor I (F \<or>. G) = (v_disyuncion (valor I F) (valor I G))"
|  "valor I (F \<rightarrow>. G) = (v_implicacion (valor I F) (valor I G))"

text \<open>
  En algunas demostraciones en las que se utiliza la noción de valor de
  verdad de una fórmula, en lugar de la definición se suele usar algunas
  de la propiedades que presentamos a continuación.

  \begin{lema}
    Sea $F$ un fórmula e $I$ una interpretación. Entonces, $I'(F)=\V$ ó
    $I'(F)=\F$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma CasosValor:
shows "valor I F = Verdad \<or>  valor I F = Falso"
(*<*)
proof(cases "valor I F")
  assume "valor I F = Verdad" thus ?thesis by simp
  next
  assume hip: "valor I F = Falso" thus ?thesis by simp
qed
(*>*)

text \<open>
  \begin{lema}
    Sea $F$ una fórmula e $I$ una interpretación. Si $I'(\neg F)=\F$,
    entonces $I'(F)=\V$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma ValoresNegacion1:
assumes "valor I (\<not>.F) = Falso"
shows "valor I F = Verdad"
(*<*)
proof -
  { assume "valor I F \<noteq> Verdad"
    hence "valor I F = Falso"  using CasosValor by auto
    hence "valor I (\<not>.F) = Verdad" by(simp add: v_negacion_def)
    hence "False"
      using assms by auto}
  thus "valor I F = Verdad" by auto
qed
(*>*)

text \<open>
  \begin{lema}
    Sea $F$ un fórmula e $I$ una interpretación. Si $I'(\neg F)=\V$,
    entonces $I'(F)=\F$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma ValoresNegacion2:
assumes "valor I (\<not>.F) = Verdad"
shows "valor I F = Falso"
(*<*)
proof -
  { assume "valor I F \<noteq> Falso"
    hence "valor I F = Verdad"  using CasosValor by auto
    hence "valor I (\<not>.F) = Falso" by(simp add: v_negacion_def)
    hence "False" using assms by auto}
  thus "valor I F = Falso" by auto
qed
(*>*)

lemma  no_verdad:
  assumes "valor I F \<noteq>  Verdad" shows "valor I F = Falso"
(*<*)
proof(rule ccontr)
  assume "valor I F \<noteq> Falso"
  thus False using assms CasosValor by auto
qed
(*>*)

text \<open>
  \begin{lema}
    Sean $F$ y $G$ fórmulas e $I$ una interpretación. Si
    $I'(F\wedge G)=\V$, entonces $I'(F)=\V$ e $I'(G)=\V$
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma ValoresConjuncion:
  assumes "valor I (F \<and>. G) = Verdad"
  shows "valor I F = Verdad \<and> valor I G = Verdad"
(*<*)
proof -
 { assume "\<not>(valor I  F = Verdad \<and> valor I  G = Verdad)"
   hence "valor I  F \<noteq> Verdad \<or> valor I G \<noteq> Verdad" by simp
   hence "valor I  F = Falso \<or> valor I G = Falso" using CasosValor by auto
   hence "valor I (F \<and>. G) = Falso" by(auto simp add: v_conjuncion_def)
   hence "False" using assms by simp}
 thus "valor I F = Verdad \<and> valor I G = Verdad" by auto
qed
(*>*)

text \<open>
  \begin{lema}
  Sean $F$ y $G$ fórmulas e $I$ una interpretación. Si $I'(F\vee G)=\V$,
  entonces $I'(F)=\V$ ó $I'(G)=\V$
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma ValoresDisyuncion:
  assumes "valor I (F \<or>. G ) = Verdad"
  shows "valor I  F = Verdad \<or> valor I G = Verdad"
(*<*)
proof -
 { assume "\<not>(valor I  F = Verdad \<or> valor I G  = Verdad)"
   hence "valor I F  \<noteq> Verdad \<and> valor I G \<noteq> Verdad" by simp
   hence "valor I  F = Falso \<and> valor I G = Falso" using CasosValor by auto
   hence "valor I (F \<or>. G) = Falso" by(simp add: v_disyuncion_def)
   hence "False" using assms by simp}
 thus "valor I F = Verdad \<or> valor I G = Verdad" by auto
qed
(*>*)

text \<open>
  \begin{lema}
  Sea $F$ y $G$ fórmulas e $I$ una interpretación tales que
  $I'(F \rightarrow G) = \V$. Si $I'(F)=\V$, entonces $I'(G)= \V$.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma ValoresImplicacion:
  assumes "valor I (F \<rightarrow>. G) = Verdad"
  shows "valor I F = Verdad \<longrightarrow> valor I G = Verdad"
(*<*)
proof -
 { assume "\<not>(valor I F = Verdad \<longrightarrow> valor I G = Verdad)"
   hence "valor I F =  Verdad \<and> valor I G \<noteq> Verdad" by simp
   hence "valor I F = Verdad \<and> valor I G = Falso" using CasosValor by auto
   hence "valor I (F \<rightarrow>. G) = Falso" by(simp add: v_implicacion_def)
   hence "False" using assms by simp}
 thus "valor I F = Verdad \<longrightarrow> valor I G = Verdad" by auto
qed
(*>*)

text \<open>
  Formalizamos  las nociones de satisfacibilidad, consecuencia
  lógica y tautología en términos del concepto de @{text modelo}.  Las
  demostraciones de las propieda\-des que se enuncian acerca de
  estos conceptos se obtienen directamente a partir de las definiciones.

  \begin{definicion}\label{modeloP}
    Una interpretación $I$ es \textbf{modelo} de un conjunto de fórmulas $S$
    si, para toda fórmula $F$ de $S$, $I'(F) = \V$.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition modelo :: "('b \<Rightarrow> v_verdad) \<Rightarrow> 'b formula set \<Rightarrow> bool" ("_ modelo _" [80,80] 80) where
 "I modelo S \<equiv> (\<forall>F \<in> S. valor I F = Verdad)"

text \<open>
  \begin{definicion}\label{satisfacibleP}
    Un conjunto de fórmulas es \textbf{satisfacible} si tiene algún modelo. En
    caso contrario se dice que es \textbf{insatisfacible}.
  \end{definicion}

  \noindent Su formalización es \<close>

definition satisfacible :: "'b formula set \<Rightarrow> bool" where
 "satisfacible S \<equiv> (\<exists>v. v modelo S)"

text \<open>
  \begin{definicion}\label{consecuenciaP}
    Una fórmula $F$ es una \textbf{consecuencia lógica} de un conjunto de
    fórmulas $S$ si para todo modelo $I$ de $S$ se tiene que $I'(F) =\V$. Se
    representa por @{text "S \<Turnstile> F"}.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition consecuencia :: "'b formula set \<Rightarrow> 'b formula \<Rightarrow> bool" ("_ \<Turnstile> _" [80,80] 80) where
 "S \<Turnstile> F \<equiv> (\<forall>I. I modelo S \<longrightarrow> valor I F = Verdad)"

text \<open>
  El siguiente resultado establece la relación entre los conceptos de
  consecuencia lógica y satisfactibilidad.
\<close>

(*<*)
text\<open>
  \begin{lema}
  Si @{text "S \<Turnstile> F"}, entonces @{text "S \<union> {\<not>. F}"} no es satisfacible.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma ConsSat:
  assumes "S \<Turnstile> F"
  shows "\<not> satisfacible (S \<union> {\<not>. F})"
proof(rule notI)
  assume "satisfacible (S \<union> {\<not>. F})"
  hence 1: "\<exists>I. I modelo (S \<union> {\<not>. F})" by (auto simp add: satisfacible_def)
  obtain I where I: "I modelo (S \<union> {\<not>. F})" using 1 by auto
  hence 2: "\<forall>G\<in>(S \<union> {\<not>. F}). valor I G = Verdad"
    by (auto simp add: modelo_def)
  hence "\<forall>G\<in>S. valor I G = Verdad" by blast
  moreover
  have 3: "valor I (\<not>. F) = Verdad" using 2 by simp
  hence "valor I F = Falso"
    proof (cases "valor I F")
      assume "valor I F = Verdad"
      thus ?thesis using 3 by(simp add: v_negacion_def)
      next
      assume "valor I F = Falso"
      thus ?thesis by simp
    qed
  ultimately
  show "False" using assms
    by (simp add: consecuencia_def, simp add: modelo_def)
qed

text \<open>
  \begin{lema}
  Si @{text "S \<union> {\<not> F}"} no es satisfacible, entonces @{text "S \<Turnstile> F"}.
  \end{lema}

  \noindent Su formalización es:
\<close>

lemma SatCons:
  assumes "\<not> satisfacible (S \<union> {\<not>. F})"
  shows "S \<Turnstile> F"
proof (rule contrapos_np)
  assume hip: "\<not> S \<Turnstile> F"
  show "satisfacible (S \<union> {\<not>. F})"
  proof -
    have 1: "\<exists>I. I modelo S \<and> \<not>(valor I F = Verdad)"
      using hip by (simp add: consecuencia_def)
    obtain I where I: "I modelo S \<and> \<not>(valor I F = Verdad)" using 1 by auto
    hence  "I modelo S" by simp
    hence 2: "\<forall>G\<in>S. valor I G = Verdad" by (simp add: modelo_def)
    have "\<not>(valor I F = Verdad)" using I by simp
    hence 3: "valor I (\<not>. F) = Verdad" by (simp add: v_negacion_def)
    have  "\<forall>G\<in>(S \<union> {\<not>. F}). valor I G = Verdad"
    proof (rule ballI)
      fix G
      assume hip2: "G\<in>(S \<union> {\<not>. F})"
      show "valor I G = Verdad"
      proof (cases)
        assume "G\<in>S"
        thus ?thesis using 2 by simp
        next
        assume "\<not>G\<in>S"
        hence "G = (\<not>. F)"using hip2 by simp
        thus ?thesis using 3 by simp
      qed
    qed
    hence "I modelo (S \<union> {\<not>. F})" by (simp add: modelo_def)
    thus ?thesis by (auto simp add: satisfacible_def)
  qed
  next
  show "\<not> satisfacible (S \<union> {\<not>. F})" using assms by simp
qed
(*>*)

text\<open>
  \begin{teorema}\label{EquiConsSat}
  @{text "S \<Turnstile> F"} si y solamente si @{text "S \<union> {\<not> F}"} no es satisfacible.
  \end{teorema}

  \noindent Su formalización es:
\<close>

theorem EquiConsSat:
  shows  "S \<Turnstile> F = (\<not> satisfacible (S \<union> {\<not>. F}))"
(*<*)
using SatCons ConsSat by blast
(*>*)

text \<open>
  Por último formulamos el concepto de tautología.

  \begin{definicion}
    Una fórmula $F$ es una \textbf{tautología} si $I'(F) =\V$ para toda
    interpretación $I$.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition tautologia :: "'b formula \<Rightarrow> bool" where
  "tautologia F \<equiv> (\<forall>I. ((valor I F) = Verdad))"
text\<open> Ejemplo:

\begin{lema}
  La f\'ormula @{text "F \<rightarrow> (G \<rightarrow> F)"} es una tautolog\'{\i}a.
  \end{lema}

  \begin{demostracion}
  La demostraci\'on se realiza f\'acilmente por casos en los posibles
  valores de la f\'ormula $F$ en la interpretaci\'on $I$, utilizando la
  definici\'on del valor de una implicaci\'on. Tal y como se muestra en la
  siguiente tabla:
  $$\begin{array}{c|c|c|l}
           & F   & G \rightarrow F  &  F  \rightarrow  (G \rightarrow F)
                                                                  \\ \hline
  caso\ 1  & \V  & \V               & \ \ \ \     \V              \\ \hline
  caso\ 2  & \F  &                  & \ \ \ \     \V              \\
  \end{array}$$
  \end{demostracion}

  \noindent Su formalizaci\'on es:
\<close>

lemma "tautologia (F  \<rightarrow>. (G \<rightarrow>. F))"
proof -
  have "\<forall>I. valor I (F \<rightarrow>. (G \<rightarrow>. F)) = Verdad"
  proof
    fix I
    show "valor I (F \<rightarrow>. (G \<rightarrow>. F)) = Verdad"
    proof (cases "valor I F")
      text\<open> Caso 1: \<close>
    { assume "valor I F = Verdad"
      thus ?thesis by (simp add: v_implicacion_def) }
      next
      text\<open> Caso 2: \<close>
    { assume "valor I F = Falso"
      thus ?thesis by(simp add: v_implicacion_def) }
    qed
  qed
  thus ?thesis by (simp add: tautologia_def)
qed

text \<open>
  El concepto de tautología se puede formular en términos del concepto
  de consecuencia lógica:
\<close>

(*<*)
text \<open>
  \begin{lema}
    Todas las interpretaciones son modelo del conjunto vacío.
  \end{lema}
\<close>

lemma modelo_de_vacio: "\<forall>(I::'b \<Rightarrow> v_verdad). I modelo {}"
proof -
  have "\<forall>F\<in> {}. valor (I::'b \<Rightarrow> v_verdad) F = Verdad" by simp
  thus "\<forall>I. I modelo {}" by (simp add: modelo_def)
qed
(*>*)

text \<open>
  \begin{teorema}
  Una fórmula es tautología si y solamente si es consecuencia del conjunto vacío.
  \end{teorema}

  \noindent Su formalizacion es
\<close>

theorem CNS_tautologia: "tautologia F = ({} \<Turnstile> F)"
(*<*)
by(simp add: tautologia_def consecuencia_def modelo_de_vacio)
(*>*)

text\<open>
  \begin{teorema}\label{TautSatis}
  La implicación @{text "F \<rightarrow> G" } es una tautología si y solamente si el conjunto
  @{text "{F, \<not>G}"} no es satisfacible.
  \end{teorema}

  \noindent Su formalización es: \<close>

theorem TautSatis:
  shows "tautologia (F \<rightarrow>. G) = (\<not> satisfacible{F, \<not>.G})"
(*<*)
proof -
 { assume h1: "\<not> tautologia (F \<rightarrow>. G)"
   have "satisfacible{F, \<not>.G}"
   proof -
     have "\<exists> I. valor I (F \<rightarrow>. G) \<noteq> Verdad"
       using h1 by (unfold tautologia_def, auto)
    then obtain I where "valor I (F \<rightarrow>. G) \<noteq> Verdad" by auto
    hence a: "valor I (F \<rightarrow>. G) = Falso" using CasosValor by blast
    hence "valor I F = Verdad \<and> valor I G = Falso"
    proof -
     { assume "valor I F \<noteq> Verdad \<or> valor I G \<noteq> Falso"
       hence "False"
       proof(rule disjE)
         assume "valor I F \<noteq> Verdad"
         hence "valor I F = Falso" using CasosValor by auto
         hence "valor I (F \<rightarrow>. G) = Verdad"
           by (auto simp add: v_implicacion_def)
         thus "False" using a by auto
       next
         assume "valor I G \<noteq> Falso"
         hence "valor I G = Verdad" using CasosValor by auto
         hence "valor I (F \<rightarrow>. G) = Verdad" by( simp add: v_implicacion_def)
         thus "False" using a by auto
       qed}
     thus "valor I F = Verdad \<and> valor I G = Falso" by auto
   qed
   hence "valor I F = Verdad \<and> valor I (\<not>.G) = Verdad"
     by (simp add: v_negacion_def)
   hence "\<exists> I. I modelo {F, \<not>.G}" by (auto simp add: modelo_def)
   thus "satisfacible {F, \<not>.G}" by(simp add: satisfacible_def)
 qed}
moreover
{ assume h2: "satisfacible {F, \<not>.G}"
  have "\<not> tautologia (F \<rightarrow>. G)"
  proof -
    have "\<exists> I. I modelo {F, \<not>.G}" using h2 by (simp add: satisfacible_def)
    hence "\<exists> I. valor I F = Verdad \<and> valor I (\<not>.G) = Verdad"
      by(simp add: modelo_def)
    then obtain I where I1: "valor I F = Verdad" and I2: "valor I (\<not>.G) = Verdad"
      by auto
    have "valor I G = Falso" using I2 ValoresNegacion2 by auto
    hence "valor I (F \<rightarrow>. G) = Falso" using I1
      by (simp add: v_implicacion_def)
    thus "\<not> tautologia (F \<rightarrow>. G)" by (auto, unfold tautologia_def, auto)
  qed}
  ultimately
  show ?thesis by auto
qed

subsection \<open> Equivalencia entre fórmulas *}

text\<open>\<close>

  \begin{definicion}
   Dos fórmulas $F$ y $G$ son equivalentes si $I'(F) = I'(G)$ para toda
   interpretación $I$, y se representa por $F\equiv G$.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition equivalentes:: "'b formula  \<Rightarrow> 'b formula \<Rightarrow> bool" where
  "equivalentes F G \<equiv> (\<forall> I. (valor I F) = (valor I G))"

(*>*)

(*<*)
end
(*>*)
