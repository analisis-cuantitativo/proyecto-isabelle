header {* Método de prueba basado en tableros semánticos *}

(*<*)
theory T4TableroP
imports T3FormaNormalConjuntivaP
begin
(*>*)

text {*
  \label{cap5}
  En este capítulo presentamos una formalización de un procedi\-miento
  de prueba para la lógica proposicional basado en la noción de {\em
  {tableros semánticos}}. Describimos el algoritmo, de la misma manera
  como se hizo en el capítulo anterior para formalizar el algoritmo
  $FNC$, en términos de los conceptos de @{text "fórmulas \<alpha>"} y @{text
  "fórmulas \<beta>"}, y demostramos su terminación y corrección siguiendo la
  exposición del texto de Fitting \cite{Fitting}.
*}

section {*
  Descripción de la formalización de la deducibilidad mediante tableros
  semánticos
*}

text {*

  El método de prueba por tableros es un sistema de pruebas por @{text
  "contradicción"}. Para probar una fórmula $F$, debemos obtener una
  contradicción a partir de $\neg F$. El método se basa en la
  construcción de un árbol (tablero), en donde los nodos se etiquetan
  con fórmulas, cada rama representa la conjunción de las fórmulas que
  aparecen en ella y el árbol representa la disyunción de sus ramas.

  En esta sección definimos la función @{text "PruebaTablero"} que
  formaliza en Isabelle un proce\-dimiento de prueba usando tableros
  semánticos.
*}

subsection {* Definición de tablero semántico *}

text {*
  Consideremos un árbol finito $T$ en donde sus nodos están etiquetados
  con fórmulas proposicionales, sea $R$ una rama de $T$ y $N$ una
  fórmula (nodo) de $R$.  Entonces, a partir de $T$, podemos obtener un
  nuevo árbol $T'$ si aplicamos una de las siguientes reglas:
  \begin{itemize}
   \item Si $N$ es de la forma  $\neg \neg Z$, $T'$ se obtiene a partir
    de $T$ añadiendo al final de la rama $R$ un nuevo nodo etiquetado con
    la fórmula $Z$.
   \item Si $N$ es una fórmula $\alpha$, $T'$ se obtiene a partir de $T$
    añadiendo al final de la rama $R$ un nodo con etiqueta $\alpha_1$ y
    posteriormente adicionamos otro nodo con etiqueta $\alpha_2$.  \item
    Si $N$ es una fórmula $\beta$, $T'$ se obtiene a partir de $T$
    añadiendo al final de la rama $R$ un hijo izquierdo con etiqueta
    $\beta_1$ y un hijo derecho con etiqueta $\beta_2$.
  \end{itemize}

  En este caso decimos que $T'$ se obtuvo a partir de $T$ por la
  aplicación de una regla de tableros. Representaremos en Isabelle los
  árboles finitos (tableros) y ramas por medio de listas; una rama
  estará representada por la lista de las fórmulas que etiquetan sus
  nodos, @{text "rama = 'b formula list"} y un árbol estará
  representado por una lista de sus ramas, @{text "árbol = rama list"}.
  Las siguientes funciones formalizan las reglas de tableros para las
  fórmulas de tipo Alfa, Beta y dobles negaciones.
*}

fun reglaTNoNo :: "'b formula \<Rightarrow> ('b formula list) list \<Rightarrow> ('b formula list) list" where
  "reglaTNoNo F T = reemplazarDN  F (Comp1 F)  T"

fun reglaTBeta:: "'b formula => ('b formula list) list \<Rightarrow> ('b formula list) list" where
  "reglaTBeta F  T = reemplazarAlfa F (Comp1 F) (Comp2 F) T"

fun reglaTAlfa:: "'b formula \<Rightarrow> ('b formula list) list \<Rightarrow> ('b formula list) list" where
  "reglaTAlfa F T =  reemplazarBeta F (Comp1 F) (Comp2 F) T"

text {*
  La siguiente definición establece la noción de @{text "tablero"} para
  un conjunto finito de fórmulas.

  \begin{definicion}
    Sea $\{A_1,\, A_2, \dots , A_n\}$ un conjunto de fórmulas proposicionales.\\
    1. El siguiente árbol de una sola rama es un tablero (inicial) para
       $\{A_1,\, A_2, \dots , A_n\}$:\\
          \[A_1\]
          \[\vdots\]
          \[A_n\]
    2. Si $T$ es un tablero para $\{A_1,\, A_2, \dots , A_n\}$ y $T'$ se
       obtiene a partir de T mediante la aplicación de una regla de
       tableros, entonces $T'$ es un tablero para
       $\{A_1,\, A_2, \dots , A_n\}$.
  \end{definicion}

  A continuación definimos tres tipos especiales de tableros: estrictos
  (\ref{estricto}), completos (\ref{completo}) y cerrados
  (\ref{cerrado}).

  \begin{definicion}\label{estricto}
    Un tablero $T$ es {\bf{estricto}} si en su construcción a ninguna
    fórmula se le ha aplicado una regla de tableros dos veces sobre la
    misma rama.
 \end{definicion}

 \begin{definicion}\label{completo}
    Un tablero $T$ es {\bf{completo}} si no es posible obtener a partir
    de él un tablero estricto $T'$ mediante la aplicación de una de las
    reglas de tableros.
 \end{definicion}

  \begin{definicion}\label{ramacerrada}
    Una rama $R$ de un tablero $T$ está {\bf{cerrada}} si existe una
    fórmula $F$ tal que $F$ y $\neg F$ son nodos de $R$ o bien $R$
    contiene a $\bot$ o contiene a $\neg \top$.
  \end{definicion}

  Para su formalización definimos {\em Ramacerrada1} tal que
  {\em (Ramacerrada1 F R)} se verifica si $R$ contiene a $F$ y $\neg F$, o
  contiene a $\bot$ o contiene a $\neg \top$.
*}

definition Ramacerrada1:: "'b formula \<Rightarrow> 'b formula list \<Rightarrow> bool" where
  "Ramacerrada1 F  R = ((F \<in> set R \<and> (\<not>. F) \<in> set R) \<or> FF \<in> set R \<or> \<not>.TT \<in> set R)"

text {*
  La formalización de las ramas cerradas es:
*}

primrec  Ramacerrada_aux:: "('b formula list) \<Rightarrow> ('b formula list) \<Rightarrow> bool"
where
  "Ramacerrada_aux [] L = False"
| "Ramacerrada_aux (x#xs) L = ((Ramacerrada1 x L) \<or> (Ramacerrada_aux xs L))"

definition Ramacerrada:: "('b formula list) \<Rightarrow>  bool" where
  "Ramacerrada R = Ramacerrada_aux R R"

(*<*)
text {*
  Una definición alternativa es
*}

fun complementario:: "'b formula  \<Rightarrow> 'b formula "
where
  "complementario F = (\<not>. F)"
| "complementario (\<not>. F) = F"

fun ramacerrada:: "('b formula list) \<Rightarrow>  bool" where
  "ramacerrada [] = False"
| "ramacerrada (F#Fs) = ((F = FF) \<or> (F = \<not>.TT) \<or> ((complementario F) \<in> set Fs))"
(*>*)

(*<*)
text {*
  Las siguientes son algunas propiedades sobre el concepto de rama que se utilizan más
  adelante
*}

lemma Ramacerrada_aux0:
  assumes "Ramacerrada1  F R"
  shows  "Ramacerrada1 F (a#R)"
using assms
by (auto simp add: Ramacerrada1_def)

lemma Ramacerrada_aux1:
  assumes "Ramacerrada_aux R L"
  shows "Ramacerrada_aux (a#R) L"
proof -
  show ?thesis using assms
  proof (induct L)
    case Nil
    assume "Ramacerrada_aux R []"
    thus "Ramacerrada_aux (a#R) []"  by (auto simp add: Ramacerrada_def)
  next
    case (Cons b L)
    assume
      hip1: "Ramacerrada_aux R L \<Longrightarrow> Ramacerrada_aux (a # R) L" and
      hip2: "Ramacerrada_aux R (b#L)"
    show "Ramacerrada_aux (a # R) (b # L)" using hip1 and hip2 by auto
  qed
qed

lemma Ramacerrada_aux2:
  assumes "Ramacerrada_aux L R"
  shows "Ramacerrada_aux L (a#R)"
proof -
  show ?thesis using assms
  proof (induct L)
    case Nil
    assume "Ramacerrada_aux [] R"
    thus "Ramacerrada_aux [] (a#R)"  by (auto simp add: Ramacerrada_def)
  next
    case (Cons b L)
    assume
      hip1: "Ramacerrada_aux L R \<Longrightarrow> Ramacerrada_aux L (a # R)" and
      hip2: "Ramacerrada_aux (b#L) R"
    show "Ramacerrada_aux (b # L) (a # R)"
    proof (cases)
      assume hip: "Ramacerrada1 b (a # R)"
      hence "True" by simp
      thus ?thesis using hip by simp
    next
      assume hip: "\<not> Ramacerrada1 b (a # R)"
      hence "\<not> Ramacerrada1 b  R" using Ramacerrada_aux0 by auto
      hence "Ramacerrada_aux L R" using hip2 by simp
      hence  "Ramacerrada_aux L (a # R)" using hip1 by simp
      thus ?thesis using hip by simp
    qed
  qed
qed

lemma Ramacerrada_aux3:
  assumes "Ramacerrada_aux R R"
  shows "Ramacerrada_aux (a#R) (a#R)"
using assms Ramacerrada_aux1 Ramacerrada_aux2
by blast

lemma Ramacerrada_aux4:
  assumes "Ramacerrada_aux R L"
  shows "\<exists>F. (F \<in> set L \<and> (\<not>.F) \<in> set L) \<or> FF \<in> set L \<or> \<not>.TT \<in> set L"
proof -
  show ?thesis using assms
  proof (induct R)
    case Nil
    assume  "Ramacerrada_aux [] L"
    thus "\<exists>F. (F \<in> set L \<and> (\<not>.F) \<in> set L) \<or> FF \<in> set L \<or> \<not>.TT \<in> set L"
      by (auto simp add: Ramacerrada_def)
  next
    case (Cons a R)
    assume
      hip1: "Ramacerrada_aux R L \<Longrightarrow>
             \<exists>F. (F \<in> set L \<and> (\<not>.F) \<in> set L) \<or> FF \<in> set L \<or> \<not>.TT \<in> set L" and
      hip2: "Ramacerrada_aux (a # R) L"
    show "\<exists>F. (F \<in> set L \<and> (\<not>.F) \<in> set L) \<or> FF \<in> set L \<or> \<not>.TT \<in> set L"
      using hip1 hip2
    proof (cases)
      assume hip: "Ramacerrada1 a L"
      thus ?thesis by(unfold Ramacerrada1_def, blast)
    next
      assume hip: "\<not> Ramacerrada1 a L"
      hence "Ramacerrada_aux R L" using hip2 by auto
      thus ?thesis using hip1 by simp
    qed
  qed
qed

lemma Ramacerrada_aux5:
  assumes "Ramacerrada_aux R R"
  shows "\<exists>F. (F \<in> set R \<and> (\<not>.F) \<in> set R) \<or> FF \<in> set R \<or> \<not>.TT \<in> set R"
using assms Ramacerrada_aux4
by auto
(*>*)

text {*
  El siguiente lema prueba que {\em Ramacerrada} cumple las condiciones
  de la definición \ref{ramacerrada}.
*}

theorem Rama1:
  assumes "Ramacerrada R"
  shows "\<exists>F. (F \<in> set R \<and> (\<not>.F) \<in> set R) \<or> FF \<in> set R \<or> \<not>.TT \<in> set R"
(*<*)
using assms Ramacerrada_aux5
by(auto simp add: Ramacerrada_def)
(*>*)

text {*
  \begin{definicion}\label{cerrado}
    Un tablero $T$ es {\bf{cerrado}} si todas sus ramas están cerradas.
  \end{definicion}

  \noindent Su formalización es
*}

primrec TableroCerrado:: "('b formula list) list \<Rightarrow> bool" where
 "TableroCerrado [] = True"
|"TableroCerrado (R#Rs) = (Ramacerrada R \<and> TableroCerrado Rs)"

section {* Sistema de prueba por tableros *}

text {*
  El concepto de tablero semántico permite establecer un procedimiento
  para decididir satisfacibilidad, y por lo tanto validez, en la lógica
  proposicional. El objetivo de esta sección es formalizar este método y
  demostrar su adecuación.

  \begin{definicion}\label{tablerodeducible}
    Sea $S$ un conjunto de fórmulas. Una fórmula $F$ es {\bf{deducible
    por tableros}} a partir de $S$ si existe un tablero cerrado para
    $S\cup \{\neg F\}$.
  \end{definicion}

  En particular tenemos la siguiente definición.

  \begin{definicion}
    Una fórmula $F$ tiene una {\bf{prueba por tableros}} si existe un
    tablero cerrado para $\{\neg F\}$.  $F$ es un {\bf{teorema}} del
    sistema deductivo por tableros si $F$ tiene una prueba por tableros.
  \end{definicion}

  El sistema deductivo por tableros es correcto y completo; es decir,
  $F$ es deducible por tableros a partir de $S$ si y sólo si $F$ es
  consecuencia lógica de $S$.  Más específicamente, $F$ es consecuencia
  lógica de $S$ si y sólo si existe un tablero completo cerrado para
  $S\cup \{\neg F\}$; además, si existe un tablero completo cerrado para
  un conjunto $S$, cualquier otro tablero completo para $S$ es cerrado.

  De esta forma, un método que construya un tablero completo para un
  conjunto de fórmulas constituye un procedimiento de prueba por
  tableros, basta con comprobar si dicho tablero completo está cerrado o
  no.

  El siguiente algoritmo construye un tablero completo para un conjunto
  finito de fórmulas.

  \begin{itemize}
   \item[] {{\em Entrada:}} Un conjunto de fórmulas $S$.
   \item[] {{\em Salida:}} Un tablero completo $T'$ para $S$.
   \item[] {{\em Procedimiento:}}
   \begin{itemize}
    \item[] Hacer $T$ = la rama cuyos nodos están etiquetados con las
     fórmulas de $S$
    \item[] Mientras que alguna rama de $T$ contenga un nodo con etiqueta
     una fórmula no literal y no marcada hacer lo siguiente:
     \begin{itemize}
      \item[] seleccionar una rama $R$ de $T$ que contenga un nodo
       etiquetado con una fórmula no literal y no marcada.
      \item[] seleccionar un nodo de $R$ etiquetado con una fórmula $N$
       no literal y no marcada.
      \item[] marcar y aplicar a $N$ en $R$ la regla de tableros
       apropiada para obtener un nuevo tablero $T$.
     \end{itemize}
    \item[] Devolver $T'=T$
   \end{itemize}
  \end{itemize}

  Usaremos las siguientes definiciones para formalizar en Isabelle el
  algoritmo anterior. Las correspondientes formalizaciones corresponden
  a las dadas en el capítulo \ref{cap4} (sección \ref{algoritmoFNC}).

  \begin{definicion}
    @{text "(tieneNoLiteralRama R)"} es @{text "Some F"} si la rama $R$
    contiene una fórmula @{text F} que no es literal y es @{text "None"}
    en caso contrario.
  \end{definicion}

  \noindent Su formalización es:
*}

definition tieneNoLiteralRama:: "'b formula list \<Rightarrow> 'b formula option" where
  "tieneNoLiteralRama = tieneNoLiteralDisyuncion"

text {*
  \begin{definicion}
    @{text "(tieneRama_con_NoLiteral T)"} se verifica si el tablero $T$
    contiene una rama @{text R} que contiene una fórmula que no es
    literal y es @{text "False"} en caso contrario.
  \end{definicion}

  \noindent Su formalización es:
*}

definition tieneRama_con_NoLiteral:: "('b formula list) list \<Rightarrow> bool" where
  "tieneRama_con_NoLiteral = tieneDisyun_con_NoLiteral"

text {*
  \begin{definicion}
    @{text "(selecRama_con_NoLiteral T)"} es la primera rama de $T$ que
    contiene una fórmula que no es literal y es @{text "[]"} en caso
    contrario.
  \end{definicion}

\noindent Su formalización es:
*}

definition selecRama_con_NoLiteral:: "('b formula list) list \<Rightarrow> 'b formula list" where
  "selecRama_con_NoLiteral  = selecDisyun_con_NoLiteral"

text {*

  \begin{definicion}
    @{text "(selecNoLiteralRama R)"} es la primera fórmula no literal de
    la rama @{text R}.
  \end{definicion}

\noindent Su formalización es:
*}

definition selecNoLiteralRama:: "'b formula list  \<Rightarrow> 'b formula" where
  "selecNoLiteralRama  = selecNoLiteralDisyuncion"

text {*
  La siguiente función @{text "PruebaTablero"} formaliza el algoritmo
  descrito anteriormente para construir un tablero completo para un
  conjunto $S$ de fórmulas.

  El argumento de la función @{text "PruebaTablero"} será, en general,
  un tablero cualquiera.  De esta forma, $PruebaTablero\ T$ será un
  tablero completo construido a partir del tablero @{text "T"}. Así, al
  representar un conjunto finito de fórmulas $S$ por medio de una lista,
  se tiene que $PruebaTablero\ [S]$ es un tablero completo para el
  conjunto de fórmulas $S$ (construido a partir del tablero inicial
  $[S]$).
*}

function PruebaTablero :: "('b formula list) list \<Rightarrow> ('b formula list) list"  where
"PruebaTablero T  =
 (if \<not>(tieneRama_con_NoLiteral T)
   then T
   else ((let R = (selecRama_con_NoLiteral T) in
        (let Noliteral = (selecNoLiteralRama R)
          in case tipoFormula Noliteral of
               NoNo \<Rightarrow> PruebaTablero (reglaTNoNo Noliteral T)
             | Beta \<Rightarrow> PruebaTablero (reglaTBeta Noliteral T)
             | Alfa \<Rightarrow> PruebaTablero (reglaTAlfa Noliteral T)))))"
by pat_completeness auto

subsection {* Terminación de la función @{text "PruebaTablero"} *}

text {*
  En esta sección formalizamos la terminación de la función @{text
  "PruebaTablero"}.  Usamos las mismas funciones, {\em rango}
  (def. \ref{rango}), {\em tamaño} (def. \ref{tamano}), {\em
  medidaLista} (def. \ref{medidalista}) y {\em Mcmedidas}
  (def. \ref{Mcmedidas}) que permitieron demostrar en el capítulo
  \ref{cap4} la terminación de la función $FNC$, y los siguientes
  resultados.
*}

(*<*)
lemma desigualdadBeta1:
  assumes hip1: "F \<in> set R"
  and hip2: "FormulaBeta F"
  shows "medidaLista(sustituir1  F (Comp1 F) R) < medidaLista R"
proof -
  have "medidaLista ((sustituir1 F (Comp1 F) R )) =
        medidaLista(borrar F R) + rango (Comp1 F)"
    using hip1 propiedadmedidalista2a by blast
  also have "... < medidaLista(borrar F R) + rango F"
    using hip2 desigualdadRangoBeta by simp
  ultimately
  show ?thesis using hip1 propiedadmedidalista1[of F R] by simp
qed

lemma desigualdadBeta2:
  assumes hip1: "F \<in> set R"
  and hip2: "FormulaBeta F"
  shows "medidaLista (sustituir1 F (Comp2 F) R) < medidaLista R"
proof -
  have "medidaLista ((sustituir1 F (Comp2 F) R)) =
        medidaLista (borrar F R) + rango (Comp2 F)"
    using hip1 propiedadmedidalista2a[of F R] by auto
  also have "... < medidaLista(borrar F R) + rango F"
    using hip2 desigualdadRangoBeta by simp
  ultimately
  show ?thesis using hip1 propiedadmedidalista1[of F R] by auto
qed

lemma desigualdadRangoAlfa:
  assumes "FormulaAlfa F"
  shows  "rango (Comp1 F) + rango (Comp2 F) < rango F"
proof -
  have "tipoFormula F = Alfa"
    using assms
    by (auto split: tipoNotacionUniforme.split,
        auto simp add: noAlfaBeta noAlfaNoNo assms)
  hence "rango F =  rango (Comp1 F) + rango (Comp2 F) + 1"
    by (induct F rule: rango.induct, auto)
  thus ?thesis by simp
qed

lemma desigualdadAlfa:
  assumes hip1: "F \<in> set R"
  and hip2: "FormulaAlfa F"
  shows "medidaLista (sustituir2  F (Comp1 F) (Comp2 F) R) <  medidaLista R"
proof -
  have "medidaLista(sustituir2  F (Comp1 F) (Comp2 F) R) =
        medidaLista (borrar F R) + rango (Comp1 F) + rango (Comp2 F)"
    using hip1 propiedadmedidalista2b[of F R] by simp
  also have "... < medidaLista (borrar F R) + rango F"
    using hip2 desigualdadRangoAlfa[of F] by auto
  ultimately
  show ?thesis using hip1 propiedadmedidalista1[of F R] by auto
qed

(*>*)
text {*
  \begin{lema}
    Sea $T$ un tablero tal que la fórmula $F$ pertenence a alguna rama
    $R\in T$. Si $F$ es una doble negación, entonces
    $((reglaTNoNo\, F\, T), T) \in medida$.
  \end{lema}

  \noindent Su formalización es
*}

lemma medidanonoT0:
  assumes hip1: "(elemento F T) \<noteq> []"
  and hip2: "FormulaNoNo F"
  shows "((reglaTNoNo F T), T) \<in> medida"
(*<*)
proof(simp add: medida_def)
  show "(Mcmedidas (borrar (elemento F T) T) +
          {#medidaLista (sustituir1 F (Comp1 F) (elemento F T))#},
         Mcmedidas T) \<in> relacionmedida"
  proof(unfold relacionmedida_def)
    show "(Mcmedidas (borrar (elemento F T) T) +
            {#medidaLista (sustituir1 F (Comp1 F) (elemento F T))#},
           Mcmedidas T) \<in> mult {(x, y). (x < y)}"
    proof -
      have "(elemento F T) \<in> set T" using hip1 by(induct T, auto)
      hence "Mcmedidas T = Mcmedidas (borrar (elemento F T) T) +
                           {# medidaLista (elemento F T) #}"
        using hip2 by (simp add: propiedadMcmedidas)
      moreover
      have "(Mcmedidas (reglaTNoNo F T)) =
            Mcmedidas (borrar (elemento F T) T) +
            {#medidaLista (sustituir1  F (Comp1 F) (elemento F T))#}"
        by (auto simp add: multiset_eq_iff)
      moreover
      let ?a = "medidaLista (elemento F T)"
      let ?K= "{#medidaLista (sustituir1  F (Comp1 F) (elemento F T))#}"
      have  "F \<in> set (elemento F T)" using hip1 by(induct T, auto)
      hence "\<forall>b. b :# ?K --> b < ?a" using hip2 desigualdadNoNo by auto
      ultimately
      have "\<exists>a M0 K. Mcmedidas(T) = M0 + {#a#} \<and>
                     (Mcmedidas (reglaTNoNo F T)) =
                     M0 + K \<and> (\<forall>b. b :# K --> b < a)"
        by blast
      thus ?thesis using r_into_trancl
        by (auto simp add: mult_def, unfold  mult1_def, auto)
    qed
  qed
qed

(*>*)
text {*
  \begin{lema}
    Sea $T$ un tablero tal que la fórmula $F$ pertenece a alguna rama
    $R\in T$.  Si $F$ es una fórmula beta, entonces
    $((reglaTBeta\, F\, T), T) \in medida$.
  \end{lema}

  \noindent Su formalización es:
*}

lemma medidabetaT0:
  assumes hip1: "(elemento F T) \<noteq> []"
  and hip2: "FormulaBeta F"
  shows "((reglaTBeta F T), T) \<in> medida"
(*<*)
proof (simp add: medida_def)
  show "(Mcmedidas (borrar (elemento F T) T) +
           {#medidaLista (sustituir1 F (Comp2 F) (elemento F T))#} +
           {#medidaLista (sustituir1 F (Comp1 F) (elemento F T))#},
         Mcmedidas T) \<in> relacionmedida"
  proof (unfold relacionmedida_def)
    show "(Mcmedidas (borrar (elemento F T) T) +
             {#medidaLista (sustituir1 F (Comp2 F) (elemento F T))#} +
             {#medidaLista (sustituir1 F (Comp1 F) (elemento F T))#},
           Mcmedidas T) \<in> mult {(x, y). (x < y)}"
    proof -
      have "(elemento F T) \<in> set T" using hip1 by(induct T, auto)
      hence "Mcmedidas(T) = Mcmedidas (borrar (elemento F T) T) +
                            {# medidaLista (elemento F T) #}"
        using hip2 by (simp add: propiedadMcmedidas)
      moreover
      have "Mcmedidas (reglaTBeta F T) =
            Mcmedidas (borrar (elemento F T) T) +
            {#medidaLista (sustituir1  F (Comp1 F) (elemento F T)),
              medidaLista (sustituir1  F (Comp2 F) (elemento F T))#}"
        by (auto simp add: multiset_eq_iff)
      moreover
      let ?a = "medidaLista (elemento F T)"
      let ?K= "{#medidaLista (sustituir1  F (Comp1 F) (elemento F T)),
                 medidaLista (sustituir1 F (Comp2 F) (elemento F T))#}"
      have "F \<in> set (elemento F T)" using hip1 by(induct T, auto)
      hence "\<forall>b. b :# ?K --> b < ?a"
        using hip2 desigualdadBeta1 desigualdadBeta2 by auto
      ultimately
      have "\<exists>a M0 K. Mcmedidas T = M0 + {#a#} \<and>
                     (Mcmedidas (reglaTBeta F T)) = M0 + K \<and>
                     (\<forall>b. b :# K --> b < a)"
        by blast
      thus ?thesis using r_into_trancl
        by (auto simp add: mult_def, unfold  mult1_def, auto)
    qed
  qed
qed

(*>*)
text {*
  \begin{lema}
  Sea $T$ un tablero tal que la fórmula $F$ pertenece a alguna rama
  $R\in T$. Si $F$ es una fórmula alfa, entonces
  $((reglaTAlfa\, F\, T), T) \in medida$.
  \end{lema}

  \noindent Su formalización es:
*}

lemma medidaalfaT0:
  assumes hip1: "(elemento F T) \<noteq> []"
  and hip2: "FormulaAlfa F"
  shows "((reglaTAlfa F T), T) \<in> medida"
(*<*)
proof(simp add: medida_def )
  show "(Mcmedidas (borrar (elemento F T) T) +
          {#medidaLista (sustituir2 F (Comp1 F) (Comp2 F) (elemento F T))#},
         Mcmedidas T) \<in> relacionmedida"
  proof (unfold relacionmedida_def)
    show "(Mcmedidas (borrar (elemento F T) T) +
            {#medidaLista (sustituir2 F (Comp1 F) (Comp2 F) (elemento F T))#},
           Mcmedidas T) \<in> mult {(x, y). (x < y)}"
    proof -
      have "(elemento F T) \<in> set T" using hip1 by(induct T, auto)
      hence "Mcmedidas(T) = Mcmedidas (borrar (elemento F T) T) +
                            {# medidaLista(elemento F T) #}"
        using hip2 by (simp add: propiedadMcmedidas)
      moreover
      have "Mcmedidas (reglaTAlfa F T) =
            Mcmedidas (borrar (elemento F T) T) +
             {#medidaLista (sustituir2 F (Comp1 F) (Comp2 F) (elemento F T))#}"
        by (auto simp add: multiset_eq_iff)
      moreover
      let ?a = "medidaLista (elemento F T)"
      let ?K= "{#medidaLista (sustituir2 F (Comp1 F) (Comp2 F) (elemento F T))#}"
      have  "F \<in> set (elemento F T)" using hip1 by(induct T, auto)
      hence "\<forall>b. b :# ?K --> b < ?a" using hip2 desigualdadAlfa by auto
      ultimately
      have "\<exists>a M0 K. Mcmedidas T = M0 + {#a#} \<and>
                     (Mcmedidas (reglaTAlfa F T)) =
                     M0 + K \<and> (\<forall>b. b :# K --> b < a)"
        by blast
      thus ?thesis using r_into_trancl
        by (auto simp add: mult_def, unfold  mult1_def, auto)
    qed
  qed
qed
(*>*)

text {*
  Usando los tres lemas anteriores, los siguientes tres teoremas
  permiten demostrar que los argumentos de la función @{text
  "PruebaTablero"}, en las llamadas recursivas, decrecen con respecto a
  la relación @{text "medida"}.

  \begin{lema}
  Supongamos que $T$ es un tablero que contiene una rama $R$ con no
  literales. Sea $F\in R$ un no literal.  Si $F$ es una doble negación,
  entonces $((reglaTNoNo\, F\, T), T) \in medida$.
  \end{lema}

  \noindent Su formalización es:
*}

theorem medidanonoT:
  assumes hip1: "tieneRama_con_NoLiteral T"
  and hip2: "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))= NoNo"
  shows "((reglaTNoNo (selecNoLiteralRama (selecRama_con_NoLiteral T)) T),
          T) \<in> medida"
(*<*)
proof -
  have "selecNoLiteralRama (selecRama_con_NoLiteral T) \<in> set
        (elemento (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)"
    using hip1 pertenenciaFundamental1
    by (unfold selecNoLiteralRama_def,
        unfold selecRama_con_NoLiteral_def,
        unfold tieneRama_con_NoLiteral_def,
        auto)
  hence "elemento (selecNoLiteralRama (selecRama_con_NoLiteral T)) T \<noteq> []"
    by auto
  thus ?thesis using hip2 tipoNoNo by(rule_tac medidanonoT0)
qed

(*>*)

text {*
  \begin{lema}
  Supongamos que $T$ es un tablero que contiene una rama $R$ con no
  literales. Sea $F\in R$ un no literal.  Si $F$ es una fórmula alfa,
  entonces $((reglaTAlfa\, F\, T), T) \in medida$.
  \end{lema}

  \noindent Su formalización es:
*}

theorem medidaalfaT:
  assumes hip1: " tieneRama_con_NoLiteral T"
  and hip2: "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))
             = Alfa"
  shows "((reglaTAlfa (selecNoLiteralRama (selecRama_con_NoLiteral T)) T), T)
         \<in> medida"
(*<*)
proof -
  have "selecNoLiteralRama (selecRama_con_NoLiteral T) \<in> set
        (elemento (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)"
    using hip1 pertenenciaFundamental1
    by (unfold selecNoLiteralRama_def,
        unfold selecRama_con_NoLiteral_def,
        unfold tieneRama_con_NoLiteral_def,
        auto)
  hence "elemento (selecNoLiteralRama (selecRama_con_NoLiteral T)) T \<noteq> []"
    by auto
  thus ?thesis using hip2 tipoAlfa by (rule_tac medidaalfaT0)
qed

(*>*)
text {*
  \begin{lema}
  Supongamos que $T$ es un tablero que contiene una rama $R$ con no
  literales. Sea $F\in R$ un no literal.  Si $F$ es una fórmula beta,
  entonces $((reglaBeta\, F\, R), R) \in medida$.
  \end{lema}

  \noindent Su formalización es:
*}

theorem medidabetaT:
  assumes hip1: " tieneRama_con_NoLiteral T"
  and hip2: "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))
             = Beta"
  shows "((reglaTBeta (selecNoLiteralRama (selecRama_con_NoLiteral T)) T), T)
         \<in> medida"
(*<*)
proof -
  have "selecNoLiteralRama (selecRama_con_NoLiteral T) \<in> set
        (elemento (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)"
    using hip1 pertenenciaFundamental1
    by (unfold selecNoLiteralRama_def,
        unfold selecRama_con_NoLiteral_def,
        unfold tieneRama_con_NoLiteral_def,
        auto)
  hence "elemento (selecNoLiteralRama (selecRama_con_NoLiteral T)) T \<noteq> []"
    by auto
  thus ?thesis using hip2 tipoBeta by (rule_tac medidabetaT0)
qed

(*>*)
text {*
  Por último, usando estos teoremas tenemos la prueba de la terminación
  de la función @{text "PruebaTablero"}
*}

termination PruebaTablero
proof-
  show ?thesis
    using wf_medida medidaalfaT medidabetaT medidanonoT
    by (relation medida, auto)
qed

section {* Semántica de los tableros semánticos *}

text {*
  En esta sección se formalizan los conceptos semánticos relativos a los
  tableros.

  \begin{definicion}
  El \textbf{valor} de una rama $[F_1,\, F_2, \dots , F_n]$ en una
  interpretación $I$ se define como sigue:

    $I'[F_1,\, F_2, \dots , F_n] =
     \begin{cases}
       \F, & \text{si $I'(F_i)=\F$ para algún $i$}\\
       \V, & \text{en caso contrario.}
     \end{cases}$
  \end{definicion}

  \noindent Su formalización es:
*}

primrec valorR :: "('b \<Rightarrow> v_verdad) \<Rightarrow> ('b formula list) \<Rightarrow> v_verdad"
where
  "valorR I [] = Verdad"
| "valorR I (F#Fs) = (if valor I F = Falso then Falso else valorR I Fs)"

(*<*)
text {*
  Tenemos las siguientes propiedades sobre la funcion @{text "valorR"}
  que serán usadas más adelante.
*}

lemma valorR1:
  assumes "F \<in> set R" and "valor I F = Falso"
  shows  "valorR I R = Falso"
proof -
  show ?thesis using assms
  proof (induct R)
    case Nil
    assume hip1: "F \<in> set []"
      and hip2: "valor I F = Falso"
    show "valorR I [] = Falso" using hip1 by simp
  next
    case (Cons a R)
    assume hip1: "\<lbrakk>F \<in> set R; valor I F = Falso\<rbrakk> \<Longrightarrow> valorR I R = Falso"
      and hip2: "F \<in> set (a # R)"
      and hip3: "valor I F = Falso"
    show "valorR I (a # R) = Falso"
    proof (cases)
      assume "F=a"
      thus ?thesis using hip3 by simp
    next
      assume "F\<noteq>a"
      hence "F \<in> set R" using hip2 by simp
      hence "valorR I R = Falso" using hip3 hip1 by simp
      thus ?thesis by simp
    qed
  qed
qed

lemma Rama2:
  assumes "Ramacerrada R"
  shows "valorR I R = Falso"
proof -
  have 1: "\<exists>F. (F \<in> set R \<and> (\<not>.F) \<in> set R) \<or> FF \<in> set R \<or> \<not>.TT \<in> set R"
    using assms Rama1 by auto
  thus ?thesis
  proof (cases)
    assume "\<exists>F. (F \<in> set R \<and> (\<not>.F) \<in> set R)"
    then obtain F where F1: "F \<in> set R" and F2: "(\<not>.F) \<in> set R" by auto
    thus ?thesis
    proof(cases "valor I F")
      assume "valor I F = Verdad"
      hence "valor I (\<not>. F) = Falso" by (auto simp add: v_negacion_def)
      thus ?thesis using F2 valorR1[of "(\<not>.F)" ] by simp
    next
      assume "valor I F = Falso"
      thus ?thesis using F1 valorR1[of F] by simp
    qed
  next
    assume  "\<not> (\<exists>F. (F \<in> set R \<and> (\<not>.F) \<in> set R))"
    hence 2: "FF \<in> set R \<or> \<not>.TT \<in> set R" using 1 by auto
    thus ?thesis
    proof (cases)
      assume 3: "FF \<in> set R"
      have "valor I FF = Falso"  by simp
      thus ?thesis using 3 valorR1[of "FF"] by auto
    next
      assume "\<not> FF \<in> set R"
      hence 4: "\<not>. TT \<in> set R" using 2 by simp
      have "valor I TT = Verdad" by simp
      hence "valor I (\<not>. TT) = Falso" by (auto simp add: v_negacion_def)
      thus ?thesis using 4 valorR1[of "\<not>.TT"] by auto
    qed
  qed
qed

lemma valorR2:
  assumes hip1: "F \<in> set S"
  and hip2: "valorR I S = Verdad"
  shows "valor I F = Verdad"
proof (cases "valor I F")
  assume "valor I F =  Verdad"
  thus ?thesis by simp
next
  assume "valor I F = Falso"
  hence "False" using hip1 hip2 valorR1[of F] by auto
  thus ?thesis by simp
qed

lemma valorR3:
  assumes "valorR I S = Verdad"
  shows "\<forall>F \<in> (set S). valor I F = Verdad"
proof
  fix F
  assume hip1: "F \<in> (set S)"
  thus "valor I F = Verdad"
   using assms valorR2 by blast
qed

lemma valorR4:
  assumes "\<forall>F \<in> (set S). valor I F = Verdad"
  shows "valorR I S = Verdad"
proof -
  show ?thesis using assms
  proof (induct S)
    case Nil
    assume "\<forall>F\<in> (set []). valor I F = Verdad"
    show "valorR I [] = Verdad" by simp
  next
    case (Cons a S)
    assume hip1: "\<forall>F\<in>(set S). valor I F = Verdad \<Longrightarrow> valorR I S = Verdad"
      and hip2: "\<forall>F\<in>(set (a # S)). valor I F = Verdad"
    show "valorR I (a # S) = Verdad"
    proof -
      have "valor I a = Verdad"  using hip2 by simp
      moreover
      have "\<forall>F\<in>(set S). valor I F = Verdad" using hip2 by simp
      ultimately
      show ?thesis using hip1 by simp
    qed
  qed
qed

(*>*)
text {*
  \begin{definicion}
    Un rama es \textbf{satisfacible} si es verdadera en alguna interpretación,
    en caso contrario se dice que es \textbf{insatisfacible}.
  \end{definicion}

  \noindent Su formalización es:
*}

definition satisfacibleR :: "'b formula list \<Rightarrow> bool" where
  "satisfacibleR R = (\<exists>I. valorR I R = Verdad)"

text {*
  El próximo teorema afirma que una rama $S$ es satisfacible si y solo si lo es
  el conjunto de sus fórmulas.
*}

(*<*)
lemma satis1:
  assumes "satisfacibleR S"
  shows "satisfacible (set S)"
proof -
  have 1: "\<exists>I. valorR I S = Verdad"
    using assms by (auto simp add: satisfacibleR_def)
  obtain I where I: "valorR I S = Verdad" using 1 by auto
  hence "I modelo (set S)" using valorR3 by (auto simp add: modelo_def)
  thus ?thesis by (auto simp add: satisfacible_def)
qed

lemma satis2:
  assumes "satisfacible (set S)"
  shows "satisfacibleR S"
proof -
  have 1: "\<exists>v. v modelo (set S)"
    using assms by (auto simp add: satisfacible_def)
  obtain v where v: "v modelo (set S)" using 1 by auto
  hence  "\<forall>F\<in>(set S). valor v F = Verdad" by (auto simp add: modelo_def)
  hence "valorR v S = Verdad" using valorR4  by auto
  thus ?thesis using assms by(auto simp add: satisfacibleR_def)
qed

(*>*)
theorem EquiSatisfacible:
  shows "satisfacibleR S = satisfacible (set S)"
(*<*)
using satis1 satis2
by auto
(*>*)

text {*
  \begin{definicion}
  El \textbf{valor} de un tablero $[R_1,\, R_2, \dots , R_n ]$ en una
  interpretación $I$ se define como sigue:

    $I'[R_1,\, R_2, \dots , R_n] =
     \begin{cases}
       \F, & \text{si $I'(R_i)=\F$ para todo $i$}\\
       \V, & \text{en caso contrario.}
     \end{cases}$
  \end{definicion}

 \noindent Su formalización es:
*}

primrec valorTablero :: "('b \<Rightarrow> v_verdad) \<Rightarrow> ('b formula list) list \<Rightarrow> v_verdad" where
  "valorTablero I [] = Falso"
| "valorTablero I (R#Rs) = (if valorR I R = Verdad then Verdad
                                                   else valorTablero I Rs)"
lemma valorTablero:
assumes "valorTablero I (a # T) = Verdad"
shows "valorR I a = Verdad \<or> valorTablero I T = Verdad"
proof(cases "valorR I a")
  assume "valorR I a = Verdad" thus ?thesis by simp
  next
  assume "valorR I a = Falso" thus ?thesis using assms by auto
qed

text {*
  \begin{definicion}
    Un tablero es \textbf{satisfacible} si verdadero en alguna interpretación,
    en caso contrario se dice que es \textbf{insatisfacible}.
  \end{definicion}

  \noindent Su formalización es:
*}

definition satisfacibleT :: "('b formula list) list \<Rightarrow> bool" where
 "satisfacibleT T = (\<exists>I. valorTablero I T = Verdad)"

text {*
  Un tablero es satisfacible sy solo si tiene una rama
  satisfacible. \noindent Su formalización es:
*}

lemma satisfacibleRT:
  assumes "\<exists>R. R \<in> set T \<and> satisfacibleR R"
  shows "satisfacibleT T"
(*<*)
proof -
  obtain R where R:  "R \<in> set T \<and> satisfacibleR R"  using assms by auto
  hence a: "R \<in> set T" and b: "satisfacibleR R" by auto
  obtain I where I: "valorR I R = Verdad"
    using b by (auto simp add: satisfacibleR_def)
  hence "valorTablero I T = Verdad"
    using a by(induct T, auto)
  thus ?thesis by(auto simp add: satisfacibleT_def)
qed

(*>*)
lemma satisfacibleTR:
  assumes "satisfacibleT T"
  shows "\<exists>R. R \<in> set T \<and> satisfacibleR R"
(*<*)
proof -
  obtain I where I: "valorTablero I T = Verdad"
  using assms by (auto simp add: satisfacibleT_def)
  hence "\<exists>R. R \<in> set T \<and> valorR I R = Verdad"
  proof(induct T)
    case Nil thus ?case by simp
    next
    case (Cons a T)
    assume h1: "valorTablero I T = Verdad \<Longrightarrow> \<exists>R. R \<in> set T \<and> valorR I R = Verdad" and
    h2: "valorTablero I (a # T) = Verdad"
    show "\<exists>R. R \<in> set (a # T) \<and> valorR I R = Verdad"
    proof(cases "valorR I a")
      assume "valorR I a = Verdad" thus ?thesis by auto
      next
      assume "valorR I a = Falso" thus ?thesis using h1 h2 valorTablero by auto
    qed
  qed
  thus ?thesis by (auto simp add: satisfacibleR_def)
qed

(*>*)
subsection{* Equivalencia entre tableros *}

text{*
  \begin{definicion}
  Los tableros $T_1$ y $T_2$ son {\bf{equivalentes}} si para toda
  interpretación $I$ el valor de $T_1$ es igual al valor de $T_2$.
  \end{definicion}

  \noindent Su formalización es:
*}

definition equivalentesT:: "('b formula list) list  \<Rightarrow> ('b formula list) list \<Rightarrow> bool" where
 "equivalentesT T1 T2 \<equiv> (\<forall>I. ((valorTablero I T1) = (valorTablero I T2)))"

text {*
  Las reglas que se usan en el algoritmo @{text "PruebaTablero"}
  preservan el valor de cualquier {\em tablero}.  Más precisamente, en
  esta sección demostramos que todo tablero $T$ es equivalen\-te a
  @{text "PruebaTablero T"}.  Para esto demostramos el siguiente
  teorema.

  \noindent
  {\bf{theorem}} @{text "EquivalentesTablero_PruebaTablero:"}\\
  $EquivalentesT\ T\ (PruebaTablero\ T)$

  La demostración de este teorema utiliza los siguientes resultados.
*}

(*<*)
lemma PruebaTableroNoNo:
  assumes "tieneRama_con_NoLiteral T"
  and "R = selecRama_con_NoLiteral T"
  and "Noliteral = selecNoLiteralRama R"
  and "tipoFormula Noliteral = NoNo"
  shows "PruebaTablero T = PruebaTablero (reglaTNoNo Noliteral T)"
using assms
by (simp add: Let_def)

lemma PruebaTableroAlfa:
  assumes "tieneRama_con_NoLiteral T"
  and "R = selecRama_con_NoLiteral T"
  and "Noliteral = selecNoLiteralRama R"
  and "tipoFormula Noliteral = Alfa"
  shows "PruebaTablero T = PruebaTablero (reglaTAlfa Noliteral T)"
using assms
by (simp add: Let_def)

lemma PruebaTableroBeta:
  assumes "tieneRama_con_NoLiteral T"
  and "R = selecRama_con_NoLiteral T"
  and "Noliteral = selecNoLiteralRama R"
  and "tipoFormula Noliteral = Beta"
  shows "PruebaTablero T = PruebaTablero (reglaTBeta Noliteral T)"
using assms
by (simp add: Let_def)

lemma EquiDNoNoa: "equivalentesT [[\<not>. \<not>. F]] [[F]]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [[\<not>. \<not>. F]] = valorTablero I [[F]]"
  proof
    fix I
    show "valorTablero I [[\<not>. \<not>. F]] = valorTablero I [[F]]"
    proof (cases "valor I F")
        -- "Caso 1:"
      { assume 1:"valor I F = Verdad"
        thus ?thesis by (simp add: v_negacion_def) }
    next
        -- "Caso 2:"
      { assume "valor I F = Falso"
        thus ?thesis by (simp add: v_negacion_def) }
    qed
  qed
qed

(*>*)
text {*
  \begin{lema}
  Si $F$ es una doble negación y $G$ es su componente, entonces
  $[[F]] \equiv [[G]]$.
  \end{lema}

  \noindent Su formalización es
*}

lemma EquiDNoNo:
  assumes "tipoFormula F = NoNo"
  shows "equivalentesT [[F]] [[Comp1 F]]"
(*<*)
proof -
  have 1: "\<exists>G. F = \<not>. \<not>. G" using assms tipoNoNo NoNo by auto
  obtain G where "F = \<not>. \<not>. G" using 1 by auto
  moreover
  hence "Comp1 F = G" by(simp add: Comp1_def)
  ultimately
  have "equivalentesT [[F]] [[Comp1 F]] = equivalentesT [[\<not>. \<not>. G]] [[G]]"
    by simp
  thus ?thesis using EquiDNoNoa by simp
qed

lemma EquiDAlfaa: "equivalentesT [[G \<and>. H]] [[G, H]]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [[G \<and>. H]] = valorTablero I [[G, H]]"
  proof
    fix I
    show "valorTablero I [[G \<and>. H]] = valorTablero I [[G, H]]"
    proof (cases "valor I G")
        -- "Caso 1:"
      { assume 1:"valor I G = Verdad"
        thus ?thesis by (simp add: v_conjuncion_def) }
    next
        -- "Caso 2:"
      { assume 2: "valor I G = Falso"
        thus ?thesis
        proof(cases "valor I H")
          assume  "valor I H = Verdad"
          thus ?thesis by (simp add: v_conjuncion_def)
        next
          assume  "valor I H = Falso"
          thus ?thesis using 2 by (simp add: v_conjuncion_def)
        qed }
    qed
  qed
qed

lemma EquiDAlfab: "equivalentesT [[\<not>. (G \<or>. H)]] [[\<not>. G, \<not>. H]]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [[\<not>. (G \<or>. H)]] = valorTablero I [[\<not>. G, \<not>. H]]"
  proof
    fix I
    show "valorTablero I [[\<not>. (G \<or>. H)]] = valorTablero I [[\<not>. G, \<not>. H]]"
    proof (cases "valor I G")
        -- "Caso 1:"
      { assume 1:"valor I G = Verdad"
        thus ?thesis
        proof(cases "valor I H")
          assume  "valor I H = Verdad"
          thus ?thesis
            using 1 by (simp add: v_negacion_def, simp add: v_disyuncion_def)
        next
          assume "valor I H = Falso"
          thus ?thesis
            using 1  by (simp add: v_negacion_def, simp add: v_disyuncion_def)
        qed }
    next
        -- "Caso 2:"
      { assume "valor I G = Falso"
        thus ?thesis
          by (simp add: v_negacion_def, simp add: v_disyuncion_def) }
    qed
  qed
qed

lemma EquiDAlfac:  "equivalentesT [[\<not>. (G \<rightarrow>. H)]] [[G, \<not>. H]]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [[\<not>. (G \<rightarrow>. H)]] = valorTablero I [[G, \<not>. H]]"
  proof
    fix I
    show "valorTablero I [[\<not>. (G \<rightarrow>. H)]] = valorTablero I [[G, \<not>. H]]"
    proof (cases "valor I G")
        -- "Caso 1:"
      { assume 1:"valor I G = Verdad"
        thus ?thesis
        proof(cases "valor I H")
          assume  "valor I H = Verdad"
          thus ?thesis using 1
            by (simp add: v_negacion_def, simp add: v_implicacion_def)
        next
          assume  "valor I H = Falso"
          thus ?thesis using 1
            by (simp add: v_negacion_def, simp add: v_implicacion_def)
        qed }
    next
        -- "Caso 2:"
      { assume "valor I G = Falso"
        thus ?thesis
          by (simp add: v_negacion_def, simp add: v_implicacion_def) }
    qed
  qed
qed
(*>*)

text {*
  \begin{lema}
  Si $F$ es una fórmula alfa y sus componentes son $F_1$ y $F_2$, $[[F]]
  \equiv [[F_1], [F_2]]$.
  \end{lema}

  \noindent Su formalización es"
*}

lemma  EquiDAlfa:
  assumes "tipoFormula F = Alfa"
  shows "equivalentesT [[F]] [[Comp1 F,Comp2 F]]"
(*<*)
proof -
  have 1: "\<exists>G H. F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))"
    using assms tipoAlfa Alfa by auto
  obtain G and H
    where H: "F = (G \<and>. H) \<or> F = (\<not>. (G \<or>. H)) \<or> F = (\<not>. (G \<rightarrow>. H))"
    using 1 by auto
  moreover
  { assume hip: "F = G \<and>. H"
    hence "Comp1 F = G" and "Comp2 F = H"
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiDAlfaa by auto }
  moreover
  { assume hip:  "F = \<not>. (G \<or>. H)"
    hence "Comp1 F = \<not>. G" and "Comp2 F = \<not>. H"
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiDAlfab by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<rightarrow>. H)"
    hence "Comp1 F = G" and "Comp2 F = \<not>. H"
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiDAlfac by simp }
  ultimately
  show ?thesis by blast
qed

lemma EquiDBetaa: "equivalentesT [[G \<or>. H]] [[G], [H]]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [[G \<or>. H]] = valorTablero I [[G],[H]]"
  proof
    fix I
    show "valorTablero I [[G \<or>. H]] = valorTablero I [[G],[H]]"
    proof (cases "valor I G")
        -- "Caso 1:"
      { assume 1:"valor I G = Verdad"
        thus ?thesis
        proof (cases "valor I H")
          assume  "valor I H = Verdad"
          thus ?thesis using 1  by (simp add: v_disyuncion_def)
        next
          assume  "valor I H = Falso"
          thus ?thesis using 1  by (simp add: v_disyuncion_def)
        qed }
    next
        -- "Caso 2:"
      { assume "valor I G = Falso"
        thus ?thesis by (simp add: v_disyuncion_def) }
    qed
  qed
qed

lemma EquiDBetab: "equivalentesT [[\<not>. (G \<and>. H)]] [[\<not>. G],[\<not>. H]]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [[\<not>. (G \<and>. H)]] = valorTablero I [[\<not>. G], [\<not>. H]]"
  proof
    fix I
    show "valorTablero I [[\<not>. (G \<and>. H)]] = valorTablero I [[\<not>. G], [\<not>. H]]"
    proof (cases "valor I G")
        -- "Caso 1:"
      { assume 1:"valor I G = Verdad"
        thus ?thesis
        proof (cases "valor I H")
          assume  "valor I H = Verdad"
          thus ?thesis using 1
            by (simp add: v_negacion_def, simp add: v_conjuncion_def)
        next
          assume "valor I H = Falso"
          thus ?thesis using 1
            by (simp add: v_negacion_def, simp add: v_conjuncion_def)
        qed }
    next
        -- "Caso 2:"
      { assume "valor I G = Falso"
        thus ?thesis
          by (simp add: v_negacion_def, simp add: v_conjuncion_def) }
    qed
  qed
qed

lemma EquiDBetac: "equivalentesT [[G \<rightarrow>. H]] [[\<not>. G],[H]]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [[G \<rightarrow>. H]] = valorTablero I [[\<not>. G], [H]]"
  proof
    fix I
    show "valorTablero I [[G \<rightarrow>. H]] = valorTablero I [[\<not>. G], [H]]"
    proof (cases "valor I G")
        -- "Caso 1:"
      { assume 1:"valor I G = Verdad"
        thus ?thesis
        proof(cases "valor I H")
          assume "valor I H = Verdad"
          thus ?thesis using 1
            by (simp add: v_negacion_def, simp add: v_implicacion_def)
        next
          assume "valor I H = Falso"
          thus ?thesis using 1
            by (simp add: v_negacion_def, simp add: v_implicacion_def)
        qed }
    next
        -- "Caso 2:"
      { assume "valor I G = Falso"
        thus ?thesis
          by (simp add: v_negacion_def, simp add: v_implicacion_def) }
    qed
  qed
qed

(*>*)
text {*
  \begin{lema}
  Si $F$ es una fórmula beta y sus componentes son $F_1$ y $F_2$,
  $[[F]] \equiv [[F_1, F_2]]$.
  \end{lema}

  \noindent Su formalización es:
*}

lemma EquiDBeta:
  assumes  "tipoFormula F = Beta"
  shows "equivalentesT [[F]] [[Comp1 F], [Comp2 F]]"
(*<*)
proof -
  have 1: "\<exists>G H. F = (G  \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F = (G \<rightarrow>. H)"
    using assms tipoBeta Beta by blast
  obtain G and H
    where H: "F = (G \<or>. H) \<or> F = (\<not>. (G \<and>. H)) \<or> F =  (G \<rightarrow>. H)"
    using 1 by auto
  moreover
  { assume hip: "F = G \<or>. H"
    hence "Comp1 F = G" and "Comp2 F = H"
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiDBetaa by simp }
  moreover
  { assume hip:  "F = \<not>. (G \<and>. H)"
    hence "Comp1 F = \<not>. G" and "Comp2 F = \<not>. H"
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiDBetab by simp }
  moreover
  { assume hip:  "F = G \<rightarrow>. H"
    hence "Comp1 F = \<not>. G" and "Comp2 F = H"
      by (simp add: Comp1_def, simp add: Comp2_def)
    hence ?thesis using hip EquiDBetac by simp }
  ultimately
  show ?thesis by blast
qed

lemma EquiTransitivaD:
  assumes "equivalentesT T1 T2" and "equivalentesT T2 T3"
  shows "equivalentesT T1 T3"
using assms
by (simp add: equivalentesT_def)

lemma EquiSustituirD2:
  assumes "equivalentesT [[F]] [[F1, F2]]"
  shows "equivalentesT [R] [sustituir2  F F1 F2 R]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [R] =
            valorTablero I [sustituir2 F F1 F2 R]"
  proof
    fix I
    show "valorTablero I [R] =  valorTablero I [sustituir2 F F1 F2 R]"
    proof (cases "valor I F")
        -- "Caso 1:"
      { assume caso1: "valor I F = Verdad"
        thus ?thesis
        proof(cases "valor I F1")
            -- "Caso 1a:"
          { assume caso1a: "valor I F1 = Verdad"
            thus ?thesis
            proof(cases "valor I F2")
                -- "Caso 1aa:"
              { assume  caso1aa: "valor I F2 = Verdad"
                show ?thesis using caso1 caso1a caso1aa
                  by(induct R, auto, (split split_if_asm, auto)+) }
            next
                -- "Caso 1ab:"
              { assume  caso1ab: "valor I F2 = Falso"
                have False
                proof -
                  have "valorTablero I [[F1, F2]] = Falso"
                    using caso1a caso1ab by simp
                  moreover
                  have "valorTablero I [[F]] = Verdad" using caso1 by simp
                  ultimately
                  show ?thesis using assms
                    by (auto simp add:  equivalentesT_def)
                qed
                thus ?thesis by simp }
            qed }
        next
            -- "Caso 1b:"
          { assume caso1b: "valor I F1 = Falso"
            have False using assms caso1 caso1b
              by (unfold  equivalentesT_def, auto, (split split_if_asm, auto)+)
            thus ?thesis by simp }
        qed }
    next
        -- "Caso 2:"
      { assume caso2: "valor I F = Falso"
        thus ?thesis
        proof (cases "valor I F1")
            -- "Caso 2a:"
          { assume caso2a: "valor I F1 = Verdad"
            thus ?thesis
            proof (cases "valor I F2")
                -- "Caso 2aa:"
              { assume  caso2aa: "valor I F2 = Verdad"
                have False
                proof -
                  have "valorTablero I [[F1, F2]] = Verdad"
                    using caso2a caso2aa by simp
                  moreover
                  have "valorTablero I [[F]] = Falso" using caso2 by simp
                  ultimately
                  show ?thesis using assms by (auto simp add: equivalentesT_def)
                qed
                thus ?thesis by simp }
            next
                -- "Caso 2ab:"
              { assume  caso2ab: "valor I F2 = Falso"
                show ?thesis using caso2 caso2a caso2ab
                  by(induct R, auto, (split split_if_asm, auto)+) }
            qed }
        next
            -- "Caso 2b:"
          { assume caso2b: "valor I F1 = Falso"
            show ?thesis using caso2 caso2b
              by (induct R, auto, (split split_if_asm, auto)+) }
        qed }
    qed
  qed
qed

lemma EquiSustituirD1:
  assumes  "equivalentesT [[F]] [[F1],[F2]]"
  shows "equivalentesT [R][sustituir1  F F1 R, sustituir1  F F2 R]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [R] =
            valorTablero I [sustituir1 F F1 R, sustituir1 F F2 R]"
  proof
    fix I
    show "valorTablero I [R] =
          valorTablero I [sustituir1 F F1 R, sustituir1 F F2 R]"
    proof (cases "valor I F")
        -- "Caso 1:"
      { assume caso1: "valor I F = Verdad"
        thus ?thesis
        proof (cases "valor I F1")
            -- "Caso 1a:"
          { assume caso1a: "valor I F1 = Verdad"
            thus ?thesis using caso1 caso1a
              by (induct R, auto, (split split_if_asm, auto)+) }
                -- "Caso 1b:"
          { assume caso1b: "valor I F1 = Falso"
            thus ?thesis
            proof(cases "valor I F2")
                -- "Caso 1ba:"
              { assume caso1ba: "valor I F2 = Verdad"
                thus ?thesis using caso1 caso1ba
                  by (induct R, auto, (split split_if_asm, auto)+) }
            next
                -- "Caso 1bb:"
              { assume  caso1bb: "valor I F2 = Falso"
                have False using assms caso1 caso1b caso1bb
                  by (unfold equivalentesT_def,
                      auto,
                      (split split_if_asm, auto)+)
                thus ?thesis by simp }
            qed }
        qed }
    next
        -- "Caso 2:"
      { assume caso2: "valor I F = Falso"
        thus ?thesis
        proof (cases "valor I F1")
            -- "Caso 2a:"
          { assume caso2a: "valor I F1 = Verdad"
            have False using assms caso2 caso2a
            proof -
              have "valorTablero I [[F1], [F2]] = Verdad"  using caso2a by simp
              moreover
              have "valorTablero I [[F]] = Falso" using caso2 by simp
              ultimately
              show ?thesis using assms by (auto simp add: equivalentesT_def)
            qed
            thus ?thesis by simp }
        next
            -- "Caso 2b:"
          { assume caso2b: "valor I F1 = Falso"
            thus ?thesis
            proof (cases "valor I F2")
                -- "Caso 2ba:"
              { assume  caso2ba: "valor I F2 = Verdad"
                have False using assms caso2 caso2b caso2ba
                  by (unfold equivalentesT_def,
                      auto,
                      (split split_if_asm, auto)+)
                thus ?thesis by simp }
            next
                -- "Caso 2bb:"
              { assume caso2bb: "valor I F2 = Falso"
                show ?thesis using caso2 caso2b caso2bb
                  by(induct R, auto, (split split_if_asm, auto)+) }
            qed }
        qed }
    qed
  qed
qed

lemma EquiSustituirD3:
  assumes  "equivalentesT [[F]] [[F1]]"
  shows "equivalentesT [R] [sustituir1  F F1 R]"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I [R] = valorTablero I [sustituir1 F F1 R]"
  proof
    fix I
    show "valorTablero I [R] = valorTablero I [sustituir1 F F1 R]"
    proof (cases "valor I F")
        -- "Caso 1:"
      { assume caso1: "valor I F = Verdad"
        thus ?thesis
        proof(cases "valor I F1")
            -- "Caso 1a:"
          { assume caso1a: "valor I F1 = Verdad"
            thus ?thesis using assms caso1
              by(induct R, (auto, split split_if_asm)+, auto) }
        next
            -- "Caso 1b:"
          { assume caso1b: "valor I F1 = Falso"
            have False
            proof -
              have "\<not>equivalentesT [[F]] [[F1]]"
              proof -
                have "valorTablero I [[F1]] = Falso" using  caso1b by simp
            moreover
            have "valorTablero I [[F]] = Verdad" using caso1 by simp
            ultimately
            show ?thesis
            by(simp add: equivalentesT_def, rule_tac  x="I" in exI, (auto, split split_if_asm)+, auto)
          qed
          thus ?thesis using assms by simp
        qed
        thus ?thesis by simp }
    qed }
next
    -- "Caso 2:"
  { assume caso2: "valor I F = Falso"
    thus ?thesis
    proof(cases "valor I F1")
        -- "Caso 2a:"
      { assume caso2a: "valor I F1 = Verdad"
        have False
        proof -
          have "valorTablero I [[F]] = Falso" using caso2 by simp
          moreover
          have  "valorTablero I [[F1]] = Verdad" using  caso2a by simp
          ultimately
          show ?thesis using assms by (auto simp add: equivalentesT_def)
        qed
        thus ?thesis by simp }
    next
        -- "Caso 2b:"
      { assume caso2b: "valor I F1 = Falso"
        thus ?thesis using caso2 caso2b
          by(induct R, auto, split split_if_asm, auto) }
    qed }
  qed
qed
qed

lemma EquiReemplazarRamaD1:
  assumes "equivalentesT [R1] [R2,R3]"
  shows  "equivalentesT (R1 # T) (R2 # R3 # T)"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I (R1 # T) = valorTablero I (R2 # R3 # T)"
  proof
    fix I
    show "valorTablero I (R1 # T) = valorTablero I (R2 # R3 # T)"
    proof (cases "valorTablero I [R1]")
        -- "Caso 1:"
      { assume caso1: "valorTablero I [R1] = Verdad"
        hence  "valorTablero I (R1 # T) = Verdad" by (induct R1, auto)
        moreover
        have "valorTablero I [R2,R3] = Verdad" using assms  caso1
          by (auto simp add:  equivalentesT_def)
        hence  "valorTablero I (R2 # R3 # T) = Verdad"
          by (induct R1, auto)
        ultimately
        show ?thesis by simp }
    next
        -- "Caso 2:"
      { assume caso2: "valorTablero I [R1] = Falso"
        thus ?thesis
        proof(cases "valorTablero I T")
            -- "Caso a:"
          { assume casoa: "valorTablero I T = Verdad"
            hence "valorTablero I (R1 # T) = Verdad" using caso2
              by (induct R1, auto)
            moreover
            have "valorTablero I (R2 # R3 # T) = Verdad"
              using casoa  by (induct R1, auto)
            ultimately
            show ?thesis by simp }
        next
            -- "Caso b:"
          { assume casob: "valorTablero I T = Falso"
            hence "valorTablero I (R1 # T) = Falso"
              using caso2 by (induct R1, auto)
            moreover
            have "valorTablero I [R2,R3] = Falso" using assms caso2
              by (auto simp add:  equivalentesT_def)
            hence "valorTablero I (R2 # R3 # T) = Falso" using casob
              by(induct T,auto, split split_if_asm, auto)
            ultimately
            show ?thesis by simp }
        qed }
    qed
  qed
qed

lemma EquiReemplazarRamaD2:
  assumes "equivalentesT [R1] [R2]"
  shows  "equivalentesT (R1 # T) (R2  # T)"
proof(unfold equivalentesT_def)
  show "\<forall>I. valorTablero I (R1 # T) = valorTablero I (R2 # T)"
  proof
    fix I
    show "valorTablero I (R1 # T) = valorTablero I (R2 # T)"
    proof -
      have "valorTablero I [R1] = valorTablero I [R2]" using assms
        by (auto simp add:  equivalentesT_def)
      thus "valorTablero I (R1 # T) = valorTablero I (R2 # T)"
        by (auto simp add:  equivalentesT_def)
    qed
  qed
qed

lemma EquiBorrarD:
  assumes "R \<in> set T"
  shows "equivalentesT T (R #  (borrar R T))"
proof (unfold equivalentesT_def)
  show "\<forall>I. valorTablero I T = valorTablero I (R # borrar R T)"
  proof
    fix I
    show "valorTablero I T =  valorTablero I (R # borrar R T)"
      using assms by(induct T, auto)
  qed
qed

lemma EquiTableroNoNo:
  assumes hip1: "equivalentesT [[F]] [[F1]]"
  and hip2: "R \<in> set T"
  shows "equivalentesT T ((sustituir1  F F1 R)#(borrar R T))"
proof -
  have "equivalentesT T  (R #  (borrar R T))"
    using hip2 EquiBorrarD[of R] by simp
  moreover
  have "equivalentesT (R #  (borrar R T))
                      (sustituir1  F F1 R # (borrar R T))"
    using hip1 EquiSustituirD3 EquiReemplazarRamaD2 [of R ] by blast
  ultimately
  show ?thesis using EquiTransitivaD by blast
qed

lemma EquiDNoNo1:
  assumes hip1: "elemento F T \<in> set T"
  and hip2: "tipoFormula F = NoNo"
  shows "equivalentesT T (reglaTNoNo F T)"
proof -
  have "equivalentesT [[F]] [[Comp1 F]]" using hip2 EquiDNoNo by simp
  thus ?thesis using hip1 EquiTableroNoNo
    by(auto simp add: reglaTNoNo.induct)
qed

lemma EquiDNoNo2:
  assumes hip1: "tieneRama_con_NoLiteral T"
  and hip2: "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))
             = NoNo"
  shows "equivalentesT
         T
         (reglaTNoNo (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)"
using hip1 hip2 pertenenciaFundamental2
by (unfold tieneRama_con_NoLiteral_def,
    unfold selecNoLiteralRama_def,
    unfold selecRama_con_NoLiteral_def,
    rule_tac EquiDNoNo1,
    auto)

lemma EquiDNoNo3:
  assumes hip1: "tieneRama_con_NoLiteral T"
  and hip2: "R = selecRama_con_NoLiteral T"
  and hip3: "Noliteral = selecNoLiteralRama R"
  and hip4: "tipoFormula Noliteral = NoNo"
  and hip5: "equivalentesT (reglaTNoNo Noliteral T)
                           (PruebaTablero (reglaTNoNo Noliteral T))"
  shows "equivalentesT T (PruebaTablero T)"
proof -
  have 1: "equivalentesT (PruebaTablero (reglaTNoNo Noliteral T))
                         (PruebaTablero T)"
    using hip1 hip2 hip3 hip4 PruebaTableroNoNo[of T]
    by (simp add:  equivalentesT_def)
  have "equivalentesT T (reglaTNoNo Noliteral T)"
    using hip1 hip2 hip3 hip4 EquiDNoNo2 by simp
  hence "equivalentesT T (PruebaTablero (reglaTNoNo Noliteral T))"
    using hip5 EquiTransitivaD by blast
  thus ?thesis using 1 EquiTransitivaD by blast
qed

lemma EquiDNoNo4:
  assumes "tieneRama_con_NoLiteral T"
  and "R = selecRama_con_NoLiteral T"
  and "Noliteral = selecNoLiteralRama R"
  and "tipoFormula Noliteral = NoNo"
  shows "\<lbrakk>\<lbrakk>tieneRama_con_NoLiteral T;
           R = selecRama_con_NoLiteral T;
           Noliteral = selecNoLiteralRama R;
           tipoFormula Noliteral = NoNo\<rbrakk>
          \<Longrightarrow> equivalentesT (reglaTNoNo Noliteral T)
                           (PruebaTablero (reglaTNoNo Noliteral T))\<rbrakk>
         \<Longrightarrow> equivalentesT T (PruebaTablero T)"
proof -
  assume hip1: "\<lbrakk>tieneRama_con_NoLiteral T;
                 R = selecRama_con_NoLiteral T;
                 Noliteral = selecNoLiteralRama R;
                 tipoFormula Noliteral = NoNo\<rbrakk>
                \<Longrightarrow> equivalentesT (reglaTNoNo Noliteral T)
                                 (PruebaTablero (reglaTNoNo Noliteral T))"
  show "equivalentesT T (PruebaTablero T)"
  proof -
    have "equivalentesT (reglaTNoNo Noliteral T)
                        (PruebaTablero (reglaTNoNo Noliteral T))"
      using assms hip1 by simp
    thus ?thesis using assms EquiDNoNo3 by blast
  qed
qed

lemma EquiTableroAlfa:
  assumes hip1: "equivalentesT [[F]] [[F1, F2]]"
  and hip2:  "R \<in> set T"
  shows "equivalentesT T (sustituir2  F F1 F2 R # (borrar R T))"
proof -
  have "equivalentesT T  (R #  (borrar R T))"
    using hip2 EquiBorrarD by auto
  moreover
  have "equivalentesT (R #  (borrar R T))
                      (sustituir2  F F1 F2 R # (borrar R T))"
    using hip1 EquiSustituirD2 EquiReemplazarRamaD2 by blast
  ultimately
  show ?thesis using EquiTransitivaD by blast
qed

lemma EquiDAlfa1:
  assumes hip1: "elemento F T \<in> set T"
  and hip2: "tipoFormula F = Alfa"
  shows "equivalentesT T (reglaTAlfa F T)"
proof -
  have "equivalentesT [[F]] [[Comp1 F, Comp2 F]]"
    using hip2 EquiDAlfa by simp
  thus ?thesis using hip1  EquiTableroAlfa
    by(auto simp add: reglaTAlfa.induct)
qed

lemma EquiDAlfa2:
  assumes hip1: " tieneRama_con_NoLiteral T"
  and hip2: "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) =
             Alfa"
shows "equivalentesT
       T
       (reglaTAlfa (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)"
using  hip1 hip2 pertenenciaFundamental2
by (unfold tieneRama_con_NoLiteral_def,
    unfold selecNoLiteralRama_def,
    unfold selecRama_con_NoLiteral_def,
    rule_tac EquiDAlfa1,
    auto)

lemma EquiDAlfa3:
  assumes hip1: "tieneRama_con_NoLiteral T"
  and hip2: "R = selecRama_con_NoLiteral T"
  and hip3: "Noliteral = selecNoLiteralRama R"
  and hip4: "tipoFormula Noliteral = Alfa"
  and hip5: "equivalentesT (reglaTAlfa Noliteral T)
                           (PruebaTablero (reglaTAlfa Noliteral T))"
  shows "equivalentesT T (PruebaTablero T)"
proof -
  have 1: "equivalentesT (PruebaTablero (reglaTAlfa Noliteral T))
                         (PruebaTablero T)"
    using hip1 hip2 hip3 hip4 PruebaTableroAlfa[of T]
    by (simp add:  equivalentesT_def)
  have "equivalentesT T (reglaTAlfa Noliteral T)"
    using hip1 hip2 hip3 hip4 EquiDAlfa2 by simp
  hence "equivalentesT T (PruebaTablero (reglaTAlfa Noliteral T))"
    using hip5 EquiTransitivaD by blast
  thus ?thesis using 1 EquiTransitivaD by blast
qed

lemma EquiDAlfa4:
  assumes "tieneRama_con_NoLiteral T"
  and "R = selecRama_con_NoLiteral T"
  and "Noliteral = selecNoLiteralRama R"
  and "tipoFormula Noliteral = Alfa"
  shows "\<lbrakk>\<lbrakk>tieneRama_con_NoLiteral T;
           R = selecRama_con_NoLiteral T;
           Noliteral = selecNoLiteralRama R;
           tipoFormula Noliteral = Alfa\<rbrakk>
          \<Longrightarrow> equivalentesT (reglaTAlfa Noliteral T)
                            (PruebaTablero (reglaTAlfa Noliteral T))\<rbrakk>
         \<Longrightarrow> equivalentesT T (PruebaTablero T)"
proof -
  assume hip1: "\<lbrakk>tieneRama_con_NoLiteral T;
                 R = selecRama_con_NoLiteral T;
                 Noliteral = selecNoLiteralRama R;
                 tipoFormula Noliteral = Alfa\<rbrakk>
                \<Longrightarrow> equivalentesT (reglaTAlfa Noliteral T)
                                  (PruebaTablero (reglaTAlfa Noliteral T)) "
  show "equivalentesT T (PruebaTablero T)"
  proof -
    have "equivalentesT (reglaTAlfa Noliteral T)
                        (PruebaTablero (reglaTAlfa Noliteral T))"
      using assms hip1 by simp
    thus ?thesis using assms EquiDAlfa3 by blast
  qed
qed

lemma EquiTableroBeta:
  assumes hip1: "equivalentesT [[F]] [[F1],[F2]]"
  and hip2: "R \<in> set T"
  shows "equivalentesT
         T
         ((sustituir1  F F1 R) # (sustituir1  F F2 R) # (borrar R T))"
proof -
  have "equivalentesT T (R #  (borrar R T))"
    using hip2 EquiBorrarD by auto
  moreover
  have "equivalentesT
         (R # (borrar R T))
         ((sustituir1  F F1 R) # (sustituir1  F F2 R) # (borrar R T))"
    using hip1 EquiSustituirD1 EquiReemplazarRamaD1[of R] by blast
  ultimately
  show ?thesis using EquiTransitivaD by blast
qed

lemma EquiDBeta1:
  assumes hip1: "elemento F T \<in> set T"
  and hip2: "tipoFormula F = Beta"
  shows "equivalentesT T (reglaTBeta F T)"
proof -
  have "equivalentesT [[F]] [[Comp1 F], [Comp2 F]]"
    using hip2 EquiDBeta by simp
  thus ?thesis using hip1 EquiTableroBeta
    by (auto simp add: reglaTBeta.induct)
qed

lemma EquiDBeta2:
  assumes hip1: " tieneRama_con_NoLiteral T"
  and hip2: "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))
             = Beta"
  shows "equivalentesT
         T
         (reglaTBeta(selecNoLiteralRama (selecRama_con_NoLiteral T)) T)"
using  hip1 hip2 pertenenciaFundamental2
by (unfold tieneRama_con_NoLiteral_def,
    unfold selecNoLiteralRama_def,
    unfold selecRama_con_NoLiteral_def,
    rule_tac EquiDBeta1,
    auto)

lemma EquiDBeta3:
  assumes hip1: "tieneRama_con_NoLiteral T"
  and hip2: "R = selecRama_con_NoLiteral T"
  and hip3: "Noliteral = selecNoLiteralRama R"
  and hip4: "tipoFormula Noliteral = Beta"
  and hip5: "equivalentesT (reglaTBeta Noliteral T)
                           (PruebaTablero (reglaTBeta Noliteral T))"
  shows "equivalentesT T (PruebaTablero T)"
proof -
  have 1: "equivalentesT (PruebaTablero (reglaTBeta Noliteral T))
                         (PruebaTablero T)"
    using  hip1 hip2 hip3 hip4 PruebaTableroBeta[of T]
    by (simp add:  equivalentesT_def)
  have "equivalentesT T (reglaTBeta Noliteral T)"
    using hip1 hip2 hip3 hip4 EquiDBeta2 by simp
  hence "equivalentesT T (PruebaTablero (reglaTBeta Noliteral T))"
    using hip5 EquiTransitivaD by blast
  thus ?thesis using 1 EquiTransitivaD by blast
qed

lemma EquiDBeta4:
  assumes "tieneRama_con_NoLiteral T"
  and "R = selecRama_con_NoLiteral T"
  and "Noliteral = selecNoLiteralRama R"
  and "tipoFormula Noliteral = Beta"
  shows "\<lbrakk>\<lbrakk>tieneRama_con_NoLiteral T;
           R = selecRama_con_NoLiteral T;
           Noliteral = selecNoLiteralRama R;
           tipoFormula Noliteral = Beta\<rbrakk>
          \<Longrightarrow> equivalentesT (reglaTBeta Noliteral T)
                           (PruebaTablero (reglaTBeta Noliteral T))\<rbrakk>
         \<Longrightarrow> equivalentesT T (PruebaTablero T)"
proof -
  assume hip1: "\<lbrakk>tieneRama_con_NoLiteral T;
                 R = selecRama_con_NoLiteral T;
                 Noliteral = selecNoLiteralRama R;
                 tipoFormula Noliteral = Beta\<rbrakk>
                \<Longrightarrow> equivalentesT (reglaTBeta Noliteral T)
                                 (PruebaTablero (reglaTBeta Noliteral T)) "
  show "equivalentesT T (PruebaTablero T)"
  proof -
    have "equivalentesT (reglaTBeta Noliteral T)
                        (PruebaTablero (reglaTBeta Noliteral T))"
      using assms hip1 by simp
    thus ?thesis
      using assms EquiDBeta3 by blast
  qed
qed

theorem  EquiT1:
  assumes hip1: "tieneRama_con_NoLiteral T"
  and hip2: "\<lbrakk>tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))
                = NoNo\<rbrakk>
             \<Longrightarrow> equivalentesT
                  (reglaTNoNo
                    (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)
                  (PruebaTablero
                    (reglaTNoNo
                      (selecNoLiteralRama (selecRama_con_NoLiteral T)) T))"
  and hip3: "\<lbrakk>tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))
                = Alfa\<rbrakk>
             \<Longrightarrow> equivalentesT
                  (reglaTAlfa
                    (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)
                  (PruebaTablero
                    (reglaTAlfa
                      (selecNoLiteralRama (selecRama_con_NoLiteral T)) T))"
  and hip4: "\<lbrakk>tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T))
                = Beta\<rbrakk>
             \<Longrightarrow> equivalentesT
                  (reglaTBeta
                    (selecNoLiteralRama (selecRama_con_NoLiteral T)) T)
                  (PruebaTablero
                    (reglaTBeta
                      (selecNoLiteralRama (selecRama_con_NoLiteral T)) T))"
  shows "equivalentesT T (PruebaTablero T)"
proof -
  have "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = NoNo \<or>
        tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = Alfa \<or>
        tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = Beta"
    using assms fundamental4[of T]
    by (unfold tieneRama_con_NoLiteral_def,
        unfold selecNoLiteralRama_def,
        unfold selecRama_con_NoLiteral_def,
        simp)
  thus ?thesis
  proof (rule disjE)
    assume "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = NoNo"
    thus "equivalentesT T (PruebaTablero T)"
      using hip1  hip2  EquiDNoNo4 by blast
  next
    assume
      "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = Alfa \<or>
       tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = Beta"
    thus "equivalentesT T (PruebaTablero T)"
    proof(rule disjE)
      assume
        "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = Alfa"
      thus ?thesis using hip1  hip3  EquiDAlfa4 by blast
    next
      assume
        "tipoFormula (selecNoLiteralRama (selecRama_con_NoLiteral T)) = Beta"
      thus "equivalentesT T (PruebaTablero T)"
        using hip1  hip4  EquiDBeta4 by blast
    qed
  qed
qed

(*>*)
text {*
  \begin{lema}
  Si $T$ es un tablero que contiene ramas con no literales, entonces $T$
  y $PruebaTablero\ T$ son equivalentes.
  \end{lema}

  \noindent Su formalización es:
*}

lemma EquiT2:
  assumes "tieneRama_con_NoLiteral T"
  shows "equivalentesT T (PruebaTablero T)"
(*<*)
using assms
by (induct T rule: PruebaTablero.induct)
   (rule EquiT1, unfold equivalentesT_def, auto)
(*>*)

text {*
  \begin{lema}
  Supongamos que $T$ es un tablero que no contiene ramas con no literales,
  entonces $PruebaTablero\ T = T$.
  \end{lema}

  \noindent Su formalización es:
*}

lemma PruebaTablero4:
  assumes "\<not> tieneRama_con_NoLiteral T"
  shows "PruebaTablero T = T"
(*<*)
using assms by auto
(*>*)

text {*
  \begin{teorema}
  Sea $T$ un tablero y $T'$ el obtenido aplicándole el algoritmo
  $PruebaTablero$ a $T$. Entonces $T$ y $T'$ son equivalentes.
  \end{teorema}

  \noindent Su formalización es:
*}

theorem EquivalentesTablero_PruebaTablero:
  "equivalentesT T (PruebaTablero T)"
proof (cases)
  assume "tieneRama_con_NoLiteral T"
  thus ?thesis using EquiT2 by blast
next
  assume "\<not> tieneRama_con_NoLiteral T"
  hence "PruebaTablero T = T" using PruebaTablero4 by simp
  hence "T = PruebaTablero T" by simp
  thus "equivalentesT T (PruebaTablero T)"
  by (unfold equivalentesT_def, simp)
qed

text {*
  Como consecuencia del teorema anterior, se tienen los siguientes dos
  resultados que serán utilizados, respectivamente, para demostrar la
  corrección y completitud del algoritmo @{text "PruebaTablero"}.

  \begin{corolario}
  Si el tablero $T$ es satisfacible entonces $PruebaTablero\ T$ es satisfacible.
  \end{corolario}

  \noindent Su formalización es:
*}

corollary satisfacible_PruebaTablero:
  assumes "satisfacibleT T"
  shows "satisfacibleT (PruebaTablero T)"
proof -
  obtain I where I: "valorTablero I T = Verdad"
  using assms by (auto simp add: satisfacibleT_def)
  hence "valorTablero I (PruebaTablero T) = Verdad"
  using EquivalentesTablero_PruebaTablero[of T]
  by (unfold equivalentesT_def, auto)
  thus ?thesis by (auto simp add: satisfacibleT_def)
qed

text {*
  \begin{corolario}
  Sea $T$ un tablero. Si $PruebaTablero\ T$ es satisfacible entonces $T$
  es satisfacible.
  \end{corolario}

  \noindent Su formalización es:
*}

corollary PruebaTablero_satisfacible:
  assumes "satisfacibleT (PruebaTablero T)"
  shows "satisfacibleT T"
proof -
  obtain I where I: "valorTablero I (PruebaTablero T) = Verdad" using assms
    by (auto simp add: satisfacibleT_def)
  hence "valorTablero I T = Verdad"
    using EquivalentesTablero_PruebaTablero[of T]
    by (unfold equivalentesT_def, auto)
  thus "satisfacibleT T" by (unfold satisfacibleT_def, blast)
qed

subsection {* Corrección del algoritmo @{text "PruebaTablero"} *}

text {*
  Dado un conjunto finito $S$ y una fórmula proposicional $F$, sea $T$
  el tablero (inicial) corres\-pondiente al conjunto $S \cup \{\neg
  F\}$.  El objetivo de la definición de la función @{text
  "PruebaTablero"} es: si @{text "PruebaTablero T"} es un tablero
  cerrado, entonces $F$ es una consecuencia lógica de $S$.  Para
  demostrar su {\em{corrección}} (\cite{Fitting} páginas 55-56),
  teniendo en cuenta que estamos representando los conjuntos finitos de
  fórmulas por medio de listas, tenemos que probar el siguiente teorema.

  \noindent
  {\bf{theorem}} @{text "correcionTableroConsecuencia:"}\\
  {\bf{assumes}} @{text "TableroCerrado (PruebaTablero [S @ [(\<not>. F)]])"}\\
  {\bf{shows}} @{text "(set S) \<Turnstile>1 F"}

  Para probar el teorema, demostramos previamente los siguientes resultados.
*}

(*<*)
lemma Tablero_aux1:
  assumes "TableroCerrado (a#T)"
  shows "TableroCerrado T"
using assms
by auto

lemma Tablero_aux2:
  assumes hip1: "R \<in> set T"
  and hip2: "\<not>Ramacerrada R"
  shows "\<not>TableroCerrado T"
proof -
  show ?thesis using assms
  proof (induct T)
    case Nil
    assume hipa: "R \<in> set []" and hipb: "\<not> Ramacerrada R"
    show "\<not> TableroCerrado []" using hipa by simp
  next
    case (Cons a T)
    assume hipa: "\<lbrakk>R \<in> set T; \<not> Ramacerrada R\<rbrakk> \<Longrightarrow> \<not> TableroCerrado T"
      and hipb: "R \<in> set (a # T)"
      and hipc: "\<not> Ramacerrada R"
    show "\<not> TableroCerrado (a # T)"
    proof (cases)
      assume "R=a"
      thus ?thesis using hipc by simp
    next
      assume "R\<noteq>a"
      hence "R \<in> set T" using hipb by simp
      thus ?thesis using hipc hipa Tablero_aux1 by auto
    qed
  qed
qed

(*>*)
text {*
  \begin{lema}
  Cualquier tablero satifacible es no cerrado.
  \end{lema}

  \noindent Su formalización es:
*}

lemma Tablero1:
  assumes "satisfacibleT T"
  shows "\<not>TableroCerrado T"
(*<*)
proof -
  obtain R where  R1: "R \<in> set T" and R2: "satisfacibleR R"
    using assms satisfacibleTR by auto
  obtain I where I: "valorR I R = Verdad"
    using R2 by (auto simp add: satisfacibleR_def)
  hence "\<not>Ramacerrada R" using Rama2[of R] by auto
  thus ?thesis using R1 Tablero_aux2 by auto
qed
(*>*)

text {*
  \begin{lema}
  Si la rama compuesta por la fórmula $\neg F$ es insatisfacible
  entonces $F$ es una tautología.
  \end{lema}

  \noindent Su formalización es:
*}

lemma tautsat:
  assumes  "\<not>(satisfacibleR [\<not>. F])"
  shows "tautologia F"
(*<*)
proof -
  have "\<forall>I. valorR I [\<not>. F] = Falso" using assms
    by(auto simp add: satisfacibleR_def, split split_if_asm, auto)
  hence "\<forall>I. valor I (\<not>. F) = Falso" by(auto, split split_if_asm, auto)
  thus ?thesis
    by (auto simp add: v_negacion_def,
        auto simp add: tautologia_def,
        split split_if_asm,
        auto)
qed
(*>*)

text {*
  \begin{lema}
  Sea $S$ un conjunto finito de fórmulas proposicionales y $S'$ el
  tablero (inicial) corres\-pondiente. Si el tablero $PruebaTablero\ S'$
  es cerrrado entonces $S$ es insatifacible.
  \end{lema}

  \noindent Su formalización es:
*}

lemma TabSat:
  assumes "TableroCerrado (PruebaTablero [S])"
  shows "\<not> satisfacible (set S)"
proof -
  have "\<not>(satisfacibleT (PruebaTablero [S]))" using assms Tablero1 by blast
  hence "\<not>(satisfacibleT [S])" using satisfacible_PruebaTablero by blast
  hence "\<not>(satisfacibleR  S)"
    by (auto simp add: satisfacibleT_def,
        auto simp add: satisfacibleR_def,
        split split_if_asm,
        auto)
  thus ?thesis using EquiSatisfacible by auto
qed
(*<*)

text {*
  \begin{lema}
  Sea $T$ el tablero que resulta de aplicarle el algoritmo
  $PruebaTablero$ al tablero (inicial) correspondiente a
  $\{\neg F\}$. Si $T$ es cerrado entoces $F$ es una tautología.
  \end{lema}

  \noindent Su formalización es:
*}

lemma correcionTableroTautologia0:
  assumes "TableroCerrado (PruebaTablero [[\<not>. F]])"
  shows "tautologia F"
proof -
  have "\<not>(satisfacibleT (PruebaTablero [[\<not>. F]]))"
    using assms Tablero1 by blast
  hence "\<not>(satisfacibleT [[\<not>. F]])" using satisfacible_PruebaTablero by blast
  hence "\<not>(satisfacibleR [\<not>. F])"
    by (auto simp add: satisfacibleT_def,
        auto simp add: satisfacibleR_def,
        split split_if_asm,
        auto)
  thus ?thesis using tautsat by auto
qed

text {*
  Otra forma de probar el resultado anterior es como un corolario del
  siguiente teorema.
*}

(*>*)
text {*
  Podemos ahora probar el teorema de corrección.

  \begin{teorema}
  Sea $S$ un conjunto finito de fórmulas proposicionales y $T$ el
  tablero (inicial) correspondiente al conjunto $S\cup\{\neg F\}$. Si el
  tablero $PruebaTablero\ T$ es cerrrado entonces $F$ es una
  consecuencia lógica de $S$.
  \end{teorema}

  \noindent Su formalización es:
*}

theorem correcionTableroConsecuencia:
  assumes "TableroCerrado (PruebaTablero [S @ [(\<not>. F)]])"
  shows "(set S) \<Turnstile>1 F"
proof -
  have "\<not> satisfacible (set (S @ [(\<not>. F)]))"
    using assms TabSat[where S = "S @ [(\<not>. F)]"] by simp
  thus ?thesis using EquiConsSat by auto
qed

text {*
  Como consecuencia se obtiene el siguiente corolario.

  \begin{lema}
  Sea $T$ el tablero que resulta de aplicarle el algoritmo
  $PruebaTablero$ al tablero (inicial) correspondiente a
  $\{\neg F\}$. Si $T$ es cerrado entonces $F$ es una tautología.
  \end{lema}

  \noindent Su formalización es:
*}

corollary correcionTableroTautologia:
  assumes "TableroCerrado (PruebaTablero [[\<not>. F]])"
  shows "tautologia F"
using assms correcionTableroConsecuencia[where  S = "[]"] CNS_tautologia
by auto

(*<*)
end
(*>*)
