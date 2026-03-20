(*<*)
theory T6CFinitoP
imports T5CCerradaP
begin
(*>*)

subsection \<open> Propiedad de carácter finito \<close>

text \<open>
  \label{caracter-finitoP}
  La demostración del teorema de existencia de modelos está basada en
  poder extender una propiedad de consistencia a otra propiedad de
  consistencia que sea cerrada por subconjuntos y de \emph{carácter
  finito}.

  \begin{definicion}\label{cfinito}
  Una colección de conjuntos @{text "\<C>"} es de \textbf{carácter finito}
  si para cada conjunto @{text "S"} se tiene que, @{text "S"}
  pertenece a @{text "\<C>"} si y sólo si cada subconjunto finito de
  @{text "S"} pertenece a @{text "\<C>"}.
  \end{definicion}

  \noindent Su formalización es:
\<close>

definition caracter_finito :: "'a set set \<Rightarrow> bool" where
  "caracter_finito \<C> = (\<forall>S. S \<in> \<C> = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>))"

text \<open>
  \begin{teorema}\label{CaracterFinitoCerradaP}
  Toda colección de conjuntos de carácter finito @{text "\<C>"} es cerrada
  por subconjuntos.
  \end{teorema}

  \begin{demostracion}
  Supongamos que @{text "\<C>"} es de carácter finito;
  sea @{text "S \<in> \<C>"} y @{text "T \<subseteq> S"}, por la definición de
  colección cerrada por subconjuntos, hay que demostrar que
  @{text "T \<in> \<C>"}. Para esto, por hipotésis, basta con demostrar que
  cada subconjunto finito @{text "U"} de @{text "T"} pertenece a
  @{text "\<C>"}. Sea @{text "U"} un conjunto finito tal que
  @{text "U \<subseteq> T"}. Puesto que @{text "T \<subseteq> S"} se tiene que
  @{text "U \<subseteq> S"}. Así, puesto que @{text "S \<in> \<C>"} y @{text "C"} es
  de carácter finito se tiene que @{text "U \<in> \<C>"}.
  \end{demostracion}

  La siguiente es la formalización del teorema anterior.
\<close>

theorem caracter_finito_cerrado:
  assumes "caracter_finito \<C>"
  shows "subconj_cerrada \<C>"
proof -
  { fix S T
    assume "S \<in> \<C>" and  "T \<subseteq> S"
    have "T \<in> \<C>" using "caracter_finito_def"
    proof -
      { fix U
        assume "finite U" and "U \<subseteq> T"
        have "U \<in> \<C>"
        proof -
          have "U \<subseteq> S" using `U \<subseteq> T` and `T \<subseteq> S` by simp
          thus "U \<in> \<C>" using `S \<in> \<C>` and `finite U` and assms
            by (unfold caracter_finito_def) blast
        qed}
      thus ?thesis using assms by( unfold caracter_finito_def) blast
    qed }
  thus ?thesis  by(unfold  subconj_cerrada_def) blast
qed

(*<*)
text \<open>
  Otra estilo de demostrar el mismo teorema:
\<close>

theorem caracter_finito_cerrado1:
  assumes "caracter_finito \<C>"
  shows "subconj_cerrada \<C>"
proof (unfold subconj_cerrada_def)
  show "\<forall> S \<in> \<C>. \<forall> T. T \<subseteq> S \<longrightarrow> T \<in> \<C>"
  proof
    fix S
    assume "S \<in> \<C>"
    show "\<forall>T\<subseteq>S. T \<in> \<C>"
    proof (rule allI)
      fix T
      show "T \<subseteq> S \<longrightarrow> T \<in> \<C>"
      proof
        assume "T \<subseteq> S"
        show "T \<in> \<C>"
        proof -
          have "\<forall>U. finite U \<longrightarrow> U \<subseteq> T \<longrightarrow> U \<in> \<C>"
          proof (rule allI)
            fix U
            show "finite U \<longrightarrow> U \<subseteq> T \<longrightarrow> U \<in> \<C>"
            proof
              assume "finite U"
              show "U \<subseteq> T \<longrightarrow> U \<in> \<C>"
              proof
                assume "U \<subseteq> T"
                hence "U \<subseteq> S" using `T \<subseteq> S` by simp
                thus "U \<in> \<C>" using `S \<in> \<C>` and `finite U` and assms
                  by (unfold caracter_finito_def) blast
              qed
            qed
          qed
          thus ?thesis using assms by( unfold caracter_finito_def) blast
        qed
      qed
    qed
  qed
qed

(*>*)
subsection \<open> Extensión a una propiedad de carácter finito \<close>

text \<open>
  \label{altercarfinito}
  En la sección \ref{cerraduraP} se demostró que toda propiedad de
  consistencia proposicional @{text "\<C>"} puede extenderse a una
  propiedad de consistencia @{text "\<C>\<^sup>+"} que es cerrada por
  subconjuntos. En esta sección demostraremoss que toda propiedad de
  consistencia proposicional @{text "\<C>"} que sea cerrada por
  subconjuntos puede extenderse a una propiedad de consistencia
  @{text "\<C>⁻"} que es de carácter finito. Para la demostración,
  basta con considerar @{text "\<C>⁻"} igual a la colección de todos
  los conjuntos tales que sus subconjuntos finitos están en
  @{text "\<C>"}: @{text "\<C>⁻ = {S | \<forall>S'\<subseteq> S (S' finito \<longrightarrow> S' \<in> \<C>)}"}.

  La definición en Isabelle de @{text "\<C>⁻"} es,
\<close>

definition clausura_cfinito :: "'a set set \<Rightarrow> 'a set set" ("_⁻" [1000] 999) where
  "\<C>⁻ = {S. \<forall>S'. S' \<subseteq> S \<longrightarrow> finite S' \<longrightarrow> S' \<in> \<C>}"

text \<open>
  \begin{teorema}\label{AlternativaCfinitoP}
  Sea @{text "\<C>"} una colección de conjuntos. Se verifican las
  siguientes propiedades:
  \begin{itemize}
  \item[(a)] Si @{text "\<C>"} es cerrada por subconjuntos, entonces
    @{text "\<C> \<subseteq> \<C>⁻"}.
  \item[(b)] @{text "\<C>⁻"} es de carácter finito.
  \item[(c)] Si @{text "\<C>"} es una propiedad de consistencia
    proposicional que es cerrada por subconjuntos entonces,
    @{text "\<C>⁻"} es una propiedad de consistencia proposicional.
  \end{itemize}
  \end{teorema}
\<close>

text \<open>
  \begin{demostracion}

  \textbf{Apartado (a)} Supongamos que @{text "\<C>"} es cerrada por
  subconjuntos y sea @{text "S \<in> \<C>"}. Mostra\-mos que @{text "S \<in> \<C>⁻"}
  usando la definición de @{text "\<C>⁻"}: sea @{text "S'\<subseteq> S"} y
  @{text "S'"} finito. Puesto que @{text "S \<in> \<C>"} y @{text "S'\<subseteq> S"},
  entonces @{text "S' \<in> \<C>"}, ya que por hipótesis @{text "\<C>"} es cerrada
  por subconjuntos.

  \textbf{Apartado (b)} Sea @{text "S"} un conjunto. Por la definición
  de propiedad de carácter finito hay que demostrar que, @{text "S\<in> \<C>⁻"}
  si y sólo si cada subconjunto finito de @{text "S"} pertenece a @{text
  "\<C>⁻"}:

  Si @{text "S\<in> \<C>⁻"}, por la definición de @{text "\<C>⁻"}, se tiene que
  cada subconjunto finito de @{text "S"} pertenece a @{text "\<C>⁻"} y
  recíprocamente si cada subconjunto finito de @{text "S"} pertenece a
  @{text "\<C>⁻"} entonces, por la definición de @{text "\<C>⁻"},
  @{text "S\<in> \<C>⁻"}.

  \textbf{Apartado (c)} Supongamos que @{text "\<C>"} es una propiedad de
  consistencia proposicional que es cerrada por subconjuntos. Sea
  @{text "S \<in> \<C>⁻"}. Entonces, por la definición de @{text "\<C>⁻"}, se
  tiene que cada subconjunto finito de @{text "S"} pertenece a @{text
  "\<C>"}. A continuación mostramos que se cumplen las condiciones para que
  @{text "\<C>⁻"} sea una propiedad de consistencia.

  \textbf{Condición 1} Sea @{text "P"} una fórmula atómica, demostramos
  por contradicción que @{text "P \<notin> S"} o @{text "\<not>P \<notin> S"}. Supongamos que
  @{text "P \<in> S"} y @{text "\<not>P \<in> S"}, entonces
  @{text "{P,\<not>P} \<subseteq> S"}. Por tanto @{text "{P,\<not>P}\<in> \<C>"}, por ser
  @{text "\<C>"} cerrada por subconjuntos.  Luego @{text "P \<notin> {P,\<not>P}"} o
  @{text "\<not>P \<notin> {P,\<not>P}"}, ya que @{text "\<C>"} es una propiedad de
  consistencia. De esta forma obtenemos una contradicción.

  \textbf{Condición 2} La demostración de @{text "\<bottom> \<notin> S"} es por
  contradicción. Supongamos que @{text " \<bottom>\<in> S"}, entonces
  @{text "{\<bottom>} \<subseteq> S"}. Por lo tanto @{text "{\<bottom>} \<in> \<C>"}, por ser
  @{text "\<C>"} cerrada pos subconjuntos. Luego @{text "\<bottom> \<notin> {\<bottom>}"}, ya que
  @{text "\<C>"} es una propiedad de consistencia. De esta forma obtenemos
  una contradicción.

  De la misma forma @{text "\<not>\<top> \<notin> S"}, de lo contrario @{text "{\<not>\<top>} \<subseteq> S"}
  y por lo tanto @{text "{\<not>\<top>} \<in> \<C>"}, por ser @{text "\<C>"} cerrada por
  subconjuntos. Así, puesto que @{text "\<C>"} es una propiedad de
  consistencia, se tendría que @{text "\<not>\<top> \<notin> {\<not>\<top>}"}, lo cual es imposible.

  \textbf{Condición 3} Supongamos que @{text "\<not>\<not>F \<in> S"}. Demostramos que
  @{text "S\<union>{F} \<in> \<C>⁻"} usando la definición de @{text "\<C>⁻"}:
  consideremos @{text "S'"} subconjunto finito de @{text "S\<union>{F}"}, y
  mostremos que @{text "S' \<in> \<C>"}.

  Puesto que @{text "\<not>\<not>F \<in> S"} y @{text "S' \<subseteq> S\<union>{F}"} tenemos que
  @{text "S'−{F}\<union> {\<not>\<not>F}\<subseteq> S"}; también tene\-mos que @{text "S'−{F}\<union>{\<not>\<not>F}"}
  es finito ya que @{text "S'"} es finito. Así, @{text "S'−{F}\<union>{\<not>\<not>F} \<in> \<C>"}
  por la definición de @{text "\<C>\<^sup>-"}, y como
  @{text "{\<not>\<not>F} \<in> S'−{F}\<union>{\<not>\<not>F}"} entonces
  @{text "(S'−{F}\<union>{\<not>\<not>F})\<union>{F} \<in> \<C>"} por ser @{text "\<C>"} una propiedad de
  consistencia. Además, puesto que
  @{text "S' −{F}\<union>{\<not>\<not>F})\<union>{F} = S'\<union>{\<not>\<not>F}\<union>{F}"}, se tiene que
  @{text "S'\<union>{\<not>\<not>F})\<union>{F} \<in> \<C>"}.  De esto último y como
  @{text "S'\<subseteq> S'\<union> {\<not>\<not>F}\<union>{F}"} se tiene que @{text "S' \<in> \<C>"} ya que por
  hipótesis @{text "\<C>"} es cerrada por subconjuntos.

  \textbf{Condición 4} Supongamos que @{text "\<alpha> \<in> S"}. Demostramos que
  @{text "S\<union>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<in> \<C>⁻"} usando la definición de @{text "\<C>⁻"}:
  consideremos @{text "S'"} subconjunto finito de @{text "S\<union>{\<alpha>\<^sub>1, \<alpha>\<^sub>2}"},
  y mostremos que @{text "S' \<in> \<C>"}.

  Puesto que @{text "\<alpha> \<in> S"} y @{text "S'\<subseteq> S\<union>{\<alpha>\<^sub>1,\<alpha>\<^sub>2}"} tenemos que
  @{text "S'−{\<alpha>\<^sub>1,\<alpha>\<^sub>2}\<union>{\<alpha> } \<subseteq> S"}; también tenemos que
  @{text "S'−{\<alpha>\<^sub>1,\<alpha>\<^sub>2}\<union>{\<alpha>}"} es finito ya que @{text "S'"} es finito.

  Así, @{text "S'−{\<alpha>\<^sub>1, \<alpha>\<^sub>2}\<union>{\<alpha> } \<in> \<C>"} por la definición de @{text "\<C>\<^sup>-"},
  y como @{text "\<alpha> \<in> S'−{\<alpha>\<^sub>1,\<alpha>\<^sub>2}\<union>{\<alpha>}"} entonces
  @{text "S'−{\<alpha>\<^sub>1,\<alpha>\<^sub>2}\<union>{\<alpha>})\<union>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<in> \<C>"} por ser @{text "\<C>"} una propiedad de consistencia.

  Además, puesto que
     @{text "S'−{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<union> {\<alpha>}) \<union> {\<alpha>\<^sub>1,\<alpha>\<^sub>2} = S' \<union> {\<alpha>}\<union> {\<alpha>\<^sub>1,\<alpha>\<^sub>2}"}
  se tiene que
     @{text "S'\<union>{\<alpha>}\<union>{\<alpha>\<^sub>1,\<alpha>\<^sub>2} \<in> \<C>"}.
  De esto último, y como @{text "S'\<subseteq> S'\<union>{\<alpha>}\<union>{\<alpha>\<^sub>1,\<alpha>\<^sub>2}"}, se tiene que
  @{text "S' \<in> \<C>"} ya que por hipótesis @{text "\<C>"} es cerrada por
  subconjuntos.

  \textbf{Condición 5} Supongamos que @{text "\<beta> \<in> S"}. Demostramos que
  @{text "S\<union>{\<beta>\<^sub>1} \<in> \<C>⁻"} o @{text "S\<union>{\<beta>\<^sub>2} \<in> \<C>⁻"} por contradicción.

  Supongamos que @{text "S\<union>{\<beta>\<^sub>1} \<notin> \<C>⁻"} y @{text "S\<union>{\<beta>\<^sub>2} \<notin> \<C>⁻"}.
  Entonces, existe @{text "S\<^sub>1"} subconjunto finito de @{text "S\<union>{\<beta>\<^sub>1}"}
  tal que @{text "S\<^sub>1 \<notin> \<C>"}, y existe @{text "S\<^sub>2"} subconjunto finito de
  @{text "S\<union>{\<beta>\<^sub>2}"} tal que @{text "S\<^sub>2 \<notin> \<C>"}. Puesto que @{text "\<beta> \<in> S"},
  @{text "S\<^sub>1 \<subseteq> S\<union>{\<beta>\<^sub>1}"} y @{text "S\<^sub>2 \<subseteq> S\<union>{\<beta>\<^sub>2}"} tenemos que,
  @{text "(S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>} \<subseteq> S"}.

  También tenemos que @{text "(S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>}"} es finito ya que
  @{text "S\<^sub>1"} y @{text "S\<^sub>2"} son finitos. Así,
  @{text "(S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>} \<in> \<C>"} por la definición de @{text "\<C>\<^sup>-"},
  y como
     \newline \hspace*{1cm}
     @{text "\<beta> \<in> (S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>}"}
  \newline entonces, por ser @{text "\<C>"} una propiedad de consistencia,
  se tiene que
     \newline \hspace*{1cm}
     @{text "((S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>})\<union>{\<beta>\<^sub>1} \<in> \<C>"}
     \newline \hspace*{1cm}
     @{text "((S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>})\<union> {\<beta>\<^sub>2} \<in> \<C>"}.

  De esto último tenemos que @{text "S\<^sub>1 \<in> \<C>"} o @{text "S\<^sub>2 \<in> \<C>"}:

  Si @{text "((S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>})\<union>{\<beta>\<^sub>1}\<in> \<C>"} entonces, puesto que
     \newline \hspace*{1cm}
     @{text "S\<^sub>1 \<subseteq> ((S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>})\<union>{\<beta>\<^sub>1}"},
  \newline tenemos que @{text "S\<^sub>1\<in> \<C>"} por ser @{text "\<C>"} cerrada por
  subconjuntos.

  De igual forma, si @{text "((S\<^sub>1−{\<beta>\<^sub>1})\<union> (S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>})\<union>{\<beta>\<^sub>2} \<in> \<C>"}
  entonces, puesto que
     \newline \hspace*{1cm}
     @{text "S\<^sub>2 \<subseteq> ((S\<^sub>1−{\<beta>\<^sub>1})\<union>(S\<^sub>2−{\<beta>\<^sub>2})\<union>{\<beta>})\<union>{\<beta>\<^sub>2}"},
  \newline tenemos que @{text "S\<^sub>2 \<in> \<C>"} por ser @{text "\<C>"} cerrada por
  subconjuntos.

  Esto contradice la hipótesis inicial: @{text "S\<^sub>1\<notin> \<C>"} y @{text "S\<^sub>2\<notin> \<C>"}.
  \end{demostracion}

  A continuación formalizamos cada parte de la prueba del teorema anterior.
  La formalización de la parte (a) es la siguiente:
\<close>

lemma caracter_finito_subset:
  assumes "subconj_cerrada \<C>"
  shows "\<C> \<subseteq> \<C>⁻"
proof -
  { fix S
    assume "S \<in> \<C>"
    have "S \<in> \<C>⁻"
    proof -
      { fix S'
        assume "S' \<subseteq> S" and "finite S'"
        hence "S' \<in> \<C>" using  `subconj_cerrada \<C>` and `S \<in> \<C>`
          by (simp add: subconj_cerrada_def)}
      thus ?thesis by (simp add: clausura_cfinito_def)
    qed}
  thus ?thesis by auto
qed

text \<open>
  El siguiente lema formaliza la parte (b) del teorema
  \ref{AlternativaCfinitoP}
\<close>

lemma caracter_finito: "caracter_finito (\<C>⁻)"
proof (unfold caracter_finito_def)
  show "\<forall>S. (S \<in> \<C>⁻) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻)"
  proof
    fix  S
    { assume  "S \<in> \<C>⁻"
      hence "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻"
        by(simp add: clausura_cfinito_def)}
    moreover
    { assume "\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻"
      hence  "S \<in> \<C>⁻" by(simp add: clausura_cfinito_def)}
    ultimately
    show "(S \<in> \<C>⁻) = (\<forall>S'. finite S' \<longrightarrow> S' \<subseteq> S \<longrightarrow> S' \<in> \<C>⁻)"
      by blast
  qed
qed

text \<open>
  Los siguientes lemas corresponden a la formalización de los 5 casos de
  la parte (c) del teorema \ref{AlternativaCfinitoP}.
\<close>

lemma condicaracterP1:
  assumes "consistenciaP \<C>"
  and "subconj_cerrada \<C>"
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "(\<forall>P. \<not>(Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S))"
(*<*)
proof (rule allI)+
  fix P t
  show "\<not>(Atomo P  \<in> S \<and> (\<not>.Atomo P) \<in> S)"
  proof (rule notI)
    assume "Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S"
    hence "{Atomo P , \<not>.Atomo P} \<subseteq> S" by simp
    hence "{Atomo P, \<not>.Atomo P} \<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> (\<forall>P ts. \<not>(Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S))"
      using `consistenciaP \<C>`
      by (simp add: consistenciaP_def)
    ultimately
    have "\<not>(Atomo P \<in> {Atomo P , \<not>.Atomo P} \<and>
          (\<not>.Atomo P) \<in> {Atomo P, \<not>.Atomo P})"
      by auto
    thus False by simp
  qed
qed
(*>*)
text\<open>\<close>
lemma condicaracterP2:
  assumes "consistenciaP \<C>"
  and "subconj_cerrada \<C>"
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "FF \<notin> S \<and> (\<not>.TT)\<notin> S"
(*<*)
proof -
  have "FF \<notin> S"
  proof(rule notI)
    assume "FF \<in> S"
    hence "{FF} \<subseteq> S" by simp
    hence "{FF}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> FF \<notin> S" using `consistenciaP \<C>`
      by (simp add: consistenciaP_def)
    ultimately
    have "FF \<notin> {FF}" by auto
    thus False by simp
  qed
  moreover
  have "(\<not>.TT)\<notin> S"
  proof(rule notI)
    assume "(\<not>.TT) \<in> S"
    hence "{\<not>.TT} \<subseteq> S" by simp
    hence "{\<not>.TT}\<in> \<C>" using hip by simp
    moreover
    have "\<forall>S. S \<in> \<C> \<longrightarrow> (\<not>.TT) \<notin> S" using `consistenciaP \<C>`
      by (simp add: consistenciaP_def)
    ultimately
    have "(\<not>.TT) \<notin> {(\<not>.TT)}" by auto
    thus False by simp
  qed
  ultimately show ?thesis by simp
qed
(*>*)
text\<open> \<close>
lemma condicaracterP3:
  assumes "consistenciaP \<C>"
  and "subconj_cerrada \<C>"
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁻"
(*<*)
proof (rule allI)
  fix F
  show "(\<not>.\<not>.F) \<in> S \<longrightarrow>  S \<union> {F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(\<not>.\<not>.F) \<in> S"
    show "S \<union> {F} \<in> \<C>⁻"
    proof (unfold clausura_cfinito_def)
      show "S \<union> {F} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>}"
      proof (rule allI impI CollectI)+
        fix S'
        assume "S' \<subseteq> S \<union> {F}" and "finite S'"
        show "S' \<in> \<C>"
        proof -
          have "S' - {F} \<union> {\<not>.\<not>.F}  \<subseteq> S"
            using `(\<not>.\<not>.F) \<in> S` and  `S'\<subseteq> S \<union> {F}` by auto
          moreover
          have "finite (S' - {F} \<union> {\<not>.\<not>.F})" using `finite S'` by auto
          ultimately
          have "(S' - {F} \<union> {\<not>.\<not>.F}) \<in> \<C>" using hip  by simp
          moreover
          have "(\<not>.\<not>.F) \<in> (S' - {F} \<union> {\<not>.\<not>.F})" by simp
          ultimately
          have "(S' - {F} \<union> {\<not>.\<not>.F})\<union> {F} \<in> \<C>"
            using `consistenciaP \<C>` by (simp add: consistenciaP_def)
          moreover
          have "(S' - {F} \<union> {\<not>.\<not>.F})\<union> {F} = (S' \<union> {\<not>.\<not>.F})\<union> {F}"
            by auto
          ultimately
          have "(S' \<union> {\<not>.\<not>.F})\<union> {F} \<in> \<C>" by simp
          moreover
          have  "S' \<subseteq> (S' \<union> {\<not>.\<not>.F})\<union> {F}" by auto
          ultimately
          show "S'\<in> \<C>" using `subconj_cerrada \<C>`
            by (simp add: subconj_cerrada_def)
        qed
      qed
    qed
  qed
qed
(*>*)
text\<open>\<close>
lemma condicaracterP4:
  assumes "consistenciaP \<C>"
  and "subconj_cerrada \<C>"
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "(\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁻)"
(*<*)
proof (rule allI)
  fix F
  show "((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(FormulaAlfa F) \<and> F \<in> S"
    hence "(FormulaAlfa F)" and "F \<in> S" by auto
    show "S \<union> {Comp1 F, Comp2 F} \<in> \<C>⁻"
    proof (unfold clausura_cfinito_def)
      show "S \<union> {Comp1 F, Comp2 F} \<in> {S. \<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>}"
      proof (rule allI impI CollectI)+
        fix S'
        assume "S' \<subseteq> S \<union> {Comp1 F, Comp2 F}"  and  "finite S'"
        show "S' \<in> \<C>"
        proof -
          have "S' - {Comp1 F, Comp2 F} \<union> {F}  \<subseteq> S"
            using `F \<in> S` and  `S'\<subseteq> S \<union> {Comp1 F, Comp2 F}` by auto
          moreover
          have "finite (S' - {Comp1 F, Comp2 F} \<union> {F})"
            using `finite S'` by auto
          ultimately
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<in> \<C>" using hip  by simp
          moreover
          have "F \<in> (S' - {Comp1 F, Comp2 F} \<union> {F})" by simp
          ultimately
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<union> {Comp1 F, Comp2 F} \<in> \<C>"
            using `consistenciaP \<C>` `FormulaAlfa F`
            by (simp add: consistenciaP_def)
          moreover
          have "(S' - {Comp1 F, Comp2 F} \<union> {F}) \<union> {Comp1 F, Comp2 F} =
                (S' \<union> {F}) \<union> {Comp1 F, Comp2 F}"
            by auto
          ultimately
          have "(S' \<union> {F}) \<union> {Comp1 F, Comp2 F} \<in> \<C>" by simp
          moreover
          have "S' \<subseteq> (S' \<union> {F}) \<union> {Comp1 F, Comp2 F}" by auto
          ultimately
          show "S'\<in> \<C>" using `subconj_cerrada \<C>`
            by (simp add: subconj_cerrada_def)
        qed
      qed
    qed
  qed
qed
(*>*)
text\<open> \<close>
lemma condicaracterP5:
  assumes "consistenciaP \<C>"
  and "subconj_cerrada \<C>"
  and hip: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
  shows "\<forall>F. FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
(*<*)
proof (rule allI)
  fix F
  show "FormulaBeta F \<and> F \<in> S \<longrightarrow> S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
  proof (rule impI)
    assume "(FormulaBeta F) \<and> F \<in> S"
    hence "FormulaBeta F" and "F \<in> S" by auto
    show "S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻"
    proof (rule ccontr)
      assume "\<not>(S \<union> {Comp1 F} \<in> \<C>⁻ \<or> S \<union> {Comp2 F} \<in> \<C>⁻)"
      hence "S \<union> {Comp1 F} \<notin> \<C>⁻ \<and> S \<union> {Comp2 F} \<notin> \<C>⁻" by simp
      hence 1: "\<exists> S1. (S1 \<subseteq> S \<union> {Comp1 F} \<and> finite S1 \<and> S1 \<notin> \<C>)"
        and 2: "\<exists> S2. (S2 \<subseteq> S \<union> {Comp2 F} \<and> finite S2 \<and> S2 \<notin> \<C>)"
        by (auto simp add: clausura_cfinito_def)
      obtain S1  where S1: "S1 \<subseteq> S \<union> {Comp1 F} \<and> finite S1 \<and> S1 \<notin> \<C>"
        using 1 by auto
      obtain S2 where  S2: "S2 \<subseteq> S \<union> {Comp2 F} \<and> finite S2 \<and> S2 \<notin> \<C>"
        using 2 by auto
      have "(S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<subseteq> S"
        using `F \<in> S` S1 S2 by auto
      moreover
      have "finite ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F})"
        using S1 and S2 by simp
      ultimately
      have "(S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<in> \<C>" using hip by simp
      moreover
      have "F \<in> (S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F}" by simp
      ultimately
      have 3: "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C> \<or>
               ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F}) \<in> \<C>"
        using `consistenciaP \<C>` `FormulaBeta F`
        by (simp add: consistenciaP_def)
      hence "S1 \<in> \<C> \<or> S2 \<in> \<C>"
      proof (cases)
        assume "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C>"
        moreover
        have "S1 \<subseteq> ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F})"
          by auto
        ultimately
        have "S1 \<in> \<C>"  using `subconj_cerrada \<C>`
          by (simp add: subconj_cerrada_def)
        thus ?thesis by simp
      next
        assume "\<not>((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp1 F}) \<in> \<C>"
        hence "((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F}) \<in> \<C>"
          using 3 by simp
        moreover
        have "S2 \<subseteq> ((S1-{Comp1 F}) \<union> (S2-{Comp2 F}) \<union> {F} \<union> {Comp2 F})"
          by auto
        ultimately
        have "S2 \<in> \<C>"  using `subconj_cerrada \<C>`
          by (simp add: subconj_cerrada_def)
        thus ?thesis by simp
      qed
      thus False using S1 and S2 by simp
    qed
  qed
qed
(*>*)

text \<open>
  Por último, se demuestra que si @{text "\<C>"} es una propiedad de
  consistencia proposicional que es cerrada por subconjuntos entonces
  @{text "\<C>⁻"} es de carácter finito.
\<close>

theorem cfinito_consistenciaP:
  assumes hip1: "consistenciaP \<C>" and hip2: "subconj_cerrada \<C>"
  shows "consistenciaP (\<C>⁻)"
proof -
  { fix S
    assume "S \<in> \<C>⁻"
    hence hip3: "\<forall>S'\<subseteq>S. finite S' \<longrightarrow> S' \<in> \<C>"
      by (simp add: clausura_cfinito_def)
    have "(\<forall>P.  \<not>(Atomo P \<in> S \<and> (\<not>.Atomo P) \<in> S)) \<and>
          FF \<notin> S \<and> (\<not>.TT) \<notin> S \<and>
          (\<forall>F. (\<not>.\<not>.F) \<in> S \<longrightarrow> S \<union> {F} \<in> \<C>⁻) \<and>
          (\<forall>F. ((FormulaAlfa F) \<and> F \<in> S) \<longrightarrow> (S \<union> {Comp1 F, Comp2 F}) \<in> \<C>⁻) \<and>
          (\<forall>F. ((FormulaBeta F) \<and> F \<in> S) \<longrightarrow>
               (S \<union> {Comp1 F} \<in> \<C>⁻) \<or> (S \<union> {Comp2 F} \<in> \<C>⁻))"
      using
        condicaracterP1[OF hip1 hip2 hip3]  condicaracterP2[OF hip1 hip2 hip3]
        condicaracterP3[OF hip1 hip2 hip3]  condicaracterP4[OF hip1 hip2 hip3]
        condicaracterP5[OF hip1 hip2 hip3]  by auto }
  thus ?thesis by (simp add: consistenciaP_def)
qed

(*<*)
end
(*>*)
