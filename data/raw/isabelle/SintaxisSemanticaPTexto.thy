(*<*)
theory SintaxisSemanticaPTexto
imports Main
begin
(*>*)

text\<open> \cite{Fitting}
%
\begin{isabellebody}%
\def\isabellecontext{T{\isadigit{1}}SintaxisSemanticaP}%
%
\isadelimtheory
%
\endisadelimtheory
%
\isatagtheory
%
\endisatagtheory
{\isafoldtheory}%
%
\isadelimtheory
%
\endisadelimtheory
%
\begin{isamarkuptext}%
\label{cap4}%
\end{isamarkuptext}%
\isamarkuptrue%
%
\isamarkupsection{Sintaxis y Semántica Proposicional%
}
\isamarkuptrue%
%
\begin{isamarkuptext}%
\label{sintaxsemanticaP}
  En la lógica proposicional que consideramos, las fórmulas se construyen a partir de las
  conectivas  \isa{{\isasymbottom}{\isacharcomma}\ {\isasymtop}{\isacharcomma}\ {\isasymnot}{\isacharcomma}\ {\isasymand}{\isacharcomma}\ {\isasymor}{\isacharcomma}\ {\isasymlongrightarrow}}.
La sintaxis y semántica de la l\'ogica proposicional y su formalizaci\'on es la siguiente.

  \begin{definicion}
    El \textbf{alfabeto} de un lenguaje proposicional se compone de los
    siguientes símbolos.
    \begin{enumerate}
      \item \textbf{Símbolos lógicos:}
        \begin{itemize}
          \item conectivas: \isa{{\isasymbottom}{\isacharcomma}\ {\isasymtop}{\isacharcomma}\ {\isasymnot}{\isacharcomma}\ {\isasymand}{\isacharcomma}\ {\isasymor}{\isacharcomma}\ {\isasymlongrightarrow}}
          \item símbolos de puntuación: '(' , ')'\, , ','
        \end{itemize}
     \item \textbf{Símbolos no lógicos:}
         \begin{itemize}
           \item símbolos proposicionales $P_0, P_1, \dots$
         \end{itemize}
   \end{enumerate}
  \end{definicion}
  Las {\em fórmulas} se definen de la
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

  El siguiente tipo de datos define en Isabelle las fórmulas de la
  lógica proposicional.%
\end{isamarkuptext}%

\begin{isabellebody}%
\isacommand{datatype}\isamarkupfalse%
\ {\isacharprime}b\ formula\ {\isacharequal}\ \isanewline
\ \ \ \ FF\isanewline
\ \ {\isacharbar}\ TT\isanewline
\ \ {\isacharbar}\ Atomo\ {\isacharprime}b\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \isanewline
\ \ {\isacharbar}\ Neg\ \ \ \ \ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose}
\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}{\isachardoublequoteopen}{\isasymnot}{\isachardot}{\isacharparenleft}{\isacharunderscore}{\isacharparenright}{\isachardoublequoteclose}\ {\isacharbrackleft}{\isadigit{1}}{\isadigit{1}}{\isadigit{0}}{\isacharbrackright}\ {\isadigit{1}}{\isadigit{1}}{\isadigit{0}}{\isacharparenright}\isanewline
\ \ {\isacharbar}\ Conj\ \ \ \ {\isachardoublequoteopen}{\isacharprime}b\ formula\ \ \ \ {\isachardoublequoteclose}\ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose}
\ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}\isakeyword{infixl}\ {\isachardoublequoteopen}{\isasymand}{\isachardot}{\isachardoublequoteclose}\ \ {\isadigit{1}}{\isadigit{0}}{\isadigit{9}}{\isacharparenright}\isanewline
\ \ {\isacharbar}\ Disy\ \ \ \ {\isachardoublequoteopen}{\isacharprime}b\ formula\ \ \ \ {\isachardoublequoteclose}\ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose} \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}\isakeyword{infixl}\ {\isachardoublequoteopen}{\isasymor}{\isachardot}{\isachardoublequoteclose}\ \ {\isadigit{1}}{\isadigit{0}}{\isadigit{8}}{\isacharparenright}\isanewline
\ \ {\isacharbar}\ Implic\ \ {\isachardoublequoteopen}{\isacharprime}b\ formula\ \ \ \ {\isachardoublequoteclose}\ {\isachardoublequoteopen}{\isacharprime}b\ formula{\isachardoublequoteclose} \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ {\isacharparenleft}\isakeyword{infixl}\ {\isachardoublequoteopen}{\isasymrightarrow}{\isachardot}{\isachardoublequoteclose}\ {\isadigit{1}}{\isadigit{0}}{\isadigit{0}}{\isacharparenright}%
\end{isabellebody}%


%
\begin{isamarkuptext}%
En lo que sigue  presentamos la formalización de los conceptos
  semánticos de la lógica proposicional.  Para formalizar la noción
  de valor de una fórmula en una interpretación (\ref{valor}),
  se necesitan los conceptos de valores de verdad
  (\ref{vverdad}) e interpretación (\ref{interpretacion}).
  \label{semanticap}

  \begin{definicion}\label{vverdad}
    Los \textbf{valores de verdad} de la lógica proposicional clásica
    son $\V$ (que se interpreta como \textbf{verdadero}) y $\F$ (que se
    interpreta como \textbf{falso}).
  \end{definicion}

  En la formalización se identifica el conjunto de los valores de verdad
  con el tipo \emph{v-verdad}, el valor $\V$ con la constante
  \emph{Verdad} y el valor $\F$ con la constante \emph{Falso}
  respectivamente.%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{datatype}\isamarkupfalse%
\ v{\isacharunderscore}verdad\ {\isacharequal}\ Verdad\ {\isacharbar}\ Falso%
\begin{isamarkuptext}%
\begin{definicion}\label{interpretacion}
    Una \textbf{interpretación} es una aplicación del conjunto de los
    símbolos proposicionales en el conjunto de los valores de verdad.
  \end{definicion}

  La representación en Isabelle del concepto de interpretación es una
  función de la forma \isa{I\ \ {\isacharcolon}{\isacharcolon}\ {\isacharprime}b\ {\isasymRightarrow}\ \ v{\isacharunderscore}verdad}.

  Ahora se puede definir por recursión el valor de una fórmula respecto de una
  interpretación.

 \begin{definicion}\label{valor}
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

  Para formalizarlo, definimos las funciones de verdad de las conectivas.%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}negacion\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}negacion\ x\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Verdad\ then\ Falso\ else\ Verdad{\isacharparenright}{\isachardoublequoteclose}\isanewline
\isanewline
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}conjuncion\ {\isacharcolon}{\isacharcolon}\ \ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}conjuncion\ x\ y\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Falso\ then\ Falso\ else\ y{\isacharparenright}{\isachardoublequoteclose}\isanewline
\isanewline
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}disyuncion\ {\isacharcolon}{\isacharcolon}\ \ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}disyuncion\ x\ y\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Verdad\ then\ Verdad\ else\ y{\isacharparenright}{\isachardoublequoteclose}\isanewline
\isanewline
\isacommand{definition}\isamarkupfalse%
\ v{\isacharunderscore}implicacion\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}v{\isacharunderscore}implicacion\ x\ y\ {\isasymequiv}\ {\isacharparenleft}if\ x\ {\isacharequal}\ Falso\ then\ Verdad\ else\ y{\isacharparenright}{\isachardoublequoteclose}%
\begin{isamarkuptext}%
La formalización del valor de una fórmula es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{primrec}\isamarkupfalse%
\ valor\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}{\isacharprime}b\ {\isasymRightarrow}\ \ v{\isacharunderscore}verdad{\isacharparenright}\ {\isasymRightarrow}\ {\isacharprime}b\ formula\ \ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isachardoublequoteclose}\isanewline
\isakeyword{where}\isanewline
\ \ \ {\isachardoublequoteopen}valor\ I\ FF\ {\isacharequal}\ Falso{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ TT\ {\isacharequal}\ Verdad{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}Atomo\ p{\isacharparenright}\ {\isacharequal}\ I\ p{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}{\isasymnot}{\isachardot}\ F{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}negacion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}F\ {\isasymand}{\isachardot}\ G{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}conjuncion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}\ {\isacharparenleft}valor\ I\ G{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}F\ {\isasymor}{\isachardot}\ G{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}disyuncion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}\ {\isacharparenleft}valor\ I\ G{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}\isanewline
{\isacharbar}\ \ {\isachardoublequoteopen}valor\ I\ {\isacharparenleft}F\ {\isasymrightarrow}{\isachardot}\ G{\isacharparenright}\ {\isacharequal}\ {\isacharparenleft}v{\isacharunderscore}implicacion\ {\isacharparenleft}valor\ I\ F{\isacharparenright}\ {\isacharparenleft}valor\ I\ G{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}%

%
\begin{isamarkuptext}%
Formalizamos  las nociones de satisfactibilidad, consecuencia
  lógica y tautología en términos del concepto de \isa{modelo}.  Las
  demostraciones de las propieda\-des que se enuncian acerca de
  estos conceptos se obtienen directamente a partir de las definiciones.

  \begin{definicion}\label{modeloP}
    Una interpretación $I$ es \textbf{modelo} de un conjunto de fórmulas $S$
    si, para toda fórmula $F$ de $S$, $I'(F) = \V$.
  \end{definicion}

  \noindent Su formalización es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ modelo\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharparenleft}{\isacharprime}b\ {\isasymRightarrow}\ v{\isacharunderscore}verdad{\isacharparenright}\ {\isasymRightarrow}\ {\isacharprime}b\ formula\ set\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\ {\isacharparenleft}{\isachardoublequoteopen}{\isacharunderscore}\ modelo\ {\isacharunderscore}{\isachardoublequoteclose}\ {\isacharbrackleft}{\isadigit{8}}{\isadigit{0}}{\isacharcomma}{\isadigit{8}}{\isadigit{0}}{\isacharbrackright}\ {\isadigit{8}}{\isadigit{0}}{\isacharparenright}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}I\ modelo\ S\ {\isasymequiv}\ {\isacharparenleft}{\isasymforall}F\ {\isasymin}\ S{\isachardot}\ valor\ I\ F\ {\isacharequal}\ Verdad{\isacharparenright}{\isachardoublequoteclose}%
\begin{isamarkuptext}%
\begin{definicion}\label{satisfacibleP}
    Un conjunto de fórmulas es \textbf{satisfactible} si tiene algún modelo. En
    caso contrario se dice que es \textbf{insatisfactible}.
  \end{definicion}

  \noindent Su formalizacion es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ satisfacible\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharprime}b\ formula\ set\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}satisfacible\ S\ {\isasymequiv}\ {\isacharparenleft}{\isasymexists}v{\isachardot}\ v\ modelo\ S{\isacharparenright}{\isachardoublequoteclose}%
\begin{isamarkuptext}%
\begin{definicion}\label{consecuenciaP}
    Una fórmula $F$ es una \textbf{consecuencia lógica} de un conjunto de
    fórmulas $S$ si para todo modelo $I$ de $S$ se tiene que $I'(F) =\V$. Se
    representa por \isa{S\ {\isasymTurnstile}\ F}.
  \end{definicion}

  \noindent Su formalización es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ consecuencia\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharprime}b\ formula\ set\ {\isasymRightarrow}\ {\isacharprime}b\ formula\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\ {\isacharparenleft}{\isachardoublequoteopen}{\isacharunderscore}\ {\isasymTurnstile}\ {\isacharunderscore}{\isachardoublequoteclose}\ {\isacharbrackleft}{\isadigit{8}}{\isadigit{0}}{\isacharcomma}{\isadigit{8}}{\isadigit{0}}{\isacharbrackright}\ {\isadigit{8}}{\isadigit{0}}{\isacharparenright}\ \isakeyword{where}\isanewline
\ {\isachardoublequoteopen}S\ {\isasymTurnstile}\ F\ {\isasymequiv}\ {\isacharparenleft}{\isasymforall}I{\isachardot}\ I\ modelo\ S\ {\isasymlongrightarrow}\ valor\ I\ F\ {\isacharequal}\ Verdad{\isacharparenright}{\isachardoublequoteclose}%
\begin{isamarkuptext}%
El siguiente resultado establece la relación entre los conceptos de
  consecuencia lógica y satisfactibilidad.%
\end{isamarkuptext}%
\isamarkuptrue%
%
\isadelimproof
%
\endisadelimproof
%
\isatagproof
%
\endisatagproof
{\isafoldproof}%
%
\isadelimproof
%
\endisadelimproof
%
\isadelimproof
%
\endisadelimproof
%
\isatagproof
%
\endisatagproof
{\isafoldproof}%
%
\isadelimproof
%
\endisadelimproof
%
\begin{isamarkuptext}%
\begin{teorema}\label{EquiConsSat}
  \isa{S\ {\isasymTurnstile}\ F} si y solamente si \isa{S\ {\isasymunion}\ {\isacharbraceleft}{\isasymnot}\ F{\isacharbraceright}} no es satisfactible.
  \end{teorema}

  \noindent Su formalización es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{theorem}\isamarkupfalse%
\ EquiConsSat{\isacharcolon}\ \isanewline
\ \ \isakeyword{shows}\ \ {\isachardoublequoteopen}S\ {\isasymTurnstile}\ F\ {\isacharequal}\ {\isacharparenleft}{\isasymnot}\ satisfacible\ {\isacharparenleft}S\ {\isasymunion}\ {\isacharbraceleft}{\isasymnot}{\isachardot}\ F{\isacharbraceright}{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}%
\isadelimproof
%
\endisadelimproof
%
\isatagproof
%
\endisatagproof
{\isafoldproof}%
%
\isadelimproof
%
\endisadelimproof
%
\begin{isamarkuptext}%
Por último formulamos el concepto de tautología.

  \begin{definicion}
    Una fórmula $F$ es una \textbf{tautología} si $I'(F) =\V$ para toda
    interpretación $I$.
  \end{definicion}

  \noindent Su formalización es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{definition}\isamarkupfalse%
\ tautologia\ {\isacharcolon}{\isacharcolon}\ {\isachardoublequoteopen}{\isacharprime}b\ formula\ {\isasymRightarrow}\ bool{\isachardoublequoteclose}\ \isakeyword{where}\isanewline
\ \ {\isachardoublequoteopen}tautologia\ F\ {\isasymequiv}\ {\isacharparenleft}{\isasymforall}I{\isachardot}\ {\isacharparenleft}{\isacharparenleft}valor\ I\ F{\isacharparenright}\ {\isacharequal}\ Verdad{\isacharparenright}{\isacharparenright}{\isachardoublequoteclose}%


%
\begin{isamarkuptext}%
El concepto de tautología se puede formular en términos del concepto
  de consecuencia lógica:%
\end{isamarkuptext}%
\isamarkuptrue%
%
\isadelimproof
%
\endisadelimproof
%
\isatagproof
%
\endisatagproof
{\isafoldproof}%
%
\isadelimproof
%
\endisadelimproof
%
\begin{isamarkuptext}%
\begin{teorema}
  Una fórmula es tautología si y solamente si es consecuencia del conjunto vacío.
  \end{teorema}

  \noindent Su formalizacion es:%
\end{isamarkuptext}%
\isamarkuptrue%
\isacommand{theorem}\isamarkupfalse%
\ CNS{\isacharunderscore}tautologia{\isacharcolon}\ {\isachardoublequoteopen}tautologia\ F\ {\isacharequal}\ {\isacharparenleft}{\isacharbraceleft}{\isacharbraceright}\ {\isasymTurnstile}\ F{\isacharparenright}{\isachardoublequoteclose}%
\isadelimproof
%
\endisadelimproof
%
\isatagproof
%
\endisatagproof
{\isafoldproof}%
%
\isadelimproof
%
\endisadelimproof
%
\end{isabellebody}%
\<close>

(*<*)
end
(*>*)
