# Resumo da modificações

Estão listado apenas os comentários que não são relacionados à gramática. Os demais comentários sobre gramática foram acatados.

|Reviewer | Where in the thesis |Reviewer's comments  | My comments  |
|---------|---------------------|---------------------|-------------|
| gnr | Seção 1.2, p. 32 | bizantine (inconsistent) failure? Completeness/coverage analysis of the model available? | São outras análises que poderiam ser feitas. Nós focamos no não-determinismo porque avaliamos que seria mais utilizado principalmente com a experiência com CSP. As heatlhiness conditions tratam a completude na análise.  |
| gnr | Seção 1.3, p. 33  [selecionado _fault injection_] | failure prediction via Simulink + CSP? | Não. Os trabalhos sobre fault injection estão citados. |
| gnr | Seção 1.3, p. 33 [selecionado _the probability of a complete failure of an airplane engine should be less than 10^-9_] | Probabilistic Existence property (see Proprost by Lars Grunske (ICSE 2008)) as PCTL property. - How can you guarantee such precision? | Não se pode garantir tal precisão no cálculo. Os requisitos são dados em ordem de grandeza. O texto selecionado é apenas um exemplo e expressa a ordem de grandeza. |
| gnr | Seção 1.3, p. 33  [selecionado _the communication system should be operational 99.99% of the cruise phase_] | could be expressed as a PCTL property. | Sim, poderia. Toda análise sobre ordem de ocorrência de eventos poderia ser escrita usando CTL. O objetivo do trabalho é desenvolver um modelo matemático para TFT e DFT. Sem alterações. |
| gnr | Seção 2.1.2, p. 38  [selecionado _on the environment_] | notice that it should refer to the environment. | Sem alterações. |
| gnr | Seção 2.1.2, p. 40  [selecionado _safety_] | is it really safety or reliability? where is the environment taken into account? | As árvores de falha estão relacionadas a _safety_, pois dizem respeito a uma falha catastrófica. Portanto a análise realizada usando AL e ATF dizem respeito a safety. |
| gnr | Seção 3.1, p. 47  [selecionado {a,b,c} ] | why c? | Texto corrigido com explicação sobre c. |
| gnr | Seção 3.1, p. 49 | Diversas seleções. | Ajustes nos acrônimos. |
| gnr | Seção 3.2.2, p. 56  [selecionado _BDD_] | onde foram usados? Por que fazem parte de seu background? | Toda a seção sobre análise de expressões de estrutura foi removida. Foram realizados ajustes pontuais em outras páginas onde esta seção era referenciada. |
| gnr | Seção 3.4.3, p. 67  [selecionado _Eq. 3.9_] | não seria para a 3.10? E não estaria faltando um termo? Pprv X Pi1 no lugar de Pprv? | Esta é uma fórmula trazida da referência citada. Ela está correta. Basta desenvolver os termos com as respectivas probabilidades. |
| gnr | Seção 4.4.2, p. 89  [selecionado _The work reported in [3] shows how to..._] | Background work| Foi inserida uma seção 3.3 sobre probabilidades com parte do texto desta seção. Outras informações foram acrescentadas à nova seção. |
| gnr | Seção 4.4.3, p. 93  [selecionado _Safety requirements are written..._] | where is such specification/requirements specified? | Foram acrescentadas referências sobre exemplos de tais requisitos. |
| gnr | Seção 5.2, p. 97 [selecionado título da seção] | System performs as expected -> reliability. It could also be expressed as Liveness? Why not this one? | São outras propriedades que poderiam ser analisadas, mas que ficaram de fora do escopo. Acrescentamos na conclusão comentário sobre trabalhos futuros com estas propriedades. |
| gnr | Seção 5.3, p. 100 [selecionado o título da seção] | How does it connect to fault itself? | Isso está explicado na introdução. |
| gnr | Seção 5.4, p. 101 [selecionado _Non-determinism is the possibility..._] | what would be the case that the failure either happens or not inconsistently? | Só são considerados _snapshots_ do estado do sistema. Em um único modelo é possível expressar mais de um estado do sistema, mesmo assim são snapshots. A inconsistência da ocorrência pode ser modelada como uma falha. Não modificamos o texto, pois não achamos que valeria a pena entrar neste detalhe na seção. |



Authors:
* gnr: Genaina
* prmm: Paulo 
* jmi: Juliano 
* acas: Augusto
* eald: Enrique