# Resumo da modificações

Estão listado apenas os comentários que não são relacionados à gramática. Os demais comentários sobre gramática foram acatados.

|Reviewer | Where in the thesis |Reviewer's comments  | My comments  |
|---------|---------------------|---------------------|-------------|
| prmm | _Geral_ | Quem seriam os usuários deste modelo? Seriam engenheiros/administradores que já estejam habituados à notação de FT que têm dificuldades de representar em FT problemas com dependências complexas (que não são possíveis de serem representadas com a FT básicas)? | Acrescentamos como trabalho futuro uma ferramenta que use diretamente a a álgebra de modo que a utilização da teoria fique mais amigável |
| prmm | _Geral_ | Com este modelo eles seriam capazes de avaliar problemas que são difíceis de se avaliar com as FT básicas. Seriam esses, os usuários? | Sim. Para árvores de falha que tenham noção de ordem de eventos. |
| prmm | _Geral_ | [...] Portanto, entendo que seja muito importante comparar os resultados das TFT e das respectivas CTMCs/DTMCs. | De fato, não realizamos tal comparação e não a pesquisamos diretamente, talvez já exista. Para nosso resulado não seria relevante, a priori, pois obtemos resultados específicos com AL e a ATF, como é o caso das healthiness conditions. |
| prmm | p. 29 | "much richer" than what? Confuso! | Texto ajustado. |
| prmm | p. 30 [citando os trabalhos de Walker e Papadopoulos] | Esses 3 trabalhos são dos mesmos autores! Trabalhos de 2008 e 2009. Ninguém usa/adota esse modelo? Por quê? Há, pelo menos, 1 trabalho mais antigo. Esse: Palshikar2002 | O trabalho de Palshikar acrescenta LTL nos nós. Citamos este trabalho na seção 3.1.2. Este trabalho não teve continuidade e achamos que não precisaria comparar nossa contribuição com a deles, apesar do nome parecido. |
| gnr | Seção 1.2, p. 32 | bizantine (inconsistent) failure? Completeness/coverage analysis of the model available? | São outras análises que poderiam ser feitas. Nós focamos no não-determinismo porque avaliamos que seria mais utilizado principalmente com a experiência com CSP. As heatlhiness conditions tratam a completude na análise.  |
| gnr | Seção 1.3, p. 33  [selecionado _fault injection_] | failure prediction via Simulink + CSP? | Não. Os trabalhos sobre fault injection estão citados. |
| gnr | Seção 1.3, p. 33 [selecionado _the probability of a complete failure of an airplane engine should be less than 10^-9_] | Probabilistic Existence property (see Proprost by Lars Grunske (ICSE 2008)) as PCTL property. - How can you guarantee such precision? | Não se pode garantir tal precisão no cálculo. Os requisitos são dados em ordem de grandeza. O texto selecionado é apenas um exemplo e expressa a ordem de grandeza. |
| gnr | Seção 1.3, p. 33  [selecionado _the communication system should be operational 99.99% of the cruise phase_] | could be expressed as a PCTL property. | Sim, poderia. Toda análise sobre ordem de ocorrência de eventos poderia ser escrita usando CTL. O objetivo do trabalho é desenvolver um modelo matemático para TFT e DFT. Sem alterações. |
| prmm | p. 34 | Qual é a principal contribuição de sua tese? | Esta detalhado na seção 1.4 |
| prmm | p. 35 [citando _"It starts with Simulink modelling, converts the model to CSP M and then obtains fault event sequences (also called fault traces). The fault event sequences are then mapped to ATF, which has a denotational semantics based on sets of lists."_]| Só na frase acima, percebe-se que usa 3 modelo e faz 2 mapeamentos (duas "traduções") Não está claro para que tudo isso? Que modelo é adotado no Simulink? | Isso é explicado na seção 3.5. Tem o objetivo de realização injeção de falhas, que é o título do bloco na figura, citado no texto: _The "Faults injection" block is obtained from part of our work reported ..._ |
| gnr | Seção 2.1.2, p. 38  [selecionado _on the environment_] | notice that it should refer to the environment. | Sem alterações. |
| gnr | Seção 2.1.2, p. 40  [selecionado _safety_] | is it really safety or reliability? where is the environment taken into account? | As árvores de falha estão relacionadas a _safety_, pois dizem respeito a uma falha catastrófica. Portanto a análise realizada usando AL e ATF dizem respeito a safety. |
| gnr | Seção 3.1, p. 47  [selecionado {a,b,c} ] | why c? | Texto corrigido com explicação sobre c. |
| jmi | Seção 3.1, p. 47 | [selecionado {a,b,c}] | A Figura 9 não tem c | Texto corrigido com explicação sobre c. |
| gnr | Seção 3.1, p. 49 | Diversas seleções. | Ajustes nos acrônimos. |
| jmi | Seção 3.1, p. 54 | Introduzir melhor a notação dos triângulos | Acrescentamos explicação sobre os símbolos. |
| gnr | Seção 3.2.2, p. 56  [selecionado _BDD_] | onde foram usados? Por que fazem parte de seu background? | Toda a seção sobre análise de expressões de estrutura foi removida. Foram realizados ajustes pontuais em outras páginas onde esta seção era referenciada. |
| jmi | Seção 3.2, p. 57 | A linha d também não produz 0? | A seção inteira foi removida. |
| jmi | Seção 3.3, p. 62 | Estranho porque X é uma variável ligada [selecionado _{ X | s \in X }_] | Notação ajustada. |
| gnr | Seção 3.4.3, p. 67  [selecionado _Eq. 3.9_] | não seria para a 3.10? E não estaria faltando um termo? Pprv X Pi1 no lugar de Pprv? | Esta é uma fórmula trazida da referência citada. Ela está correta. Basta desenvolver os termos com as respectivas probabilidades. |
| jmi | Seção X, p. 79 | Introduzir UNIV aqui. [sobre a notação da semântica denotacional de _var_] | Notação ajustada. |
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