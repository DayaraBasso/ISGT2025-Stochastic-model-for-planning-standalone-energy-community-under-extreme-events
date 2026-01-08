##############################################
# MODELO

# definição de conjuntos
set P:=1..10000; #conjunto de candidatas a instalar paineis
set B:=1..50; # conjunto de candidatas a instalar baterias
set H:=1..24;  # conjunto de horas do dia
set S; #cenarios
set SN; # conjunto dos cenários normais
set SE; # conjunto dos cenários extremos
set K:= 1..3;  # conjunto dos veículos eletricos

# definição dos parâmetros

#baterias
param eta_c_BAT; #eficiencia de carga das baterias
param eta_d_BAT; #eficiencia de descarga das baterias 
param c_b; #custo de cada bateria
param P_BAT_nom; #potencia nominal de cada bateria
param E_BAT_nom >= 0; #energia da bateria nominal# veículos elétricos
param eta_c_VE; #eficiencia de carga dos VEs
param eta_d_VE; #eficiencia de descarga dos VEs
param SOC_max; #SOC maximo do VE (kWh)
param SOC_min; #SOC minimo do VE (kWh)
param Pcargamax; # Potência máxima de carregamento do VE (kW)
param c_ve; #custo veiculo elétrico

# painéis fotovoltaicos
param Noct; # temperatura que o painel chega em 800 W/m2
param Voc;  # tensão de circuito aberto
param Isc;  # corrente de curto circuito
param Kv; # coeficiente de temperatura para a tensão
param Ki; # coeficiente de temperatura para a corrente
param Vmppt; # tensão  em ponto de máxima potência
param Imppt;  # corrente em ponto de máxima potência
param Ta; #temperatura ambiente
param c_p; #custo de cada painel fotovoltaico
param Tc{H,S} >= 0; #temperatura na celula fotovoltaica
param Ic{H,S} >= 0; #corrente na celula fotovoltaica
param Vc{H,S} >= 0; #tensão na celula fotovoltaica
param P_pv_m{H,S} >= 0; #potencia do painel fotovoltaico
param G{H,S}; #irradiação solar
param FF >= 0; #fator de forma

# sistema e modelo
param P_EC_nom{H}; #demanda do edificio 
param lambda_ls >= 0; # taxa de load shift pra deslocamento de carga do edificio
param alpha >= 0; # taxa de trazer o valor presente
param pi{S} >= 0; # probabilidade de cada cenário ocorrer
param taxa_juros; # 10% de taxa de juros para trazer o valor presente
param vida_util; # Vida útil da bateria do VE (anos)
param dias_ano; # dias úteis no ano
param lambda1{H}; # penalização para deslocamento de carga do edificio
param lambda2 >=0; # penalização para descarga do VE
param lambda3 >=0; #peso para penalizar a potência indisponível 
param omegaEV >= 0;  # capacidade do estado de carga da bateria do EV



# definição das variáveis
var z{P} binary; # variavel binária de instalaçao de paineis fotovoltaicos
var y{B} binary; # variavel binaria de instalaçao de baterias
var P_BAT_c {B,H,S} >= 0; #potencia de carga da bateria
var P_BAT_d {B,H,S} >= 0; # potencia de descarga da bateria
var E_BAT {B,H,S} >= 0; #energia da bateria
var P_pv{H,S} >= 0; # potencia do painel fotovoltaico
var w1{B,H,S} binary;  # variavel binaria pra bateria nao carregar e descarregar simultaneamente
var P_EC{H,S} >= 0; # potencia horária do edificio inteligente
var P_ind{H,SE} >= 0; # potencia indisponivel
var P_EV_c {K,H,S} >= 0; #potencia de carga do VE
var P_EV_d {K,H,S} >= 0; # potencia de descarga do VE
var E_EV {K,H,S} >= 0; # estado de carga do VE
var w2{B,H,S} binary;  # variavel binaria para o VE nao carregar e descarregar simultaneamente
var omega >= 0 <= 1; # capacidade da bateria
var zeta{B} >= 0 <= 1; # variavel auxiliar para linearização do omega 
var P_LS{H,S};
var u{H,S} binary;
var P_LS_ABS{H,S} >= 0;
var P_LS_POS{H,S} >= 0;
var P_LS_NEG{H,S} >= 0;



# FUNÇÃO OBJETIVO
#(1º termo: minimiza a instalaçao de paineis fotovoltaicos, 2º termo: minimiza a instalação de baterias, 3º termo: penaliza a operação - deslocamento de carga + potencia indisponível + descarga do VE)
minimize fo:
    sum{p in P} z[p] * c_p + sum{b in B} y[b] * c_b +
	alpha * ( (sum{s in SE} pi[s] * (sum{h in H} (P_LS_POS[h,s] + P_LS_NEG[h,s] )* lambda1[h])) + 
    (lambda2 * sum{k in K, se in SE, h in H} pi[se] *P_EV_d[k,h,se]) +
	(lambda3 * sum{se in SE, h in H} pi[se] *P_ind[h,se]));


##########################################################################
# RESTRIÇÕES
	
# limita a potencia de descarga e carga de cada veículo a um mínimo 
# e evita que carregue e descarregue ao mesmo tempo
subject to restricaoEV1 {k in K, h in H, s in S}:
	P_EV_d[k,h,s] >= 0;
subject to restricaoEV2 {k in K, h in H, s in S}:
	P_EV_d[k,h,s] <= Pcargamax * w2[k,h,s];
subject to restricaoEV3 {k in K, h in H, s in S}:
	P_EV_c[k,h,s] >= 0;
subject to restricaoEV4 {k in K, h in H, s in S}:
	P_EV_c[k,h,s] <= Pcargamax * (1 - w2[k,h,s]);

# limita o estado de carga do VE a um máximo e a um minimo
subject to restricaoEV7 {k in K, h in H, s in S}:
	E_EV[k,h,s] >= SOC_min;
subject to restricaoEV8 {k in K, s in S, h in H: h == 1}:
	E_EV[k,h,s] <= SOC_max;

subject to restricaoEV15 {k in K, s in S, h in H}:
	E_EV[k,h,s] <= SOC_max;

# calcula o estado de carga do VE quando não é inicio
subject to restricaoEV10 {k in K, s in S, h in H : h>1}:
	E_EV[k,h,s] - E_EV[k, h-1, s] = eta_c_VE*P_EV_c[k,h,s] - (1/eta_d_VE)*P_EV_d[k,h,s];

	
# limita a potencia de carga e de descarga horária de cada bateria a um máximo
subject to restricaoEV12 {k in K, h in H, s in S}:
	P_EV_c[k,h,s] <= Pcargamax;
subject to restricaoEV13 {k in K, h in H, s in S}:
	P_EV_d[k,h,s] <= Pcargamax;

# Define que a energia da bateria do VE ao final do dia deve ser igual ao valor nominal
subject to restricaoEV14 {k in K, s in SN, h in H: h == 24}:
	E_EV[k,h,s] >= E_EV[k,h-23,s];

##################################
	
# limita a potencia horária dos paineis fotovoltaicos a um mínimo e um máximo
subject to restricaoPV1 {h in H, s in S}:
	P_pv[h,s] >= 0;
subject to restricaoPV2{h in H,s in S}:
	P_pv[h,s] <= sum{p in P} z[p] * P_pv_m[h,s]; 
	
#######################################

# limita a potencia de descarga e carga horária de cada bateria a um mínimo 
# e evita que elas carreguem e descarreguem ao mesmo tempo
subject to restricaoBAT1 {b in B, h in H, s in S}:
	P_BAT_d[b,h,s] >= 0;
subject to restricaoBAT2 {b in B, h in H, s in S}:
	P_BAT_d[b,h,s] <= P_BAT_nom * w1[b,h,s];
subject to restricaoBAT3 {b in B, h in H, s in S}:
	P_BAT_c[b,h,s] >= 0;
subject to restricaoBAT4 {b in B, h in H, s in S}:
	P_BAT_c[b,h,s] <= P_BAT_nom * (1 - w1[b,h,s]);

subject to restricaoBAT5 {b in B, h in H, s in S}:
	P_BAT_c[b,h,s] <= P_BAT_nom * y[b];
subject to restricaoBAT6 {b in B, h in H, s in S}:
	P_BAT_d[b,h,s] <= P_BAT_nom * y[b];


# limita a energia de cada bateria a um máximo e a um minimo
subject to restricaoBAT7{b in B, h in H, s in S}:
	E_BAT[b,h,s] >= 0;
subject to restricaoBAT8 {b in B, s in S, h in H: h == 1}:
	E_BAT[b,h,s] <= E_BAT_nom * y[b];

# calcula a energia de cada bateria quando não é inicio
subject to restricaoBAT10 {b in B, s in S, h in H : h>1}:
	E_BAT[b,h,s] - E_BAT[b, h-1, s] = eta_c_BAT*P_BAT_c[b,h,s] - (1/eta_d_BAT)*P_BAT_d[b,h,s];

# Define que a energia da bateria ao final do dia deve ser igual ao valor nominal
subject to restricaoBAT11 {b in B, s in SN, h in H: h == 24}:
	E_BAT[b,h,s] >= E_BAT[b,h-23,s];



	##################################
	
# restrições do edificio inteligente
# realiza uma transferencia de carga com um load shift máximo
subject to restricaoEC1 {h in H, s in SE, se in SE}:
	P_EC[h,s] <= P_EC_nom[h] * (1 + lambda_ls);

# realiza uma transferencia de carga com um load shift mínimo
subject to restricaoEC2 {h in H, s in SE, se in SE}:
	P_EC[h,s] >= P_EC_nom[h] * (1 - lambda_ls);
	
# nao realiza deslocamento em cenarios normais
subject to restricaoEC4 {h in H, s in SN}:
	P_EC[h,s] = P_EC_nom[h];


# faz a soma da potencia do edificio, para que a transferencia de carga continue atendendo a carga total do EI
subject to restricaoEC3 {s in S}:
	sum{h in H} P_EC_nom[h] = sum{h in H} P_EC[h,s];

# calculo despacho
subject to restricaoEC5 {h in H, s in SE}:
	P_LS[h,s] = P_EC_nom[h] - P_EC[h,s];
	
subject to restricaolinear2 {h in H, s in SE}:
	P_LS[h,s] = P_LS_POS[h,s] - P_LS_NEG[h,s];

subject to restricaolinear3 {h in H, s in SE}:
	P_LS_POS[h,s] >= 0;

subject to restricaolinear4 {h in H, s in SE}:
	P_LS_NEG[h,s] >= 0;


############################

## restrições da potencia indisponível
subject to restricaopotenciaindis1 {h in H, se in SE}:
	P_ind[h,se] >= 0;
subject to restricaopotenciaindis2 {h in H, se in SE}:
	P_ind[h,se] <= P_EC_nom[h];
	
	
###########################################
# restrições de balanço de potencia
# balanco de potencia total:a potencia gerada pelos paineis, a potencia de descarga das baterias, a descarga dos VEs, a indisponível deve ser igual ao total de potencia consumida pelo edificio e a carga dos VEs
subject to restricaobalancopotencia {h in H,s in SE}:
	P_pv[h,s]  + sum{b in B} P_BAT_d[b,h,s] + P_ind[h,s] + sum {k in K} P_EV_d[k,h,s] >= sum{b in B} P_BAT_c[b,h,s] + sum{k in K} P_EV_c[k,h,s] + P_EC[h,s];
 
 
 # restrição energia mínima cenários normais
subject to restricaobalancopotencia1 {h in H,s in SN}:
	P_pv[h,s]  + sum{b in B} P_BAT_d[b,h,s]  >= sum{b in B} P_BAT_c[b,h,s] + P_EC[h,s];
	
	
