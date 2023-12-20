#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Fri Mar 31 15:34:06 2023


This file is to generate all trees of size between 1 and n vertices with n growing from 2 up to maxn vertices
"""

import csv
import pandas as pd
import numpy as np
import time
from utility_to_gen_all_tree import gen_tree_taille_max
import sys


 

taille_max_tree = int(sys.argv[1])

tree = gen_tree_taille_max(taille_max_tree,True).sort_values(by="v")
tree.to_csv("tree_" +str(taille_max_tree)+ ".csv")


combinaisons_list = [(['v', 'maxp'], 1),
 (['v', 'minp'], 2),
 (['v', 'maxd'], 3),
 (['v', 'mind'], 4),
 (['v', 'f'], 5),
 (['v', 'maxp', 'f'], 6),
 (['v', 'maxp', 'mind'], 7),
 (['v', 'maxp', 'maxd'], 8),
 (['v', 'maxp', 'minp'], 9),
 (['v', 'minp', 'maxp'], 10),
 (['v', 'minp', 'f'], 11),
 (['v', 'minp', 'mind'], 12),
 (['v', 'minp', 'maxd'], 13),
 (['v', 'maxd', 'minp'], 14),
 (['v', 'maxd', 'maxp'], 15),
 (['v', 'maxd', 'f'], 16),
 (['v', 'maxd', 'mind'], 17),
 (['v', 'mind', 'maxd'], 18),
 (['v', 'mind', 'minp'], 19),
 (['v', 'mind', 'maxp'], 20),
 (['v', 'mind', 'f'], 21),
 (['v', 'f', 'mind'], 22),
 (['v', 'f', 'maxd'], 23),
 (['v', 'f', 'minp'], 24),
 (['v', 'f', 'maxp'], 25),
 (['v', 'minp', 'maxp', 'f'], 26),
 (['v', 'minp', 'maxp', 'mind'], 27),
 (['v', 'minp', 'maxp', 'maxd'], 28),
 (['v', 'maxd', 'minp', 'maxp'], 29),
 (['v', 'maxd', 'minp', 'f'], 30),
 (['v', 'maxd', 'minp', 'mind'], 31),
 (['v', 'maxd', 'maxp', 'minp'], 32),
 (['v', 'maxd', 'maxp', 'f'], 33),
 (['v', 'maxd', 'maxp', 'mind'], 34),
 (['v', 'mind', 'maxd', 'maxp'], 35),
 (['v', 'mind', 'maxd', 'minp'], 36),
 (['v', 'mind', 'maxd', 'f'], 37),
 (['v', 'mind', 'minp', 'maxd'], 38),
 (['v', 'mind', 'minp', 'maxp'], 39),
 (['v', 'mind', 'minp', 'f'], 40),
 (['v', 'mind', 'maxp', 'minp'], 41),
 (['v', 'mind', 'maxp', 'maxd'], 42),
 (['v', 'mind', 'maxp', 'f'], 43),
 (['v', 'f', 'mind', 'maxp'], 44),
 (['v', 'f', 'mind', 'minp'], 45),
 (['v', 'f', 'mind', 'maxd'], 46),
 (['v', 'f', 'maxd', 'mind'], 47),
 (['v', 'f', 'maxd', 'maxp'], 48),
 (['v', 'f', 'maxd', 'minp'], 49),
 (['v', 'f', 'minp', 'maxd'], 50),
 (['v', 'f', 'minp', 'mind'], 51),
 (['v', 'f', 'minp', 'maxp'], 52),
 (['v', 'f', 'maxp', 'minp'], 53),
 (['v', 'f', 'maxp', 'maxd'], 54),
 (['v', 'f', 'maxp', 'mind'], 55)]
 
def initial_dic_comb_dic_value(combinaisons,list_carac_names):
    #tps1 = time.time()
    dic_comb_dic_value = {}
    for (combinaison,ind_comb) in combinaisons:
        dic_comb_dic_value[ind_comb] = {}
        dic_comb_dic_value[ind_comb]["att"] = list_carac_names
    #tps2 = time.time()
    #print("initial_dic_comb_dic_value made:",tps2-tps1,"s")
    return dic_comb_dic_value

def get_complement_comb(combinaison,list_carac_names):
    compl_comb = []
    for att_string in list_carac_names:
        if att_string not in combinaison:
                compl_comb.append(att_string)
    return compl_comb

def transform_row_key(row,combinaison):
    row_comb_values_entries = "["+row[combinaison[0]]
    for att_string in combinaison[1:-1]:
            row_comb_values_entries = row_comb_values_entries + "," + row[att_string]
    row_comb_values_entries = row_comb_values_entries + "]"
    return row_comb_values_entries

    
    
def delete_undependant_sec(row0,row,cur_list_atts):
    
    new_list_atts = []
    for att in cur_list_atts:
        if row0[att] == row[att]:
            new_list_atts.append(att)
    return new_list_atts

def buil_row_dependant_sec(row,cur_list_atts):
    
    row_dependant_sec = {}
    for att in cur_list_atts:
        row_dependant_sec[att] = row[att]
    return row_dependant_sec

def gen_name_datatable(combinaison):
    name_datatable = ""
    for param in combinaison:
        param_sans_moins = param.replace('-','').lower()
        name_datatable =  name_datatable + "_" + param_sans_moins                    
    return name_datatable

def write_ext_table(combinaison,ind_comb,dic_comb_dic_value,lowup):
    cur_list_atts = dic_comb_dic_value[ind_comb]["att"]
    compl_comb = get_complement_comb(combinaison,cur_list_atts)
    ext_data = []
    for ext_row in dic_comb_dic_value[ind_comb].values():
        if ext_row != dic_comb_dic_value[ind_comb]["att"]:
            ext_data.append(ext_row)
    df = pd.DataFrame(data = ext_data, columns = cur_list_atts)[combinaison + compl_comb]
    if lowup == "up":
        df.to_csv("ext_tree/up"+gen_name_datatable(combinaison)+".csv")
    else:
        df.to_csv("ext_tree/low"+gen_name_datatable(combinaison)+".csv")
    return df


def gen_forest_csv_tables(combinaisons_list,list_carac_names,lowup):
    tps1 = time.time()
    dic_comb_dic_value = initial_dic_comb_dic_value(combinaisons_list,list_carac_names)
    
    with open("tree_"+str(taille_max_tree)+".csv", newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            
            for row in reader:
                for (combinaison,ind_comb) in combinaisons_list:
                    output = combinaison[-1]
                    row_key_entry = transform_row_key(row,combinaison)
                    if row_key_entry not in dic_comb_dic_value[ind_comb].keys():
                                            dic_comb_dic_value[ind_comb][row_key_entry] = row
               
                    elif lowup == "up" :
                          if int(dic_comb_dic_value[ind_comb][row_key_entry][output]) < int(row[output]):
                                dic_comb_dic_value[ind_comb][row_key_entry] = row
                                
                    elif lowup == "low" :
                          if int(dic_comb_dic_value[ind_comb][row_key_entry][output]) > int(row[output]):
                                dic_comb_dic_value[ind_comb][row_key_entry] = row
                                
    with open("tree_"+str(taille_max_tree)+".csv", newline='') as csvfile:
            reader = csv.DictReader(csvfile)
            
            for row in reader:
                for (combinaison,ind_comb) in combinaisons_list:
                    output = combinaison[-1]
                    row_key_entry = transform_row_key(row,combinaison)
                    
                    if    dic_comb_dic_value[ind_comb][row_key_entry][output] == row[output]:
                            new_list_att = delete_undependant_sec(dic_comb_dic_value[ind_comb][row_key_entry],row,dic_comb_dic_value[ind_comb]["att"])
                            dic_comb_dic_value[ind_comb]["att"] = new_list_att
                          
    for (combinaison,ind_comb) in combinaisons_list:
        for row in dic_comb_dic_value[ind_comb].values():
            
            if row != dic_comb_dic_value[ind_comb]["att"]:
                row_key_entry = transform_row_key(row,combinaison)
                row_dependant_sec = buil_row_dependant_sec(row,dic_comb_dic_value[ind_comb]["att"])
                dic_comb_dic_value[ind_comb][row_key_entry] = row_dependant_sec
        write_ext_table(combinaison,ind_comb,dic_comb_dic_value,lowup)        
    tps2 = time.time()
    print("gen_forest_csv_tables made:",tps2-tps1,"s")

list_carac_names = ["v", "f","mind","maxd", "minp","maxp"]
gen_forest_csv_tables(combinaisons_list,list_carac_names,"up")
gen_forest_csv_tables(combinaisons_list,list_carac_names,"low")


def ecris_parametres(dataframe_tabledata,lowup,bounded,nb_param):
    list_parametres = ""
    k = 0
    for parametre in dataframe_tabledata.columns[1:-1]:
        k = k + 1
        param_sans_moins = parametre.replace('-','').lower()
        if param_sans_moins == bounded:
            list_parametres = list_parametres + "t("+param_sans_moins+","+lowup+",output),\n"
        elif k <= nb_param : 
            list_parametres = list_parametres + "t("+param_sans_moins+",primary,input),\n"
        else:
            list_parametres = list_parametres + "t("+param_sans_moins+",secondary,input),\n" 
    
           
    if dataframe_tabledata.columns[-1] == bounded:
        list_parametres = list_parametres + "t("+dataframe_tabledata.columns[-1]+","+lowup+",output)\n"
    else:
        list_parametres = list_parametres + "t("+dataframe_tabledata.columns[-1]+",secondary,input)\n"  
    return list_parametres

def ecrire_un_fait(nom_de_la_table,entreetable):
    fait = nom_de_la_table+"("
    for valeur in entreetable[1:-1]:
        fait = fait + str(int(valeur))+","
    fait = fait + str(int(entreetable[-1])) + ").\n" 
    return fait
        
def ecris_les_faits_prolog(nom_de_la_table,dataframe_tabledata):
    list_faits_prolog = ""
    for entreetable in dataframe_tabledata.values.tolist():
        list_faits_prolog = list_faits_prolog + ecrire_un_fait(nom_de_la_table,entreetable)
    return list_faits_prolog
    

    
def trans_allfeaturestabledata_prolog(nom_de_la_tab,dataframe_tabledata,lowup,maxn,bounded,nb_param,objet_combinatoire):
    nom_de_la_table = lowup+nom_de_la_tab
    
    nom_table_prolog = "data_"+objet_combinatoire+"/data"+str(maxn)+"/" + nom_de_la_table + ".pl"
    nb_col = dataframe_tabledata.shape[1]-1
    fichier0 = open(nom_table_prolog, "w")
    fichier0.write(":- multifile signature/3.\n"+
                  ":- multifile "+ nom_de_la_table+"/"+str(nb_col)+".\n"+
                  ":- dynamic signature/3.\n"+
                  ":- dynamic "+ nom_de_la_table+"/"+str(nb_col)+".\n\n"+
                  "signature("+ nom_de_la_table+","+str(maxn)+",t(\n"+
                  ecris_parametres(dataframe_tabledata,lowup,bounded,nb_param)+")).\n\n"+
                  ecris_les_faits_prolog(nom_de_la_table,dataframe_tabledata))
    fichier0.close() 
    
for (combinaison,ind_comb) in combinaisons_list:
        nb_param = len(combinaison)
        objet_combinatoire = "tree"
        nom_de_la_tab = gen_name_datatable(combinaison)
        for lowup in ["up","low"]:
             for maxn in range(2,taille_max_tree+1):
                    bounded = combinaison[-1]
                    dataframe_tabledata = pd.read_csv("ext_tree/up"+nom_de_la_tab+".csv")

                    valeurs_de_la_colonne_v = np.array(dataframe_tabledata["v"])
                    array_ind_entrees_egales_maxn = np.flatnonzero(valeurs_de_la_colonne_v == maxn)
                    tree_maxn = dataframe_tabledata.loc[0:max(array_ind_entrees_egales_maxn.tolist())]

                    trans_allfeaturestabledata_prolog(nom_de_la_tab,tree_maxn,lowup,maxn,bounded,nb_param,objet_combinatoire)
    
