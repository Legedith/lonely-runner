# -*- coding: utf-8 -*-
"""
Created on Thu Apr 11 18:55:42 2019

@author: DSC
"""
from internetarchive import search_items
import json
import csv
import sqlite3
import pandas as pd
from pandas import DataFrame

class mat():
    def __init__(self, s):
        self.subject = s
        
    def main(self, t):
        outfile = open('data_'+self.subject+' '+t+'.json', 'w')
        f = ['description','downloads','identifier','mediatype','publicdate','title']
        results=[]
        with open('data_'+self.subject+' '+t+'.csv', 'w', newline='',encoding="utf-8") as csvfile:
            writer = csv.DictWriter(csvfile,fieldnames = f)
            writer.writeheader()
            count = 0
            for i in search_items(self.subject+' AND mediatype:'+t, fields=f):
                results.append(i)
                writer.writerow(i)
                count+=1
                print('.',end='')
                if count ==30:
                    break
#        print(len(results))
        conn = sqlite3.connect('data_'+self.subject+' '+t+'.db')  
        c = conn.cursor()
        read = pd.read_csv(r'data_'+self.subject+' '+t+'.csv')
        read.to_sql('data', conn, if_exists='append', index = False)
        json.dump(results,outfile) 
        
            
#a = mat('linear')
#a.main('texts')