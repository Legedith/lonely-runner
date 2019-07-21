# -*- coding: utf-8 -*-
"""
Created on Thu Apr 11 18:55:42 2019

@author: DSC
"""
from internetarchive import search_items
import json
import csv

class mat():
    def __init__(self, s,t):
        self.subject = s
        self.type = t
        
    def main(self):
        outfile = open('data_'+self.subject+' '+self.type+'.json', 'w')
        f = ['description','downloads','identifier','mediatype','publicdate','title']
        results=[]
        with open('data_'+self.subject+' '+self.type+'.csv', 'w', newline='',encoding="utf-8") as csvfile:
            writer = csv.DictWriter(csvfile,fieldnames = f)
            writer.writeheader()
            count = 0
            for i in search_items(self.subject+' AND mediatype:'+self.type,fields=f):
                results.append(i)
                writer.writerow(i)
                count+=1
                print('.',end='')
                if count ==30:
                    break
        print(len(results))
        json.dump(results,outfile) 
        
            
a = mat('linear','texts')
a.main()