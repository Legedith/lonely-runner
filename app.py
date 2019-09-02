from flask import Flask, render_template, request
import csv
import random
from multiprocessing import Pool
from os import path
import material
app = Flask(__name__)

# For database
import sqlite3
import pandas as pd
from pandas import DataFrame
n  = random.randint(4,6)
#subject = ''

@app.route("/")
def index():
    return render_template("index.html")


@app.route("/result", methods=["POST"])
def result():
    global subject
    subject = request.form.get("topic")
#    subject = removeSpaces(subject)
    domain = request.form.get("domain")
#    domain = removeSpaces(domain)
    if domain:
        subject+= ' ' + domain
    final = Textual(subject)
#    mit = course_mit(subject)
    return render_template("result.html", texts=final[0][:n],web=final[1][:n],movies=final[2][:n],image=final[3][:n],audio = final[4][:n],subject=subject)#, medium=medium)

#def removeSpaces(s):
#    s.replace(" ","+")
#    return s

@app.route("/display", methods=["GET"])
def display():
    info = request.args.get('id')
    t = request.args.get('type')
    subject = request.args.get('subject')
    conn = sqlite3.connect('data_'+subject+' '+t+'.db')  
    c = conn.cursor()
#    read = pd.read_csv(r'data_'+subject+' '+t+'.csv')
#    read.to_sql('data', conn, if_exists='append', index = False)
#    c.execute('SELECT * FROM data')
    c.execute("UPDATE data SET downloads=downloads+1 WHERE identifier='"+ info+"'")
    conn.commit()
    c.execute("SELECT * FROM data WHERE identifier='"+info+"'")
    a = c.fetchall()
#   names = [description[0] for description in c.description]
    return render_template("display.html", info = a[0])


def Textual(subject):
    docType  = ['texts','web','movies','image','audio']
    if not path.exists('data_'+subject+' texts.csv'):
        mater = material.mat(subject)
        try:
            with Pool(5) as p:
                p.map(mater.main,  [i for i in docType])
        except:
            print("Bug in Documents")
    final=[]
    for i in docType:
        conn = sqlite3.connect('data_'+subject+' '+i+'.db')  
        c = conn.cursor()
        c.execute('SELECT * FROM data')
        final.append(c.fetchall())
    return final
            
            
            
            