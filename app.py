from flask import Flask, render_template, request
import csv
from multiprocessing import Pool
from os import path
import material
app = Flask(__name__)


@app.route("/")
def index():
    return render_template("index.html")


@app.route("/result", methods=["POST"])
def result():
    subject = request.form.get("topic")
#    subject = removeSpaces(subject)
    domain = request.form.get("domain")
#    domain = removeSpaces(domain)
    if domain:
        subject+= ' ' + domain
    final = Textual(subject)
#    mit = course_mit(subject)
    return render_template("result.html", texts=final[0],web=final[1],movies=final[2],image=final[3],audio = final[4])#, medium=medium)

#def removeSpaces(s):
#    s.replace(" ","+")
#    return s

@app.route("/display", methods=["POST"])
def display():
    return render_template("display.html")


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
        with open('data_'+subject+' '+i+'.csv', "r", encoding='utf-8') as file:
            reader = csv.DictReader(file)
            final.append(list(reader))   
    return final
            
            
            
            