from flask import Flask, render_template, request
import csv
from multiprocessing import Pool
from os import path
#import edx
import material
#import youtube
app = Flask(__name__)


@app.route("/")
def index():
    return render_template("index.html")


@app.route("/result", methods=["POST"])
def result():
    subject = request.form.get("topic")
    subject = removeSpaces(subject)
    domain = request.form.get("domain")
    domain = removeSpaces(domain)
    if domain:
        subject+= '+' + domain
    final = Textual(subject)
    mit = course_mit(subject)
#    medium = course_medium(subject)
    return render_template("result.html", pdf=final[0],ppt=final[1],docx=final[2],books=final[3],mit = mit)#, medium=medium)

def removeSpaces(s):
    s.replace(" ","+")
    return s

def Textual(subject):
    docType  = ['pdf','ppt','docx','books']
    if not path.exists('material_'+subject+' books.csv'):
        mater = material.mat(subject)
        #edx.main(subject)
        try:
            with Pool(5) as p:
                p.map(mater.main,  [i for i in docType])
        except:
            print("Bug in Documents")
    final=[]
    for i in docType:
#        material.main(subject, i)
        with open('material_'+subject+" "+i+'.csv', "r", encoding='utf-8') as file:
            reader = csv.DictReader(file)
            final.append(list(reader))   
    return final

def course_mit(subject):
    if not path.exists('mit '+subject+' .csv'):
        try: 
            mit.main(subject)
        except:
            print("Bug in mit")
    with open('mit '+subject+' .csv', "r", encoding='utf-8') as file:
            reader = csv.DictReader(file)
            final = list(reader)
    return final

def course_medium(subject):
    if not path.exists('medium '+subject+' .csv'):
        try: 
            medium.main(subject)
        except:
            print("Bug in mit")
    with open('medium '+subject+' .csv', "r", encoding='utf-8') as file:
            reader = csv.DictReader(file)
            final = list(reader)
    return final
            
            
            
            