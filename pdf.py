# -*- coding: utf-8 -*-
"""
Created on Wed Jun 19 16:10:55 2019

@author: DSC
"""
from selenium import webdriver
from bs4 import BeautifulSoup

def main():
    subject = input("Enter Subject: ")
    subject = removeSpaces(subject)
    driver = webdriver.Chrome()
    driver.get('https://archive.org/search.php?query='+subject+'&and[]=mediatype%3A%22texts%22')


def removeSpaces(s):
    s.replace(" ","+")
    return s    


if __name__ == "__main__":
    main()