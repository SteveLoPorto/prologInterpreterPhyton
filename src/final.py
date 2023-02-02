from ast import Constant
from curses import termattrs
import functools
from tkinter import Y
from prolog_structures import Rule, RuleBody, Term, Function, Variable, Atom, Number
from typing import List, Tuple
from functools import reduce

import sys
import random

class Not_unifiable(Exception):
	pass


class Interpreter:
	def __init__(self):
		pass


	def occurs_check (self, v : Variable, t : Term) -> bool:
		if isinstance(t, Variable):
			return v == t
		elif isinstance(t, Function):
			for t in t.terms:
				if self.occurs_check(v, t):
					return True
			return False
		return False


	def variables_of_term (self, t : Term) -> set :
		vars = set()
		s = []
		if(isinstance(t, Function)):
			s = t.terms
		for curr in s:
			if (isinstance(curr, Variable)):
				vars = vars.union([curr])
			elif (isinstance(curr, Function)):
				vars = vars.union(Interpreter.variables_of_term(self, curr))

		return vars

	def variables_of_clause (self, c : Rule) -> set :
		vars = set()
		s = []
		t = c.head
		if(isinstance(t, Function)):
			s = t.terms
		for curr in s:
			if (isinstance(curr, Variable)):
				vars = vars.union([curr])
			elif (isinstance(curr, Function)):
				vars = vars.union(Interpreter.variables_of_term(self, curr))
		return vars

	def substitute_in_term(self, s : dict, t : Term):
		t_ = []
		if (s == {}) :
			return t
		elif isinstance(t, Function):
			for term in t.terms:
				if (isinstance(term, Variable)):
					keyLookUp = s.get(term)
					if keyLookUp:
						t_.append(s[term])
					else:
						t_.append(term)
				elif(isinstance(term, Function)):
					t_.append(Interpreter.substitute_in_term(self,s, term))
				else:
					t_.append(term)
			return Function(t.relation, t_)
		elif isinstance(t, Variable):
			keyLookUp = s.get(t)
			if keyLookUp:
				return s[t]
			else:
				return t
		else:
			return t


	
	def substitute_in_clause (self, s : dict, c : Rule) -> Rule:
		t = c.head
		t_ = []
		b = c.body
		#print(b)
		b_ = []
		if (s == {}) :
			return c
		for f in b.terms:
			b_.append(Interpreter.substitute_in_term(self, s, f))
		if (s == {}) :
			return c
		elif isinstance(t, Function):
			for term in t.terms:
				if (isinstance(term, Variable)):
					t_.append(s[term])
				else:
					t_.append(term)
			return Rule(Function(t.relation, t_), RuleBody(b_))

	def printTypes(self, t : Term):
		t_ = []

		if isinstance(t, Function):
			for term in t.terms:
				if (isinstance(term, Variable)):
						t_.append("Variable")
				elif(isinstance(term, Atom)):
						t_.append("Atom")
				elif(isinstance(term, Number)):
						t_.append("Number")
				elif(isinstance(term, Constant)):
						t_.append("Constant")
				elif(isinstance(term, Function)):
					z = ["Function"]
					z.append(Interpreter.printTypes(self, term))
					t_.append(z)
				else:
					t_.append(type(term))
			return t_

	def unify (self, t1: Term, t2: Term) -> dict:

		def contains(f: Function, t: Term):
			for term in f.terms:			
				if(term == t):
					return True
			return False

			
			#print("enter unify")
		def unifyHelper(t1: Term, t2: Term, s: dict):
			#print("enter unifyHelper")
			x = Interpreter.substitute_in_term(self,s, t1)
			y = Interpreter.substitute_in_term(self,s, t2)


			if(isinstance(x, Variable) and Interpreter.occurs_check(self, x, y)==False):
				for k in s.keys():
					if(s[k] == x):
						s[k] = y 
						#check if k and change
				s[x] = y
				#print("1")
				return s
			elif(isinstance(y, Variable) and Interpreter.occurs_check(self, y, x)==False):
				for k in s.keys():
					if(s[k] == y):
						s[k] = x 
				s[y] = x
				#print("2")
				return s
			elif(( isinstance(y, Variable) and isinstance(x, Variable) and (x == y)) or ( isinstance(y, Number) and isinstance(x, Number) and (x == y)) or ( isinstance(y, Atom ) and isinstance(x, Atom) and (x == y)) ):
				#print("3")
				return s
			elif( isinstance(t1, Function) and isinstance(t2, Function) and t1.relation == t2.relation):
				t1TermList = t1.terms
				t2TermList = t2.terms
				if(len(t1TermList)!= len(t2TermList)):
					raise Not_unifiable()

				tupleList = []
				
				for t in range(len(t1TermList)):
					#print(t1TermList[t])
					#print(t2TermList[t])
					tup: Tuple = (t1TermList[t], t2TermList[t])
					tupleList.append(tup)
				#for t in tupleList:
					#print(t)
				z = lambda acc, pair : unifyHelper(pair[0],pair[1],acc)
				return reduce(z,tupleList,s)
			else:
				#print("5")
				raise Not_unifiable()
		return unifyHelper(t1, t2, {})

	def nondet_query (self, program : List[Rule], pgoal : List[Term]) -> List[Term]:
		originalProgram = program
		originalGoal = pgoal
		def list2str(l):
			return ('(' + (',' + ' ').join(list(map(str, l))) + ')') 
		"Enter query"
		g = pgoal
		resolvent = pgoal
		while(len(resolvent) != 0):
			#print("this is g at start", g[0])
			'''Chooses random resolvent'''
			randomResolventIndex = random.randint(0, (len(resolvent)-1))
			currResolvent: Function = resolvent[randomResolventIndex]
			#print("This is currResolvent ", currResolvent)
			possibleRulesandFacts = []
			aPrime: Rule
			unifier: dict = None
		#	print("This is program size ", len(program))
			'''Checks if head of program line unify with goal if they do it adds to list'''
			for r in program:
				#print("in for loop")
				tempProgLine = Interpreter.freshen(self, r)
				#print("This is tempProg line before unify: ", tempProgLine)
				#print("This is currentResolvent before unify: ", currResolvent)
				try:
					#print("entered Sucessful unify")
					unifier = Interpreter.unify(self, currResolvent, tempProgLine.head)
					#print("this is a possible unifier below")
				#	for key in unifier:
				#		print(key, '->', unifier[key])
				except:
					pass
				if(unifier != None):
					possibleRulesandFacts.append(r)
					unifier = None
			'''Checks if theres no possibles and exits if theres not'''	
			if(len(possibleRulesandFacts) == 0):
				#print("break Hit")
				break
			'''Choose Random Possible Rule or Fact'''
			aPrime = possibleRulesandFacts[random.randint(0, (len(possibleRulesandFacts)-1))]
			'''Replace a with the content of aPrime in the resolvent, might have to see if you can just replace a or have to append each'''
			'''aPrime is a fact'''
			#print("this is g after for loop", g[0])
			#print("this is aPrime: ", aPrime)
			if(aPrime.body == RuleBody ([])):
				#print("a prime body is none")
				#print("this is g before aPrime.body == RuleBody work", g[0])
				tempList = []
				for s in resolvent:
					if(s != resolvent[randomResolventIndex]):
						tempList.append(s)
					else:
						pass
				resolvent = tempList
				unifier = Interpreter.unify(self, currResolvent, aPrime.head)
				#print("this is unifier below")
				#for key in unifier:
				#	print(key, '->', unifier[key])
			else:
				'''aPrime is a rule/clause'''
				tempList = []
				for s in resolvent:
					if(s != resolvent[randomResolventIndex]):
						tempList.append(s)
					else:
						pass
				resolvent = tempList
				for t in aPrime.body.terms:
					resolvent.append(t)		
			#	print("this is aPrime: ", aPrime.head)
			#	print("this is currResolvent: ", currResolvent)
				unifier = Interpreter.unify(self, currResolvent, aPrime.head)
			#	print("this is unifier below")
			# 	for key in unifier:
			#		print(key, '->', unifier[key])
			'''apply unifier to goals - terms'''
			for t in range(len(g)):
			#	print("this is goals value before unifier: ", g[t])
				g[t] = Interpreter.substitute_in_term(self, unifier, g[t])
			#	print("this is applied unifier value to goals: ", g[t])
			'''apply unifier to resolvent '''
			for t in range(len(resolvent)): 
			#	print("this is resolvent value before unifier: ", resolvent[t])
				resolvent[t] = Interpreter.substitute_in_term(self, unifier, resolvent[t])
			#	print("this is applied unifier value to resolvent : ", resolvent[t])

		if(Interpreter.variables_of_term(self, g[0]) != set()):
		#	print("variables are not empty []")
			return Interpreter.nondet_query(self, originalProgram, originalGoal)
		else:
		#	correct = [Function ("ancestor", (Atom("rickard"), Atom("robb")))]
		#	print("variables are empty []")
		#	print("This is length of g",len(g))
		#	print("This is type of g ", type(g), "This is type of g[0]", type(g[0]))
		#	print("this is list 2 string", list2str(g))
		#	print("this is supposed correct answer ", list2str(correct))
		#	print(Interpreter.printTypes(self, g[0]))
		#	print(Interpreter.printTypes(self, correct[0]))
		#	print(g)
			return g

	fresh_counter = 0
	def fresh(self) -> Variable:
		self.fresh_counter += 1
		return Variable("_G" + str(self.fresh_counter))
	def freshen(self, c: Rule) -> Rule:
		c_vars = self.variables_of_clause(c)
		theta = {}
		for c_var in c_vars:
			theta[c_var] = self.fresh()

		return self.substitute_in_clause(theta, c)

