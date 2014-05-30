########################################################################
# Basics of Data Compression implementation on Python
# Using a Huffman Algorithm
# Author: Jules Oppenheim
#
# Reference: http://www.openbookproject.net/py4fun/huffman/huffman.html
########################################################################

import string

class Huffman(object):
	def __init__(self):
		self.codes = {}
		pass

	def frequency(self, str):
		freqs = {}
		for ch in str:
			freqs[ch] = freqs.get(ch,0) + 1
		return freqs

	def sortFreq(self, freqs):
		letters = freqs.keys()
		tuples = []
		for let in letters:
			tuples.append((freqs[let],let))
		tuples.sort()
		return tuples

	def buildTree(self, tuples):
		while len(tuples) > 1:
			leastTwo = tuple(tuples[0:2])
			theRest = tuples[2:]
			combFreq = leastTwo[0][0] + leastTwo[1][0]
			tuples = theRest + [(combFreq,leastTwo)]
			tuples.sort()
		return tuples[0]

	def trimTree(self, tree):
		p = tree[1]
		if type(p) == type(""): return p
		else: return (self.trimTree(p[0]), self.trimTree(p[1]))

	def assignCodes(self, node, pat=''):
		if type(node) == type(""): self.codes[node] = pat
		else:
			self.assignCodes(node[0], pat+"0")
			self.assignCodes(node[1], pat+"1")

	def encode(self, str):
		output = ""
		for ch in str: output += self.codes[ch]
		return output

	def decode(self, tree, str):
		output = ""
		p = tree
		for bit in str:
			if bit == '0':
				if type(p[0])==int:
					p = p
				else:
					p = p[0]
			else: p = p[1]
			if type(p) == type(""):
				output += p
				p = tree
		return output


def main():
	Huff = Huffman()

	message = "This will be encrypted or something"
	
	freq = Huff.frequency(message)
	sort = Huff.sortFreq(freq)
	tree = Huff.buildTree(sort)
	trim = Huff.trimTree(tree)
	Huff.assignCodes(trim)
	
	small = Huff.encode(message)
	original = Huff.decode(trim, small)

	print "Original text length", len(message)
	print "Requires %d bits. (%d bytes)" % (len(small),(len(small)+7)/8)
	print "Restored matches original", message==original
	print "Code for space is ", Huff.codes[' ']
	print "Code for letter e ", Huff.codes['e']

	print message
	print small
	print original
	

main()









