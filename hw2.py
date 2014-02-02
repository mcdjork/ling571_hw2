#!/opt/python-2.6/bin/python2.6
__author__ = 'David McHugh'

import copy
import sys
import nltk

class Rule:
    splitter = '->'

    def __init__(self, left, right):
        self.left = left

        if (isinstance(right, Tag)):
            self.right = [right]
        else:
            self.right = right

        self._buildString()

    def _buildString(self):
        self._string = self.left.name + ' ' + self.splitter
        for tag in self.right:
            self._string += ' ' + tag.name

    def containsTerminal(self):
        #    if rule string contains apostrophe, signifies a terminal is present
        #    does not rule out hybrid
        return Tag(self.toString()).isTerminal()

    def isBinary(self):
        if len(self.right) == 2:
            return True
        return False

    def isUnitProduction(self):
        if not self.containsTerminal() and len(self.right) == 1:
            return True
        return False

    def toString(self):
        if self._string == '':
            return self._buildString()
        return self._string


class Tag:
    def __init__(self, name):
        self.name = name.strip()
        self.pointers = []
        self.isParentOfTerminal = False

    def __eq__(self, other):
        return self.name  == other.name

    def isTerminal(self):
        if '\'' in self.name:
            return True
        return False

class Pointer:
    def __init__(self,i,j,tagIdx):
        self.i = i
        self.j = j
        self.tagIdx = tagIdx

class Grammar:
    start = 'TOP'

    def __init__(self):
        self.rules = []
        self._newTags = []

    def _generateNewTag(self):
        newTagCnt = len(self._newTags)
        tag = Tag('X' + str(newTagCnt + 1))

        while self._newTagExists(tag):
            newTagCnt += 1
            tag = Tag('X' + str(newTagCnt))

        self._newTags.append(tag)
        return tag

    def _newTagExists(self, newTag):
        if newTag in self._newTags:
            return True
        return False

    def _getNewTag(self, oldTag):
        newTag = Tag(oldTag.name.replace('\'', '').upper())

        if not newTag.name.isalnum():
            return self._generateNewTag()

        self._newTags.append(newTag)
        return newTag

    def parseRule(self, line):
        split = line.split(Rule.splitter)

        leftTag = Tag(split[0])
        rightStrings = split[1].split()

        rightTags = []
        for string in rightStrings:
            rightTags.append(Tag(string))

        return Rule(leftTag, rightTags)

    def load(self, inputFile):
        grammarFile = open(inputFile)
        grammarLines = grammarFile.readlines()
        grammarFile.close()

        del self.rules [:]
        del self._newTags [:]

        for line in grammarLines:
            if not Rule.splitter in line:
                continue

            self.rules.append(self.parseRule(line.replace('\n', '').replace('  ',' ')))

    def writeToFile(self, outputFile):
        nonterminals = []
        terminals = []

        #    split terminals off for sorting purposes only
        for rule in self.rules:
            if rule.containsTerminal():
                terminals.append(rule)
            else:
                nonterminals.append(rule)

        nonterminals.sort(key=lambda tup: tup.toString())
        terminals.sort(key=lambda tup: tup.toString())

        grammarFile = open(outputFile, 'w')
        grammarFile.write('#\t' + __author__ + '\n\n')

        for rule in nonterminals:
            grammarFile.write (rule.toString() + '\n')

        for rule in terminals:
            grammarFile.write (rule.toString() + '\n')

        grammarFile.close()

class CnfGrammar(Grammar):

    def __init__(self, grammar):
        Grammar.__init__(self)
        self._todo = []
        self._done = []
        self._convertFromCfg(grammar)

    #    precondition: all cnf rules already removed
    def _convertHybrids(self, rules):
        for i, rule in enumerate(self._todo):
            #    if contains terminal, must be hybrid
            if rule.containsTerminal():
                #    will be fixed, remove from to-do list and fix
                self._todo.pop(i)
                newRules = self._convertHybrid(rule)
                self._sortRules(newRules)

    def _convertHybrid(self, rule):
        newRules = []
        newRights = []

        #    iterate over tags in right side of rule
        #    if tag is terminal, create new left side rule
        for rightTag in rule.right:
            if rightTag.isTerminal():
                newTag = self._getNewTag(rightTag)
                newRights.append(newTag)
                newRule = Rule(newTag, rightTag)
                newRules.append(newRule)
            else:
                newRights.append(rightTag)

        #    return newly created rules
        newRules.append(Rule(rule.left, newRights))
        return newRules

    #    precondition all cnf and hybrid rules are removed
    def _convertUnitProductions(self, rules):
        for i, rule in enumerate(self._todo):
            if rule.isUnitProduction():
                self._todo.pop(i)
                newRules = self._convertUnitProduction(rule)
                self._sortRules(newRules)
                self._convertUnitProductions(self._todo)


    def _convertUnitProduction(self, rule):
        children = []

        #    right side of unit production rule
        fromTag = rule.right[0]
        #    left side of unit production rule
        toTag = rule.left

        #    find all rules (fixed and non) where left side of rule
        #    matches right side of unit production rule
        for cnfRule in self._done:
            if cnfRule.left == fromTag:
                children.append(cnfRule)

        for cfRule in self._todo:
            if cfRule.left == fromTag:
                children.append(cfRule)

        newRules = []

        #    create new rules where left of unit prod rule
        #    is left of rules where right side of unit prod
        #    rule is left
        #    A -> B and B-> C D to A -> C D
        for child in children:
            newRule = Rule(toTag, child.right)
            newRules.append(newRule)

        return newRules

    #    precondition: all cnf, hybrid, unit removed
    def _convertNonBinaries(self, rules):
        for i, rule in enumerate(self._todo):
            if not rule.isBinary():
                self._todo.pop(i)
                newRules = self._convertNonBinary(rule)
                self._sortRules(newRules)
                self._convertNonBinaries(self._todo)


    def _convertNonBinary(self, rule):
        newRules = []
        #    create new tag to represent first two tags in right side
        #    of non binary rule
        newLeft = self._generateNewTag()
        #    take first two tags in right side of nonbinary rule for new rule
        newRight = [rule.right[0], rule.right[1]]
        #    create new rule
        newRule = Rule(newLeft, newRight)
        newRules.append(newRule)

        #    create new rule from old nonbinary rule with new tag for first two tags on right
        #    remove old rule from todo list and add updated rule to new list
        oldLeft = rule.left
        oldRight = rule.right
        rule.right.pop(1)
        rule.right[0] = newLeft
        newRules.append(Rule(oldLeft, oldRight))

        return newRules


    def _isCnf(self, rule):
        if not rule.containsTerminal():
            if rule.isBinary():
                return True
            return False
        if len(rule.right) == 1:
            return True
        return False

    def _sortRules(self, rules):
        for rule in rules:
            if self._isCnf(rule):
                self._done.append(copy.deepcopy(rule))
            else:
                self._todo.append(copy.deepcopy(rule))

    #    convert a context free grammar to chomsky normal form
    def _convertFromCfg(self, grammar):
        self.rules = grammar.rules

        self._sortRules(self.rules)

        self._convertHybrids(self._todo)

        self._convertUnitProductions(self._todo)

        self._convertNonBinaries(self._todo)

        self.rules = self._done

class Parser:

    def __init__(self):
        self._sentences = []
        self._grammar = Grammar

    def load(self, fileName):
        sentenceFile = open(fileName)
        sentenceLines = sentenceFile.readlines()
        sentenceFile.close()

        del self._sentences [:]

        for line in sentenceLines:
            if '' == line:
                continue

            self._sentences.append(line.replace('\n', ''))

    def writeParsesToFile(self, fileName):
        #    total number of parses
        totalCnt = 0
        #    total number of sentences
        sentenceCnt = 0

        #    clear parse output file
        output = open(fileName, 'w')
        output.write('#\t' + __author__ + '\n\n')
        output.close()

        #    generate and print trees for each sentence
        for sentence in self._sentences:
            parses =  self._parse(sentence)
            parseCnt = len(parses)

            output = open(fileName, 'a')

            output.write(sentence + '\n')
            for parse in parses:
                output.write(parse + '\n')

            output.write('\n' + str(parseCnt) + '\n\n')

            totalCnt += parseCnt
            sentenceCnt += 1

        #    calculate and print average number of parses per sentence
        output = open(fileName, 'a')
        output.write(str(float(totalCnt) / float(sentenceCnt)) + '\n')
        output.close()

class CkyParser(Parser):
    def __init__(self, cnfGrammar):
        Parser.__init__(self)
        assert isinstance(cnfGrammar, CnfGrammar)
        self._grammar = cnfGrammar


    def _parse(self, sentence):
        table = self._buildTable(sentence)
        strings = self._buildStrings(table, sentence)
        return strings

    def _buildTable(self, sentence):
            tokens = nltk.word_tokenize(sentence)
            length = len(tokens)

            table = [[Cell() for i in range(length+1)] for i in range(length+1)]

            j = 1
            while j <= length:
                #    fill cell with left side of rules where right side is correct terminal
                table[j-1][j].addTags([rule.left for rule in self._grammar.rules if rule.right[0].name == '\'' + tokens[j-1] + '\''])

                i = j-2
                while i >= 0:
                    k = i+1
                    while k <= j-1:
                        #    iterate all rules
                        for rule in self._grammar.rules:
                            #    iterate tags in "b" cell
                            for bIdx,bTag in enumerate(table[i][k].tags):
                                #    if position "b" in rule matches tag in "b" cell
                                if rule.right[0].name == bTag.name:
                                    #    iterate tags in "c" cell
                                    for cIdx,cTag in enumerate(table[k][j].tags):
                                        #    if position "c" in rule matches tag in "c" cell
                                        if rule.right[1].name == cTag.name:
                                            bPointer = Pointer(i,k,bIdx)
                                            cPointer = Pointer(k,j,cIdx)
                                            tag = Tag(rule.left.name)
                                            tag.pointers.append(bPointer)
                                            tag.pointers.append(cPointer)
                                            table[i][j].addTag(tag)
                        k += 1
                    i -= 1
                j += 1

            return table

    def _buildStrings(self, table, sentence):
        strings = []

        rootCell = table[0][len(table) - 1]

        tokens = nltk.word_tokenize(sentence)

        for tag in rootCell.tags:
            tokenCopy = copy.deepcopy(tokens)
            #    if any tags are start tag in root cell, begin to descent into tree
            if tag.name == self._grammar.start:
                string = ''
                depth = 0
                string = self._addNodeToString(table, tag, string, depth, tokenCopy)
                strings.append(string)

        return strings

    def _addNodeToString(self, table, tag, string, depth, tokens):
        string += '\n'
        for x in range(depth):
            string += '  '

        string += '(' + tag.name
        depth += 1

        for pointer in tag.pointers:
            childTag = table[pointer.i][pointer.j].tags[pointer.tagIdx]
            string = self._addNodeToString(table, childTag, string, depth, tokens)

        if len(tag.pointers) == 0:
            if len(tokens) > 0:
                string += ' ' + tokens[0]
                tokens.pop(0)

        string += ')'
        return string

class Cell:
    def __init__(self):
        self.tags = []

    def addTag(self, tag):
        self.tags.append(tag)

    def addTags(self, tags):
        for tag in tags:
            self.addTag(tag)

cfFile = sys.argv[1]
cnfFile = sys.argv[2]
sntcFile = sys.argv[3]
parseFile = sys.argv[4]

#   load context free grammar
g = Grammar()
g.load(cfFile)
#   convert grammar to chomsky normal form
cnfG = CnfGrammar(g)
#    output converted grammar to file
cnfG.writeToFile(cnfFile)

#   load sentences to parse
p = CkyParser(cnfG)
p.load(sntcFile)
#   print parses to file
p.writeParsesToFile(parseFile)