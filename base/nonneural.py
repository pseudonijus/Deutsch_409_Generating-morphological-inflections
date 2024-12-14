#!/usr/bin/env python3
"""
Non-neural baseline system for the SIGMORPHON 2020 Shared Task 0.
Author: Mans Hulden
Modified by: Tiago Pimentel
Modified by: Jordan Kodner
Modified by: Omer Goldman
Last Update: 22/03/2021
"""

import sys, os, getopt, re
#sys, os: system level operations (file paths, arguments)
#getopt: parsing command-line options
#re: regular expressions
from functools import wraps
#preserves wrapped functions
from glob import glob
#globbing (method for finding files with similar naming schema)


def hamming(s,t):
    """Calculate the Hamming distance between two given strings, s, and t:
    (ie: how many substitutions needed to turn one string into another)."""
    return sum(1 for x,y in zip(s,t) if x != y)
    #iterates through each character in the zipped pair; for x,y in zip(s,t)
    #if x and y are not equal; if x!=y, it adds 1 to the total pair; sum()

def halign(s,t):
    """Align two strings by Hamming distance by padding them with
    underscores so that their Hamming distance can be minimized."""
    slen = len(s) #stores the length of string s
    tlen = len(t) #stores the length of string t
    minscore = len(s) + len(t) + 1
    #minscore keeps track of the current minimum Hamming distance
    #initialized as the sum of the string lengths plus one
    for upad in range(0, len(t)+1): #padding s to align with t
        upper = '_' * upad + s + (len(t) - upad) * '_'
        #pads s with 'upad' underscores on the left  and 'len(t)-upad) underscores on the right
        lower = len(s) * '_' + t
        #pads t with len(s) underscores to match the length of upper
        score = hamming(upper, lower)
        #calculates the Hamming distance with current padding
        if score < minscore: #if Hamming distance is less than current minscore
            bu = upper #stores padded version of s for current minimum
            bl = lower #stores padded version of t for current minimum
            minscore = score #updates with current minimum Hamming distance

    for lpad in range(0, len(s)+1): #same as above but for string t
        upper = len(t) * '_' + s
        lower = (len(s) - lpad) * '_' + t + '_' * lpad
        score = hamming(upper, lower)
        if score < minscore:
            bu = upper
            bl = lower
            minscore = score
    zipped = list(zip(bu,bl)) #zips padded versions of s and t for minimum Hamming distance
    newin  = ''.join(i for i,o in zipped if i != '_' or o != '_') #stores the version of s without the underscores
    newout = ''.join(o for i,o in zipped if i != '_' or o != '_') #stores the version of t without the underscores
    return newin, newout


def levenshtein(s, t, inscost = 1.0, delcost = 1.0, substcost = 1.0):
    """Recursive implementation of Levenshtein, with alignments returned by
    calculating the minimum number of edits (insert, delete, substitute) to transform s to t."""
    #s and t: input strings to compare
    #inscost, delcost, substcost: costs of insertion, deletion, and substitution, respectively (default: 1.0)
    @memolrec
    #memoizer for lrec function (as seen below)
    #spast, tpast: parts of s and t that are passed
    #srem, trem: parts of s and t that are remaining
    def lrec(spast, tpast, srem, trem, cost):
        if len(srem) == 0:
            #base case of recursive algorithm: if there are no more remaining characters in s
            return spast + len(trem) * '_', tpast + trem, '', '', cost + len(trem)
        if len(trem) == 0:
            return spast + srem, tpast + len(srem) * '_', '', '', cost + len(srem)
            #base case of recursive algorithm: if there are no more remaining characters in t

        addcost = 0
        #total cost of insertions/deletions/substitutions, initialized at 0
        if srem[0] != trem[0]:
            addcost = substcost
            #checks if first characters of s and t are not equal, if so, add cost of substition to total cost

        return min((lrec(spast + srem[0], tpast + trem[0], srem[1:], trem[1:], cost + addcost),
                    #substition
                    #adds first character of srem to spast, removes from srem
                    #adds first character of trem to tpast, removes from trem
                   lrec(spast + '_', tpast + trem[0], srem, trem[1:], cost + inscost),
                    #insertion
                    #adds underscore to spast to represent an insertion
                    #add first character of trem to tpast, removes from trem
                   lrec(spast + srem[0], tpast + '_', srem[1:], trem, cost + delcost)),
                    #deletion
                    #adds first character of srem to spast, removes from srem
                    #adds underscore to tpast to represent an deletion
                   key = lambda x: x[4])
                    #finds the minimum cost using minimum number of substitutions, insertions, deletions

    answer = lrec('', '', s, t, 0)
    #spast and tpast are initialized as empty strings as no characters have been processed yet
    #srem and trem are initialized as the full strings as they have yet to be processed
    #cost initialized to 0
    return answer[0],answer[1],answer[4]


def memolrec(func):
    """Memoizer for Levenshtein (cache to check if Levenshtein distance between s and t has already been calculated
    before to save time, as Levenshtein is a recursive algorithm that repeatedly solves subproblems."""
    cache = {}
    @wraps(func)
    def wrap(sp, tp, sr, tr, cost):
        #sp and tp are shorthands for spast and tpast; sr and tr are shorthands for srem and trem
        if (sr,tr) not in cache:
            res = func(sp, tp, sr, tr, cost)
            cache[(sr,tr)] = (res[0][len(sp):], res[1][len(tp):], res[4] - cost)
        return sp + cache[(sr,tr)][0], tp + cache[(sr,tr)][1], '', '', cost + cache[(sr,tr)][2]
    return wrap


def alignprs(lemma, form):
    """Break lemma/form into three parts:
    IN:  1 | 2 | 3
    OUT: 4 | 5 | 6
    1/4 are assumed to be prefixes, 2/5 the stem, and 3/6 a suffix.
    1/4 and 3/6 may be empty.
    """

    al = levenshtein(lemma, form, substcost = 1.1) #force preference of 0:x or x:0 by 1.1 cost
    #aligns lemma and form using Levenshtein function
    alemma, aform = al[0], al[1]
    #aligned lemma and aligned form
    lspace = max(len(alemma) - len(alemma.lstrip('_')), len(aform) - len(aform.lstrip('_')))
    #leading spaces: calculates the difference in length before and after padding with underscores for lemma and form
    #max determines larger number of leading spaces
    tspace = max(len(alemma[::-1]) - len(alemma[::-1].lstrip('_')), len(aform[::-1]) - len(aform[::-1].lstrip('_')))
    #trailing spaces
    #leading spaces: calculates the difference in length before and after padding with underscores for lemma and form
    #max determines larger number of trailing spaces
    return alemma[0:lspace], alemma[lspace:len(alemma)-tspace], alemma[len(alemma)-tspace:], aform[0:lspace], aform[lspace:len(alemma)-tspace], aform[len(alemma)-tspace:]
    #returns prefix of alemma, stem of alemma, suffix of alemma, prefix of aform, stem of aform, suffix of aform


def prefix_suffix_rules_get(lemma, form):
    """Extract a number of suffix-change and prefix-change rules
    based on a given example lemma+inflected form."""
    """Analyze how the prefix and suffix change given a lemma and inflected form in order
    to predict forms for other words.""" 
    lp,lr,ls,fp,fr,fs = alignprs(lemma, form) #get six parts, three for in three for out
    #lp, lr, ls: lemma prefix, lemma root, lemma suffix
    #fp, fr, fs: form prefix, form root, form suffix

    # Suffix rules
    ins  = lr + ls + ">"
    #stem and suffix of lemma, '>' indicates end
    outs = fr + fs + ">"
    #stem and suffix of form, '>' indicates end
    srules = set()
    #initializes empty set for suffix rules
    for i in range(min(len(ins), len(outs))):
        #iterates through either the stem+suffix of lemma or stem+suffix of form, whichever is shorter
        srules.add((ins[i:], outs[i:]))
        #adds ins and outs sliced from index i to end into set of suffix rules
    srules = {(x[0].replace('_',''), x[1].replace('_','')) for x in srules}
    #removes underscores from suffix rules by replacing with empty strings

    # Prefix rules
    prules = set()
    if len(lp) >= 0 or len(fp) >= 0:
        #if either the lemma or form has a prefix
        inp = "<" + lp
        #lemma prefix, '<' indicates' beginning
        outp = "<" + fp
        #form prefix, '<' indicates' beginning
        for i in range(0,len(fr)):
            #iterates through length of form root
            prules.add((inp + fr[:i],outp + fr[:i]))
            #inp and outp, plus the form root sliced from the beginning to index i
            prules = {(x[0].replace('_',''), x[1].replace('_','')) for x in prules}
            #removes underscores from prefix rules by replacing with empty strings

    return prules, srules
    #returns set of prefix and suffix rules, respectively


def apply_best_rule(lemma, msd, allprules, allsrules):
    """Applies the longest-matching suffix-changing rule given an input
    form and the MSD. Length ties in suffix rules are broken by frequency.
    For prefix-changing rules, only the most frequent rule is chosen."""
    #lemma: base
    #msd: morphosyntactic description (eg. past, plural, etc.)
    #allprules: dictionary of prefix rules grouped by msd
    #allsrules: dictionary of suffix rules grouped by msd

    bestrulelen = 0
    base = "<" + lemma + ">"
    #wrap lemma with '<' and '>' to match rule format
    if msd not in allprules and msd not in allsrules:
        return lemma #haven't seen this inflection, so bail out

    if msd in allsrules: #applying the best suffix rule
        applicablerules = [(x[0],x[1],y) for x,y in allsrules[msd].items() if x[0] in base]
        if applicablerules:
            bestrule = max(applicablerules, key = lambda x: (len(x[0]), x[2], len(x[1])))
            base = base.replace(bestrule[0], bestrule[1])

    if msd in allprules: #applying the best prefix rule
        applicablerules = [(x[0],x[1],y) for x,y in allprules[msd].items() if x[0] in base]
        if applicablerules:
            bestrule = max(applicablerules, key = lambda x: (x[2]))
            base = base.replace(bestrule[0], bestrule[1])

    base = base.replace('<', '')
    base = base.replace('>', '')
    return base


def numleadingsyms(s, symbol):
    return len(s) - len(s.lstrip(symbol))
    #returns count of leading occurrences of symbol


def numtrailingsyms(s, symbol):
    return len(s) - len(s.rstrip(symbol))
    #returns count of trailing occurrences of symbol

###############################################################################


def main(argv):
    options, remainder = getopt.gnu_getopt(argv[1:], 'ohp:', ['output','help','path='])
    TEST, OUTPUT, HELP, path = False,False, False, '../data/'
    for opt, arg in options:
        if opt in ('-o', '--output'):
            OUTPUT = True
        if opt in ('-t', '--test'):
            TEST = True
        if opt in ('-h', '--help'):
            HELP = True
        if opt in ('-p', '--path'):
            path = arg

    if HELP:
            print("\n*** Baseline for the SIGMORPHON 2020 shared task ***\n")
            print("By default, the program runs all languages only evaluating accuracy.")
            print("To create output files, use -o")
            print("The training and dev-data are assumed to live in ./part1/development_languages/")
            print("Options:")
            print(" -o         create output files with guesses (and don't just evaluate)")
            print(" -t         evaluate on test instead of dev")
            print(" -p [path]  data files path. Default is ../data/")
            quit()

    totalavg, numlang = 0.0, 0
    for lang in [os.path.splitext(d)[0] for d in os.listdir(path) if '.trn' in d]: #identifies all .trn files in directory
        allprules, allsrules = {}, {} #initializes allprules and allsrules to empty dictionaries
        if not os.path.isfile(path + lang +  ".trn"):
            continue
        lines = [line.strip() for line in open(path + lang + ".trn", "r", encoding='utf8') if line != '\n']
        #reads and cleans lines from training file

        # First, test if language is predominantly suffixing or prefixing
        # If prefixing, work with reversed strings
        prefbias, suffbias = 0,0
        for l in lines:
            lemma, _, form = l.split(u'\t')
            aligned = halign(lemma, form)
            #aligns lemma and form
            if ' ' not in aligned[0] and ' ' not in aligned[1] and '-' not in aligned[0] and '-' not in aligned[1]:
                prefbias += numleadingsyms(aligned[0],'_') + numleadingsyms(aligned[1],'_')
                suffbias += numtrailingsyms(aligned[0],'_') + numtrailingsyms(aligned[1],'_')
                #counts leading/trailing underscores to detect whether the language has prefix or suffix bias
        for l in lines: # Read in lines and extract transformation rules from pairs
            lemma, msd, form = l.split(u'\t')
            if prefbias > suffbias:
                lemma = lemma[::-1]
                form = form[::-1]
                #if language has prefix bias, reverses lemma and form to treat prefixes as suffixes
            prules, srules = prefix_suffix_rules_get(lemma, form)
            #generates transformation rules

            if msd not in allprules and len(prules) > 0:
                allprules[msd] = {} #no prefix rule needs to be applied
            if msd not in allsrules and len(srules) > 0:
                allsrules[msd] = {} #no suffix rule needs to be applied

            for r in prules:
                if (r[0],r[1]) in allprules[msd]:
                    allprules[msd][(r[0],r[1])] = allprules[msd][(r[0],r[1])] + 1
                else:
                    allprules[msd][(r[0],r[1])] = 1

            for r in srules:
                if (r[0],r[1]) in allsrules[msd]:
                    allsrules[msd][(r[0],r[1])] = allsrules[msd][(r[0],r[1])] + 1
                else:
                    allsrules[msd][(r[0],r[1])] = 1

        # Run eval on dev
        devlines = [line.strip() for line in open(path + lang + ".dev", "r", encoding='utf8') if line != '\n']
        if TEST:
            devlines = [line.strip() for line in open(path + lang + ".tst", "r", encoding='utf8') if line != '\n']
        numcorrect = 0
        numguesses = 0
        if OUTPUT:
            outfile = open(path + lang + ".out", "w", encoding='utf8')
        for l in devlines:
            lemma, msd, correct = l.split(u'\t')
            if prefbias > suffbias:
                lemma = lemma[::-1]
            outform = apply_best_rule(lemma, msd, allprules, allsrules)
            if prefbias > suffbias:
                outform = outform[::-1]
                lemma = lemma[::-1]
            if outform == correct:
                numcorrect += 1
            numguesses += 1
            if OUTPUT:
                outfile.write(lemma + "\t" + msd + "\t" + outform + "\n")

        if OUTPUT:
            outfile.close()

        numlang += 1
        totalavg += numcorrect/float(numguesses)

        print(lang + ": " + str(str(numcorrect/float(numguesses)))[0:7])

    print("Average accuracy", totalavg/float(numlang))


if __name__ == "__main__":
    main(sys.argv)
