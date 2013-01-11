#!/usr/bin/python2

from goatools import obo_parser;
from math     import sqrt;

###############################################################################

class intelligo:

  #############################################################################

  weights_list1 = { 'TAS':1.0, 'NAS':1.0, 'EXP':1.0, 'IDA':1.0, 'IPI':1.0, 'IMP':1.0, 'IGI':1.0, 'IEP':1.0, 'ISS':1.0, 'RCA':1.0, 'ISA':1.0, 'ISO':1.0, 'ISM':1.0, 'IGC':1.0, 'IC':1.0, 'ND':1.0, 'IEA':1.0,   'IBA':0.4, 'IRD': 0.4, 'IKR':0.4 }
  weights_list2 = { 'TAS':1.0, 'NAS':0.5, 'EXP':0.8, 'IDA':0.8, 'IPI':0.8, 'IMP':0.8, 'IGI':0.8, 'IEP':0.6, 'ISS':0.6, 'RCA':0.6, 'ISA':0.6, 'ISO':0.6, 'ISM':0.6, 'IGC':0.6, 'IC':0.5, 'ND':0.0, 'IEA':0.4,   'IBA':0.4, 'IRD': 0.4, 'IKR':0.4 }
  weights_list3 = { 'TAS':1.0, 'NAS':0.5, 'EXP':0.8, 'IDA':0.8, 'IPI':0.8, 'IMP':0.8, 'IGI':0.8, 'IEP':0.6, 'ISS':0.6, 'RCA':0.6, 'ISA':0.6, 'ISO':0.6, 'ISM':0.6, 'IGC':0.6, 'IC':0.5, 'ND':0.0, 'IEA':0.0,   'IBA':0.4, 'IRD': 0.4, 'IKR':0.4 }
  weights_list4 = { 'TAS':0.0, 'NAS':0.0, 'EXP':0.0, 'IDA':0.0, 'IPI':0.0, 'IMP':0.0, 'IGI':0.0, 'IEP':0.0, 'ISS':0.0, 'RCA':0.0, 'ISA':0.0, 'ISO':0.0, 'ISM':0.0, 'IGC':0.0, 'IC':0.0, 'ND':0.0, 'IEA':1.0,   'IBA':0.4, 'IRD': 0.4, 'IKR':0.4 }

  depth_cache  = {};
  anc_cache    = {};
  lcaset_cache = {};
  mdist_cache  = {};
  dot_cache    = {};
  obo = [];
  weights = {};

  #############################################################################

  def __init__(self, fin, weights={ 'TAS':1.0, 'NAS':1.0, 'EXP':1.0, 'IDA':1.0, 'IPI':1.0, 'IMP':1.0, 'IGI':1.0, 'IEP':1.0, 'ISS':1.0, 'RCA':1.0, 'ISA':1.0, 'ISO':1.0, 'ISM':1.0, 'IGC':1.0, 'IC':1.0, 'ND':1.0, 'IEA':1.0, 'IBA':0.8, 'IRD': 0.4, 'IKR':0.4 }):
    self.obo = obo_parser.GODag(fin);
    self.weights = weights;
  #edef

  #############################################################################

  def depth(self, term):
    """
      Find the maximal depth of a given GO term
    """

    if term in self.depth_cache:
      return self.depth_cache[term];
    #fi

    parents = set([ t.id for t in self.obo[term].parents ]);

    if len(parents) == 0:
      rdep = 0;
    else:

      maxd = -1;
      maxdp = '';

      for parent in parents:
        d = self.depth(parent);
        if d > maxd:
          maxd = d;
          maxdp = parent;
        #fi
      #efor
      rdep = maxd + 1;

    #fi

    self.depth_cache[term] = rdep;
    return rdep;
  #edef

  #############################################################################

  def ancestors(self, term):

    """
      Find the ancestors of a given GO term
    """

    if term in self.anc_cache:
      return self.anc_cache[term];
    #fi

    parents = set([ t.id for t in self.obo[term].parents ]);
    anc = parents | set([term]);

    for parent in parents:
      anc = anc | self.ancestors(parent);
    #efor

    self.anc_cache[term] = anc;
    return anc;
  #edef

  #############################################################################

  def commonanc(self, term1, term2):

    """
      Return the common ancestors of two terms
    """

    return self.ancestors(term1) & self.ancestors(term2);

  #edef

  #############################################################################

  def lcaset(self, term1, term2):

    """
      Return the set of lowest common ancestors (ancestors with the highest depth)
    """

    k  = (term1, term2);
    ki = (term2, term1);

    if k in self.lcaset_cache:
      return self.lcaset_cache[k];
    elif ki in self.lcaset_cache:
      return self.lcaset_cache[ki];
    #fi

    canc = self.commonanc(term1, term2);
    mdp  = 0;
    lcas = set([]);

    for anc in canc:
      dp = self.depth(anc);
      if dp > mdp:
        mdp = dp;
        lcas =  set([anc]);
      elif dp == mdp:
        lcas = lcas | set([anc]);
      #fi
    #efor

    self.lcaset_cache[k] = lcas;
    return lcas;

  #edef

  #############################################################################

  def mdist(self, term, anc):

    """
      The shortest distance between a term and it's ancestor.
        returns -1 if the two are not connected at all.
    """

    k  = (term, anc);
    if k in self.mdist_cache:
      return self.mdist_cache[k];
    #fi

    if term == anc:
      return 0;
    #fi
 
    parents = set([ t.id for t in self.obo[term].parents ]);

      # If the two are not connected at all
    if len(parents) == 0:
      return -1;
    #fi

    dps = [ 0 for i in xrange(len(parents)) ];

    parents = list(parents);
    for anci in xrange(len(parents)):
      dps[anci] = self.mdist(parents[anci], anc);
    #efor

    if sum(dps) == -1*(len(dps)):
      return -1;
    #fi

    retdep = min([ d for d in dps if d > -1 ]);

    self.mdist_cache[k] = retdep+1;
    return retdep + 1;

  #edef

  #############################################################################

  def minspla(self, term1, term2, anc):

    """
      Return the minimal path length from term1 to term2 via anc.
        returns -1 if anc is not an ancestor
    """

    dist1 = self.mdist(term1, anc);
    if dist1 == -1:
      return -1;
    #fi

    dist2 = self.mdist(term2, anc);
    if dist2 == -1:
      return -1;
    #fi

    return (dist1 + dist2);

  #edef

  #############################################################################

  def minspl(self, term1, term2):

    ancs = list(self.lcaset(term1, term2));

    dists = [ 0 for i in xrange(len(ancs)) ];

    for anci in xrange(len(ancs)):
      dists[anci] = self.minspla(term1, term2, ancs[anci]);
    #efor

    return min(dists);

  #efor

  #############################################################################

  def termdot(self, term1, term2):

    """
      Calculate the dot product between two terms
    """

    k  = (term1, term2);
    ki = (term2, term1);

    if k in self.dot_cache:
      return self.dot_cache[k];
    elif ki in self.dot_cache:
      return self.dot_cache[ki];
    #fi

    lca   = list(self.lcaset(term1, term2))[0];
    lcadp = float(self.depth(lca));
    mspl  = float(self.minspl(term1, term2));

    denom = mspl + (2.0 * lcadp);
    if denom == 0:
      dot = 0;
    else:
      dot = (2.0 * lcadp) / denom;
    #fi

    self.dot_cache[k] = dot;
    return dot;

  #edef

  #############################################################################

  def cos_base(self, gene1, gene2, IAF):

    gh = 0;

    for i in xrange(len(gene1)):
      (ti, eci) = gene1[i];
      for j in xrange(len(gene2)):
        (tj, ecj) = gene2[j];

        ai   = self.weights[eci] * IAF[ti];
        bj   = self.weights[ecj] * IAF[tj];
        eiej = self.termdot(ti, tj);

        gh = gh + (ai * bj * eiej);
      #efor
    #efor

    return gh;
  #edef

  #############################################################################

  def sim_ontology(self, gene1, gene2, IAF):

    """
      Determine the similarity for two genes in a given ontology.
        gene* format:
          [ (goterm1, goterm1EC), ... (goterm2, gotermEC) ]
    """

    a = self.cos_base(gene1, gene2, IAF);
    b = sqrt(self.cos_base(gene1, gene1, IAF));
    c = sqrt(self.cos_base(gene2, gene2, IAF));

    if (a == 0) or (b == 0):
      return 0;
    #fi

    return a / (b * c);

  #edef

  #############################################################################

  def sim(self, gene1, gene2, IAF, onts=['molecular_function', 'cellular_component', 'biological_process']):

    ont_gene1 = [];
    ont_gene2 = [];
    sims      = [ 0  for i in range(len(onts)) ];

    for i in range(len(onts)):
      ont_gene1 = [ (t,e) for (t,e) in gene1 if self.obo[t].namespace == onts[i] ]
      ont_gene2 = [ (t,e) for (t,e) in gene2 if self.obo[t].namespace == onts[i] ]

      sims[i] = self.sim_ontology(ont_gene1, ont_gene2, IAF);
    #efor

    return sims;

  #edef

  #############################################################################

#eclass
