// makes an Evaluator object
function makeEvaluator(expr)
{
  // checks the expression format
  if (!/^\s*(\d+(\.\d+)?\s*(\+|-|\*|\/)\s*)*\d+(\.\d+)?$/.test(expr)) {
    throw 'Invalid expression.';
  }

  // remove spaces
  expr = expr.replace(/ /g, '');
  
  // splits by the operators
  expr = expr.replace(/\+/g, ' + ');
  expr = expr.replace(/-/g, ' - ');
  expr = expr.replace(/\*/g, ' * ');
  expr = expr.replace(/\//g, ' / ');
  var exprArray = expr.split(' ');
  
  // checks array length
  if (exprArray.length % 2 !== 1) {
    throw 'Invalid expression.';
  }
  
  // builds the real array
  var opsArray = [];
  var opsSet = {'+': true, '-': true, '*': true, '/': true};
  for (var i = 0; i < exprArray.length; i++) {
    var val = exprArray[i];
    if (val in opsSet) {
      opsArray.push({op: val});
    } else {
      opsArray.push({val: parseFloat(val), str: val.toString()});
    }
  }
  
  return {
    _a: opsArray,
    
    getNumOps: function() {
      return Math.floor(this._a.length / 2);
    },
    
    getResult: function(order) {
      function getRep(obj) {
        if (!('rep' in obj)) {
          return obj;
        } else {
          return obj.rep = getRep(obj.rep);
        }
      }
      function addParens(lStr, lOp, rStr, rOp, op) {
        if (op === '+') {
          return lStr + op + rStr;
        } else if (op === '-') {
          if (rOp === '+' || rOp === '-') {
            return lStr + op + '(' + rStr + ')';
          } else {
            return lStr + op + rStr;
          }
        } else if (op === '*') {
          if (lOp === '+' || lOp === '-' || lOp === '/') {
            lStr = '(' + lStr + ')';
          }
          if (rOp === '+' || rOp === '-' || rOp === '/') {
            rStr = '(' + rStr + ')';
          }
          return lStr + op + rStr;
        } else if (op === '/') {
          if (lOp !== 'N') {
            lStr = '(' + lStr + ')';
          }
          if (rOp !== 'N') {
            rStr = '(' + rStr + ')';
          }
          return lStr + op + rStr;
        } else {
          throw '';
        }
      }
      for (var i = 0; i < this._a.length; i++) {
        if ('rep' in this._a[i]) {
          delete this._a[i].rep;
        }
        if ('op' in this._a[i] && 'str' in this._a[i]) {
          delete this._a[i].str;
        }
        if ('op' in this._a[i] && 'val' in this._a[i]) {
          delete this._a[i].val;
        }
      }
      if (order.length * 2 + 1 !== this._a.length) {
        throw 'Invalid order description.';
      }
      for (var i = 0; i < order.length; i++) {
        if (order[i] < 0 || order[i] > order.length - 1) {
          throw 'Invalid order description.';
        }
        if ('rep' in this._a[2*order[i]+1]) {
          throw 'Invalid order description.';
        }
        var lRep = getRep(this._a[2*order[i]]);
        var rRep = getRep(this._a[2*order[i]+2]);
        // now all representatives have value & string
        var op = this._a[2*order[i]+1].op;
        if (op === '+') {
          this._a[2*order[i]+1].val = lRep.val + rRep.val;
        } else if (op === '-') {
          this._a[2*order[i]+1].val = lRep.val - rRep.val;
        } else if (op === '*') {
          this._a[2*order[i]+1].val = lRep.val * rRep.val;
        } else if (op === '/') {
          this._a[2*order[i]+1].val = lRep.val / rRep.val;
        } else {
          throw '';
        }
        var lOp = ('op' in lRep) ? lRep.op : 'N';
        var rOp = ('op' in rRep) ? rRep.op : 'N';
        this._a[2*order[i]+1].str = addParens(lRep.str, lOp, rRep.str, rOp, op);
        // puts the new value as representative of the other two
        lRep.rep = rRep.rep = this._a[2*order[i]+1];
      }
      var rep = getRep(this._a[0]);
      return [rep.val, rep.str];
    }
  };
}

function parenthesize(expr, result)
{ 
  // it's a brute force solution, just checks all possible operation orders
  
  // makes an evaluator
  ev = makeEvaluator(expr);
  
  // converts the result to a numerical value
  result = parseFloat(result);

  // initial operation order
  var order = [];
  for (var i = 0; i < ev.getNumOps(); i++) {
    order.push(i);
  }
  
  // solutions map
  var solutionsMap = {};
  
  // generates all permutations
  // - Find the largest index k such that a[k] < a[k + 1]. If no such index exists, the permutation is the last permutation.
  // - Find the largest index l such that a[k] < a[l]. Since k + 1 is such an index, l is well defined and satisfies k < l.
  // - Swap a[k] with a[l].
  // - Reverse the sequence from a[k + 1] up to and including the final element a[n].
  while (true) {
    // tries with the current permutation
    var res = ev.getResult(order);
    if (res[0] === result) {
      solutionsMap[res[1]] = true;
    }
    
    // gets the next permutation
    var k;
    for (k = order.length - 2; k >= 0; k--) {
      if (order[k] < order[k+1]) {
        break;
      }
    }
    if (k < 0) {
      break;
    }
    var l;
    for (l = order.length - 1; l >= 0; l--) {
      if (order[k] < order[l]) {
        break;
      }
    }
    var tmp = order[k];
    order[k] = order[l];
    order[l] = tmp;
    for (var x1 = k + 1, x2 = order.length - 1; x1 < x2; x1++, x2--) {
      tmp = order[x1];
      order[x1] = order[x2];
      order[x2] = tmp;
    }
  }
  
  // gest the solutions array
  var solutions = [];
  for (var sol in solutionsMap) {
    solutions.push(sol);
  }
  
  return solutions;
}
