let bytemode = process.argv.length <= 2;
var data;
var nchar = 0;
var nbit = 0;
var progchar;

function bit2lam(bit) {
  return function(x0) {
    return function(x1) {
        return bit ? x1 : x0
      }
  }
}

function byte2lam(bits,n) {
  return function(z) {
    return n-- ? z (function(a) { return bit2lam((bits>>n)&1)(a) })
                   (function(b) { return byte2lam(bits,n)(b) }) // cons bitn bits>n
               : function(y) { return y }                                         // nil
  }
}

function input(n) {           // input from n'th character onward
  return function(z) {
    if (n >= data.length) {
      return function(y) { return y }     // nil
    }
    let c = data[n]; // cons charn chars>n
    return z (function(a) { return (bytemode ? byte2lam(c,8) : bit2lam(c&1))(a) })
             (function(b) { return input(n+1)(b) })
  }
}

function lam2bit(lambit) {
  return lambit(function(){return 0})(function(){return 1})()  // force suspension
  // return lambit(0)(1);
}

function lam2byte(lambits, x) {
  return lambits(function(lambit) {
           y = 2*x + lam2bit(lambit);
           return function(lamtail) {
             return function() { return lam2byte(lamtail, y) }
           }
         })(String.fromCharCode(x))              // end of byte
}

function output(prog) {
  return prog(function(c) {      // more chars
    process.stdout.write(bytemode ? lam2byte(c,0) : lam2bit(c) ? '1' : '0');
    return function(tail) {
      return function() { return output(tail) }
    }
  })(42)                         // end of output
}

function getbit() {
  if (nbit==0) {
    progchar = data[nchar++];
    nbit = bytemode ? 8 : 1;
  }
  let bit = (progchar >> --nbit) & 1;
  return bit;
}

function program() {
  if (getbit()) {               // variable
    var i = 0;
    while (getbit()==1) { i++ }
    return function() { return arguments[i] }
  } else if (getbit()) {        // application
    let p = program();
    let q = program();
    return function(...args) {
      return p(...args)(function(arg) { return q(...args)(arg) }) // suspend argument
    }
  } else {
    let p = program();
    return function(...args) {
      return function(arg) { return p(arg, ...args) }  // extend environment with one more argument
    }
  }
}

process.stdin.on('readable', () => {
  if ((data = process.stdin.read()) != null) {
    prog = program()();
    output(prog(input(nchar)))             // run program with empty env on input
  }
});
