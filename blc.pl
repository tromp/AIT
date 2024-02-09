$z=pop=~/8/;

sub bit2lam {
  my $bit = pop;
  sub {
    my $x0 = pop;
      sub {
        my $x1 = pop;
        $bit ? $x1 : $x0
      }
  }
}

sub byte2lam {
  my ($bits,$n) = @_;
  sub {
    $n-- ? pop->(bit2lam(vec$bits,$n,1))->(byte2lam($bits,$n)) # cons bitn bits>n
         : sub { pop }                                         # nil
  }
}

sub input {
  my $n = pop;                                # input from n'th character onward
  sub {
    my $c;
    ($B[$n] ||= defined($c=getc) ?
       sub { pop->($z ? byte2lam($c,8) : bit2lam($c))->(input($n+1)) # cons charn chars>n
       } :
       sub { sub { pop } }                                           # nil
    )->(pop)
  }
}

sub lam2bit {
  pop->(sub{0})->(sub{1})->()              # force suspension
}

sub lam2byte {
  my $x = pop;	                           # 2nd argument is partial byte
  pop->(sub {
          $x = 2*$x + lam2bit(pop);
          sub {
            my $tail = pop;
            sub { lam2byte($tail, $x) }
          }
        })->(chr $x)                       # end of byte
}

sub output {
  pop->(sub {                              # more chars
          my $c = pop;
          print($z ? lam2byte($c,0) : lam2bit($c));
          sub {
            my $tail = pop;
            sub { output($tail) }
          }
        })->(0)                         # end of output
}

sub getbit {
  $n ||= ($c = getc, $z?8:1);
  vec $c,--$n,1
}

sub program {
  if (getbit()) {             # variable
    my $i;
    $i++ while getbit();
    sub { $_[$i] }
  } elsif (getbit()) {        # application
    my $p=program();
    my $q=program();
    sub {
      my @env = @_;
      $p->(@env)->(sub { $q->(@env)->(pop) }) # suspend argument
    }
  } else {
    my $p = program();
    sub {
      my @env = @_;
      sub { $p->(pop,@env) }  # extend environment with one more argument
    }
  }
}

$| = 1;                                      # non zero value sets autoflush
output program()->()->(input(0))             # run program with empty env on input
