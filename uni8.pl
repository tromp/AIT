sub getb {if(!@b){for(my$x=256+ord(getc);$x>1;$x>>=1){unshift@b,$x&1}};shift@b}
sub b{my($c,$m)=@_;sub{($m>>=1)
 ?shift->(sub{my$x=shift;sub{$c&$m?shift:$x}})->(b($c,$m))
 :sub{shift}}}
sub I{my$i=shift;sub{my$c;($B[$i]||=defined($c=getc)
 ?sub{shift->(b(ord$c,256))->(I($i+1))}
 :sub{sub{shift}})->(shift)}}
sub d{my$x=shift;shift->(sub{$x=2*$x+shift->(sub{0})->(sub{1})->();
  sub{my$r=shift;sub{d($x,$r)}}})->(chr$x)}
sub O{shift->(sub{print d(0,shift);sub{my$r=shift;sub{O($r)}}})->("\n")}
sub P{if(getb()){my$i;$i++while getb();sub{$_[$i]}}
   elsif(getb()){my$p=P();my$q=P();sub{my@a=@_;$p->(@a)->(sub{$q->(@a)->(shift)})}}
          else{my$p=P();sub{my@a=@_;sub{$p->(shift,@a)}}}}
$|=1;print O P()->()->(I(0))
