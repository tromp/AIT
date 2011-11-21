sub I{my$i=shift;sub{my$c;($B[$i]||=defined($c=getc)
 ?sub{shift->(sub{my$x=shift;sub{$c?shift:$x}})->(I($i+1))}
 :sub{sub{shift}})->(shift)}}
sub O{shift->(sub{print shift->(sub{0})->(sub{1})->();sub{my$r=shift;sub{O($r)}}})->("\n")}
sub P{if(getc){my$i;$i++while getc;sub{$_[$i]}}
   elsif(getc){my$p=P();my$q=P();sub{my@a=@_;$p->(@a)->(sub{$q->(@a)->(shift)})}}
          else{my$p=P();sub{my@a=@_;sub{$p->(shift,@a)}}}}
$|=1;print O P()->()->(I(0))
