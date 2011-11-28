$z=pop=~/8/;

sub bit2lam {my$c=pop;sub{my$x=pop;sub{$c?pop:$x}}}
sub byte2lam {my($c,$x)=@_;sub{$x--?
 pop->(bit2lam(vec$c,$x,1))->(byte2lam($c,$x)):sub{pop}}}
sub input {my$i=pop;sub{my$c;($B[$i]||=defined($c=getc)?sub{pop->($z?
 byte2lam($c,8):bit2lam($c))->(input($i+1))}:sub{sub{pop}})->(pop)}}

sub lam2bit {pop->(sub{0})->(sub{1})->()}
sub lam2byte {my$x=pop;pop->(sub{$x=2*$x+lam2bit(pop);
 sub{my$r=pop;sub{lam2byte($r,$x)}}})->(chr$x)}
sub output {pop->(sub{print($z?lam2byte(pop,0):lam2bit(pop));
 sub{my$r=pop;sub{output($r)}}})->("\n")}

sub getbit {$x||=($c=getc,$z?8:1);vec$c,--$x,1}
sub program {if(getbit()){my$i;$i++while getbit();sub{$_[$i]}}
 elsif(getbit()){my$p=program();my$q=program();sub{my@bit2lam
 =@_;$p->(@bit2lam)->(sub{$q->(@bit2lam)->(pop)})}}else{my$p=
 program();sub{my@bit2lam=@_;sub{$p->(pop,@bit2lam)}}}}

$|=1; print output program()->()->(input(0))
