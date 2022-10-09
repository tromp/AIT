import Control.Applicative hiding((<|>),many)
import Text.Parsec
import System.IO
data W=S!Char|F(W->W)
j(F f)=f
f=c$F id
c=F .const
a x y v=x v`j`y v
l e v=F$ \a->e(a:v)
q x y=F$ \z->z`j`x`j`y
b n=if even n then F c else f
s w=c where(S c)=w`j`S '0'`j`S '1'
o p=map s.g.(p[]`j`).foldr(q.b.fromEnum)f
g l=case (l`j`c(c.S$':'))of{S ':'->l`j`F c:g(l`j`f);F _->[]}
x=char '0'*>(l<$char '0'<*>x<|>a<$char '1'<*>x<*>x)<|>flip(!!)<$>pred.length<$>many(char '1')<*char '0'
main=hSetBuffering stdout NoBuffering>>interact(either(error.show)id.parse(o<$>x<*>getInput)"")
