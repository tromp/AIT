import Control.Applicative hiding((<|>),many)
import Text.Parsec
import System.IO
data W=S!Char|F(W->W)
(F f)&w=f w
f=c$F id
c=F .const
a x y v=x v&y v
l e v=F$ \a->e(a:v)
q x y=F$ \z->z&x&y
b n=if even n then F c else f
s w=c where(S c)=w&S '0'&S '1'
o p=map s.g.(p[]&).foldr(q.b.fromEnum)f
g l=case (l&c(c.S$':'))of{S ':'->l&F c:g(l&f);F _->[]}
x=char '0'*>(l<$char '0'<*>x<|>a<$char '1'<*>x<*>x)<|>flip(!!)<$>pred.length<$>many(char '1')<*char '0'
main=hSetBuffering stdout NoBuffering>>interact(either(error.show)id.parse(o<$>x<*>getInput)"")
