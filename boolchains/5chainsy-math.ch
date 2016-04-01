@x Mathematica notation rather than infix; use bool.m
printf("%s%d",s?"~":"", d);
@y
printf("%sx%d",s?"c":"", d);
@z
@x
printf("(");
explain(op==12? c->history2: s^(op==10)? mask-c->history2: c->history2, ppp);
printf("%c", op==12?'^': s^(op==11)? '|': '&');
explain(s^(op==9)? mask-t: t,ppp);
printf(")");
@y
printf("%s[",op==12?"bx": s^(op==11)? "bo": "ba");
explain(op==12? c->history2: s^(op==10)? mask-c->history2: c->history2, ppp);
printf(",");
explain(s^(op==9)? mask-t: t,ppp);
printf("]");
@z
