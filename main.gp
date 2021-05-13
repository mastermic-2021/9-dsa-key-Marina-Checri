dsa_pub = [Mod(16, 2359457956956300567038105751718832373634513504534942514002305419604815592073181005834416173), 589864489239075141759526437929708093408628376133735628500576354901203898018295251458604043, 2028727269671031475103905404250865899391487240939480351378663127451217489613162734122924934];
check(s,dsa_pub) = {
  my(h,r,g,q,X);
  [h,r,s] = s;
  [g,q,X] = dsa_pub;
  X=Mod(X,g.mod);
  lift( (g^h*X^r)^(1/s % q) ) % q == r;
}



/* ****************************************************************************** */
/* ******************************* Explications : ******************************* */
/* ****************************************************************************** */

/*
 * On possède un ensemble de signatures (r,s).
 
 * Une première étape consiste à savoir s'il existe au moins
 * deux couples de valeurs qui ont été obtenus à partir de la même valeur k.
 * Alors, il suffira de mettre en place l'attaque expliquée dans le tp7.
 //* C'est ce que cherche la fonction find_same_r();

 * Rappel rapide de l'attaque :
   * si une même valeur k a été utilisée pour signer m et m',
     alors le r_k obtenu est le même pour les deux signatures.
   * Si on dispose de deux couples (r,s_k) et (r,s_k'), on peut retrouver k:
     k = (h(m)-h(m')) (s_k - s_k')^{-1}
   * Et alors s_k = k^{-1} * (h(m) + x*r) mod q
   * On connait toutes les valeurs sauf x :
     k * s_k= (h(m) + x*r) [q]
     k * s_k - h(m) = x*r  [q]
     (k * s_k - h(m)) * r^{-1} = x [q]


 * Ici, il n'y a pas de tels couples. On cherche donc deux couples qui
 * auraient été obtenus à partir des valeurs k et k+a pour un entier a.
 * Dans ce cas également, on pourra retrouver k, et donc x.
   * Si (r,s) la signature de m est obtenue à partir de k,
     et (r',s') celle de m' est obtenue à partir de k+a.
     On a r' = r * g^a mod p mod q.
   * Alors g^a * (ks -xr = h(m)) auquel on soustrait ks' - xr' = h(m') donne
   
                  [   ks    = h(m) + xr ] * g^a
                - [ (k+a)s' = h(m')+ xr']
     ____________________________________________________________________
     
     ks * g^a  - (k+a)*s'   =  g^a*h(m) + xr * g^a  - h(m') - xr'
     ks * g^a  - (k+a)*s'   =  g^a*h(m) + xr * g^a  - h(m') - x (g^a * r)
     ks * g^a  - (k+a)*s'   =  g^a*h(m) - h(m')
     k*s *g^a  - ks' - a*s' =  g^a*h(m) - h(m')
     k (s*g^a - s') - a*s'  =  g^a*h(m) - h(m')
     k (s*g^a - s')         =  g^a*h(m) - h(m') + a*s'

   * D'où k (g^a s - s') = h(m) * g^a - h(m') + a*s'.
     
     Et la seule inconnue est k.
   * On obtient donc la valeur de k et donc celle de x.

*/

/*
 * Nota Bene :
 * lors de discussions avec mes camarades, certains ont soulignés que l'espace
   des k à parcourir n'était pas énorme, et qu'on pouvait donc effectuer directement
   une attaque brute force en tirant des k aléatoires
   tels qu'on obtienne deux couples avec le même r.
   
 * Cette attaque n'est pas généralisable si l'espace devient bien plus grand,
   alors que celle qui consiste à chercher deux couples obtenus à partir de k et k+a
   pourrait se révéler plus adaptée pour un très grand nombre de valeurs.

 * Cependant, Daphné et moi avons essayé de partir sur le côté mathématique du challenge
   avant de nous pencher sur la programmation.
 * Si nous avons bien réussi à déterminer k (et donc x) théoriquement,
   l'implémentation n'a pas fonctionnée.
 * C'est pourquoi, on implémente tout de même une attaque brute force.
   Le principe est de tirer aléatoirement un k, et une fois le r' calculé,
   de regarder s'il existe un r dans les données qui soit identique :
   on aura trouvé le k à l'origine de ce r.
 * On calcule alors simplement le x comme étant x = (k * s_k - h(m)) * r^{-1} [q].
 */


/* ****************************************************************************** */
/* ******************************** Fonctions : ********************************* */
/* ****************************************************************************** */




/*On prend en paramètre un tableau de [h(m),r,s]*/
trouve_couples_k_identique(tab)={
	my(m, sig_k, sig_k_);
        m = Map();
	for(i=1,#tab, if(mapisdefined(m,tab[i][2]),
	return ([mapget(m, tab[i][2]),tab[i]])
	, mapput(m, tab[i][2], tab[i])) ); 
};

/*On prend en paramètre une map de r -> [h(m),r,s]*/
trouve_couples_k_k_plus_a(my_map, a, p, q, g, X)={
        my(g_a, h, r, s, h_, r_, s_, my_vec);
	[g,q,X]=dsa_pub;
	p = g.mod;
	g_a = g^a;
	\\print("a = ", a, " et g^a = ", lift(g_a));

	my_vec = Vec(my_map);
	for(i=1, #my_vec,
	   r = my_vec[i];
	   r_ = lift(r*g_a);
	   \\print("a = ", a, " et g^a = " g_a);
	   \\print("r = ", r , " r_ = ",r_);
	   if(mapisdefined(my_map, r_),
	      [h,r,s] = mapget(my_map, my_vec[i]);
	      [h_,r_,s_] =  mapget(my_map, r_);
	      if(h!=h_,
	         return ([a, [h,r,s], [h_,r_,s_]])
	      );
	   );
	);
};



/* Attaque Brute_force */
brute_force_attack_on_k(my_map, p, q, g, X)={
	my(k,h,r,s);
	egalite=0;
	while(!egalite,
	      k = random(10^10-1)+1;
	      r_= lift(Mod(lift(g^k),q));
	      if(mapisdefined(my_map,r_),
	   	 egalite=1;
		 [h,r,s]=mapget(my_map,r_)));
	return ([k, [h,r,s]]);
};





/* ****************************************************************************** */
/* ******************************* Application : ******************************** */
/* ****************************************************************************** */


text=readvec("input.txt");
map_sig = Map();
for(i=1,#text, mapput(map_sig, text[i][2], text[i])); 

[g,q,X]=dsa_pub;
p = g.mod;


/*
couple = trouve_couples_k_k_plus_a(map_sig, 18173, p, q, g, X);

count = 18000;
while(couple == 0,couple = trouve_couples_k_k_plus_a(map_sig, count, p , q, g , X); count = count +1; )

a=couple[1];
[h, r, s ]=couple[2];
[h_,r_,s_]=couple[3];


\\g = lift(g) * Mod(1,q);
k = (h*g^a - h_ + a*s_)*(g^a*s - s_)^{-1};
\\k = lift((h*g^a - h_ + a*s_)*(g^a*s - s_)^{-1}) * Mod(1,q);
k = lift(k);
x = (k*s-h)*(Mod(r,q))^{-1};
\\222517259583957478623412508904334816977511571012655868126197869285530929696119562344776227
print(lift(x));
*/




bon_couple=brute_force_attack_on_k(map_sig, p, q, g, X);
k=bon_couple[1];
[h,r,s] = bon_couple[2];

x=lift((k*s-h)*(Mod(r,q))^{-1});
print(x);