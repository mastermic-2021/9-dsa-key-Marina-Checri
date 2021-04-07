# Attaque sur DSA

## Problème

Le fichier `main.gp` contient une clef publique DSA `[g,q,X]`,
ainsi qu'une fonction permettant de vérifier la validité d'une signature
`[h(m),r,s]`.

Le fichier `input.txt` contient un certain nombre de signatures DSA,
obtenues pour des entiers $k<10^10$.

On demande de retrouver la clef privée `x`.

## Format

Vous devez écrire un programme `main.gp` en Pari/GP dont l'exécution via
```
gp -fq < main.gp
```
affiche (uniquement) la solution cherchée.

taper `make check` permet de vérifier que votre solution est bonne.

Veillez à mettre des commentaires sur votre démarche et sa validité
dans le fichier ``main.gp``.

De manière alternative, vous pouvez écrire un programme `main.c` qui
fasse la même chose.

## Validation

Il reste à faire un commit et à envoyer votre solution pour l'enregistrer
```
git add main.gp
git commit -m 'ma solution'
git push
```

