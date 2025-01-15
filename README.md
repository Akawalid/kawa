## Table of Contents

0. [Extensions_rajoutées](#Extensions_rajoutées)
0. [Kawa](#Kawa)
1. [Parser](#Parser)
2. [TypeChecker](#TypeChecker)
3. [Interpreter](#Interpreter)

---
## 0. **Extensions_rajoutées**: 
  - champs immuables
  - visibilité
  - déclaration en série et avec ou sans initialisation
  - champs statiques
  - tests de type
  - tableaux
  - classes et méthodes abstraites
  - Déclarations simplifié
  - "Did you mean recursion?"
  - important: 
    - les fichiers de tests donnée ne fonctionneront pas à cause de l'extension 'déclarations simplifié'
    - les acces au tableau se font comme le suivant tab[n] dans Kawa est n[tab]
    - final est implementé seulement sur les attributs

## 0. **Kawa**

### Les éléments rajoutés :
-Dans `typ`, les élements rajoutés sont :
    - **`TArray of typ`** : Permet de reconnaître les types tabulaires.
    - **`TNull`** : Représente le type de la constante `null`.

<a name="ajout-access"></a>
- Ajout du type **`access`** : Représente les droits d'accès aux attributs et méthodes.


- Dans `Binop` :
  - **`Instanceof`** : Vérifie si un objet est une instance d'une classe.
  - **`Rem`** : Calcule le reste d'une division (modulo).

- Dans `expr` :
  - **`NewArray`** : Pour créer un tableau de type `typ` avec une liste d'expressions optionnelles (plus de détails dans le fichier `Kawa.ml`).
  - **`Array`** : Pour créer un tableau directement, par exemple : `[1; 3; 9..]`.
- Dans `mem_access`
    - **`Tab(e, i)`**: Pour acceder à la case mémoire `eval(e, env)[i]`
- Dans `instr`:
   - `If2`: pour représenter les conditionnelles partiels (if sans le else)

- Dans `method_def` :
    <a name="meths"></a>
  - **`visibility`** : Représente la visibilité de la méthode.
  - **`locals`** : Dans `locals`, l'ajout de **`expr option`** dans son type représente l'existence d'un initialiseur pour la variable locale.
- **`abstract_method_def`** : Structure spéciale pour les méthodes abstraites, car elles sont très différentes des méthodes régulières. Elle contient :  
  - **`abs_method_name`** : Le nom de la méthode.  
  - **`abs_visibility`** : La visibilité de la méthode.  
  - **`abs_params`** : Liste des types des paramètres (il n'est pas nécessaire de stocker les noms des paramètres).  
  - **`abs_return`** : Le type de retour de la méthode.  
- **Dans `class_def`** : Les champs suivants ont été ajoutés :  
  - **`is_abstract`** : Boolean pour indiquer s'il s'agit d'une classe abstraite.  
  - **`s_attributs`** : Liste des attributs statiques, où chaque attribut est représenté par :  
    - **`string`** : Nom de l'attribut.  
    - **`typ`** : Type de l'attribut.  
    - **`access`** : Visibilité de l'attribut.  
    - **`bool`** : Indique si l'attribut est `final` ou non.  
    - **`expr option`** : Expression d'initialisation de l'attribut (si elle existe).  

  - **`s_methods`** : Liste des méthodes statiques.  
  - **`abstract_methods`** : Liste des méthodes abstraites.  
- **Dans `program`** :  
  - **`globals`** : Un **`expr option`** a été ajouté pour chaque variable globale, représentant son initialisateur (si elle en a un).  

## 1. **Parser**
### Explication des règles
#### parent:
 utilisé pour reconnaître l'héritage, renvoie un type `string option` :
- **`None`** : Indique l'absence de superclasse.
- **`Some id`** : Indique que la classe hérite de la classe `id`.

#### typ:
Règle récursive pour reconnaître les tableaux de dimension n, décomposée en deux parties : `typ_base` et `typ []`.

#### dimensions, maybe_empty_dimensions, empty_dimensions_or_nothing:
Ces trois règles sont utilisées pour reconnaître la création d'un tableau, particulièrement la séquence de dimensions `[n0][n1]...[n_k][]...[]`.

- **`dimensions`** : Sert à reconnaître la première partie de la séquence, `[n0][n1]...[n_k]`, où chaque `n` représente une dimension avec une taille spécifique.
- **`maybe_empty_dimensions`** : Sert à reconnaître le début de la séquence, `[]...[]`, ou à identifier le cas où il n'y a aucune dimension avec une taille indéfinie.
- **`empty_dimensions_or_nothing`** : Sert à reconnaître la partie restante de la séquence vide, c'est-à-dire `[]...[]` qui représente des dimensions sans taille définie.

#### params, params_nempty:
Ces règles sont utilisées pour reconnaître une liste non vide des arguments formels d'une méthode. Bien qu'il soit possible de faire cela avec `non_empty_list`, il est nécessaire de déclarer un non-terminal pour reconnaître `typ IDENT`, ce qui revient au même.

#### abs_method_params, abs_method_params_nempty:
Ces règles sont utilisées pour reconnaître les paramètres d'une méthode abstraite. Ce sont les mêmes règles que pour `params` et `params_nempty`, elles différent dans la valeur de retour. 

les méthodes abstraites n'ont pas besoin de stocker les noms des paramètres. Ainsi, seules les listes de types des paramètres sont renvoyées, sans les identifiants des paramètres.


#### var_decl_l, var_decl:
Ces règles servent à reconnaître la liste de déclarations de variables. On aurait dû utiliser `list(var_decl)`, mais cela causerait des conflits, car la règle de réduction `list(var_decl)` doit être appliquée avec la priorité `REDUCE_PREFERENCE`.

#### ident_and_maybe_initialisation:
 utilisé avec seperated_non_empty_list pour reconnaitre la déclaration multiple avec initilalisation dans les attributs, les variables globales et les variables locales.

#### att_decl, att_decl_l, method_def:
Ces règles sont utilisées pour reconnaître l'ensemble des attributs et des méthodes d'une classe. L'ordre des mots-clés comme `static`, `final`, `private`, `abstract`, etc., est indifférent, ce qui explique la longueur des règles, car il faut tenir compte de toutes les permutations possibles de ces mots-clés.
- Explication de la valeur de retour de `att_decl`:
Les attributs renvoient un type de la forme `bool * ((string * typ * access * bool * expr option) list)` :
Voici ce que chaque composant représente :

- **`bool`** : Indique si l'attribut est statique ou non (si `true`, l'attribut est statique).
- **`string`** : Le nom de l'attribut.
- **`typ`** : Le type de l'attribut.
- **`access`** : La visibilité de l'attribut ( [plus de détails](#ajout-access).)
- **`bool`** : Indique si l'attribut est final (si `true`, l'attribut est final et ne peut pas être modifié après son initialisation).
- **`expr option`** : L'initialisation de l'attribut :
  - **`Some e`** signifie que l'attribut est initialisé avec l'expression `e`.
  - **`None`** signifie que l'attribut n'est pas initialisé.

-Explication de la valeur de retour de `method_def`:[lien vers l'explication des méthodes](#meths).



#### class_def:
La règle `l_att_decl` renvoie une liste de listes en raison des déclarations multiples d'attributs. Par conséquent, on utilise la fonction `List.flatten` pour aplatir cette structure. Ensuite, on répartit les attributs en fonction du booléen `statique` dans deux listes distinctes : `att` (attributs non statiques) et `s_att` (attributs statiques).

La même logique est appliquée pour les méthodes, elles sont réparties sur trois listes: `meths`, `s_meths` (méthodes statiques), et `abs_meths` (méthodes abstraites).

- **Explication de la structure utilisée pour répartir les méthodes** : [lien](#explication-du-code-caml-dans-le-parser)

#### mem :
On a ajouté la dérivation `INT LBRACK expression RBRACK` pour reccnnaitre les accès à un tableau comme java `tab[i]`

### Explication du code caml dans le parser:
- **`method_type`** : Ce type est utilisé pour reconnaître les méthodes d'une classe. Une méthode peut être abstraite ou non, ce qui donne deux objets de nature différente : `method_def` ou `abstract_method_def`. Comme on ne peut pas regrouper deux types différents dans une même liste, ce type a été créé pour les rassembler :  
  - **`Abstract of abstract_method_def`** : Représente les objets de méthodes abstraites.  
  - **`Concret of bool * method_def`** : Représente un objet de méthode concrète, avec :  
    - **`bool`** : Indique si la méthode est statique et qui nous permet ensuite de répartir les méthodes dans les champs `s_methods` et `methods` de `class_def`.
    - **`method_def`** : L'objet de la méthode.  
- Les fonctions **`create_meth_object`** et **`create_abs_meth_object`** servent à simplifier le code. Elles renvoient un objet de méthode dont le contenu est constitué des paramètres passés en argument.  
---
## 2. **TypeChecker**
Dans le suivant, les explicaitons vont suivre la l'ordre de déclaration des focntions dans le typechecker:

- **`pg_state`** : C'est une structure globale utilisée par le typechecker. Elle contient :
  - **`this_k_found`** : Signifie 'this_keyword_found'. Utilisé pour savoir si le mot-clé `this` est utilisé dans une méthode statique. Il est mis à `true` lorsqu'on rencontre une expression `This`, et remis à `false` dès qu'on termine la vérification d'une méthode statique.
  - **`current_method`** : Stocke le nom de la méthode en cours de vérification. Il est mis à jour dès qu'on entre dans une méthode. Initialisé à "main", il est utilisé pour déterminer si on est dans un constructeur, et donc pour tester si l'utilisateur essaie de modifier la valeur d'un attribut immuable (final) en dehors du constructeur.

  - **`evaluating_left_side_of_assign`** : Indique si le côté gauche d'une affectation est en cours d'évaluation. Il est mis à `true` juste avant l'appel à l'évaluation du côté gauche d'une affectation, et remis à `false` après l'évaluation. Cela sert à détecter lorsque l'utilisateur essaie de modifier un attribut immuable.

  - **`checked_classes`** : Table de hachage pour stocker les classes vérifiées. Si aucune abstraction n'est présente, ce champ n'est pas nécessaire. La vérification de la cohérence d'une méthode abstraite nécessite la vérification de la cohérence de ses classes parentes de manière récursive. Pour éviter les vérifications redondantes de la même classe dans la boucle 
  `List.iter (fun c_def -> check_class c_def tenv) (List.rev p.classes);`, Une optimisation a été réalisée sur ce parcours et est expliquée en commentaire à la fin du programme, attaché à la ligne de code d'en dessus.
  
  - **`abstract_methods`** : Table de hachage pour stocker les méthodes abstraites. Elle est utilisée dans la vérification de la cohérence d'une classe en termes d'abstraction. L'algorithme parcourt l'héritage des classes de haut en bas, stocke les méthodes abstraites rencontrées, retire les méthodes concrètes de la table et vérifie la cohérence de la classe. Les détails de l'algorithme sont expliqués dans les lignes où apparaît le mot `abstract_methods` (utilisez CTRL + F pour les trouver).
- **La fonction `typecheck_prog`** :
    - **`get_class`** : Recherche et renvoie l'objet de la classe donnée en paramètre dans la liste `p.classes`. Si la classe n'est pas trouvée, elle lève une erreur `Not_found`.
    - **`method_to_string`** : Prend en entrée le nom de la fonction, les types des paramètres et le type de retour. Elle renvoie une chaîne de caractères représentant la signature de la méthode.
    - **`levenshtein_distance`** : Utilisé pour calculer la distance entre deux chaînes de caractères en termes d'insertion, modification et suppression en O(n * m).  
    Il est utilisé dans l'extension de propositions de noms de méthodes, par exemple : "Did you mean `récursion` ?".

    - **`ascendent_fold application o`** : La fonction la plus importante du projet. Elle fonctionne comme `fold_left` sur des listes, mais sur une séquence d'héritage de classes.  
    En donnant un objet de classe `o`, elle applique la fonction `application` à la classe `o` et à chaque super-classe. Elle s'arrête lorsque la fonction `application` renvoie une valeur différente de `None`. Ainsi, elle est plus performante que `fold_left`, car cette fonction peut s'arrêter avant la fin du parcours.

    - **`subtype tho1 tho2`** : Fonction construite à partir de `ascendent_fold`. Si `tho1 = tho2` ou si `tho1` est un sous-type strict de `tho2`, alors `subtype` renvoie `true`.  
    Un tableau est un sous-type d'un autre si les dimensions sont identiques et si le type de base du premier est un sous-type de celui du second.

    - **`type_expr e tenv`**: les cas les plus intéressants sont, `match e with` :
        - **`NullPtr`** : L'expression `NullPtr` représente la constante `null`, qui a le type `TNull`. Le type `TNull` est un sous-type de tous les types de classe, car logiquement la classe vide (l'ensemble vide) est incluse dans toutes les classes.
        - **`Binop(Instanceof, e, Get (Var c))`** : Si `e` est `null`, alors l'expression reste valide, comme en Java.
        - **`This`** : Dès que l'on entre dans la vérification d'une classe `c`, on ajoute dans l'environnement `tenv` une association `'this' -> TClass c`. Si aucune association de `'this'` n'existe dans `tenv`, cela signifie que l'on est en dehors des classes et que le mot-clé `this` ne doit pas être utilisé. Dans ce cas, une erreur est levée.
        - Les `pattern matching` qui se terminent par `when List.exists (fun c_def -> c_def.class_name = c) p.classes` sont utilisés pour détecter les appels aux attributs ou méthodes statiques.
        - **`Array li`** : Un tableau est cohérent si et seulement si tous ses éléments ont le même type. L'idée de l'algorithme est de trouver le plus grand type `tho` qui vérifie tous les éléments du tableau, un peu comme la recherche d'un maximum dans un tableau. Une explication détaillée de l'algorithme dans le typechecker.
    - **`check_visibility`** : Utilisée pour déterminer si l'utilisation d'une entité (attribut ou méthode) est cohérente avec sa visibilité. Elle prend en argument la classe où se trouve l'entité (`target_class`), le nom de l'entité (`entity_name`), sa visibilité, et l'environnement pour chercher le mot-clé `this`, afin de déterminer la classe qui a effectué l'appel.
        - Si la règle de visibilité est `protected` et que la classe de l'entité n'est pas une super-classe de la classe où se trouve `this`, alors une erreur est levée.
        - Si la règle de visibilité est `private` et que la classe de `this` est strictement différente de la classe de l'entité, alors une erreur est levée.
        - Si `this` n'existe pas dans l'environnement (on est dans la méthode `main`), alors si la visibilité est `private` ou `protected`, une erreur est levée.
        - La visibilité `PackageProtected` signifie qu'il n'y a aucune contrainte de visibilité.
    - **`type_method`** : Cette méthode prend en arguments `s` (nom de la méthode), `el` (liste des paramètres) et `o` (définition de la classe). Elle est découpée en trois parties :
        - La première partie concerne la recherche de la méthode. En cas d'erreur, un nom de méthode proche est proposé si une méthode similaire existe (pas plus de 3 (<3) de distance entre la proposition et la saisie).
        - La deuxième partie vérifie la cohérence de l'utilisation de la méthode avec sa visibilité.
        - La troisième partie vérifie la cohérence des arguments effectifs avec les arguments formels.
        - Si la méthode n'est pas trouvée dans la liste des méthodes, on réapplique les mêmes étapes précédentes sur la liste des méthodes statiques. La proposition de correction sera le nom de la méthode statique ou non statique le plus proche de ce qui a été saisi.
    - **`type_mem_access`** :
        - **`Field(e, attribut_name)`** : Pour traiter ce cas de matching, on le découpe en trois parties :
            - On cherche l'attribut dans la classe courante.
            - On vérifie si c'est un attribut final et on s'assure qu'il satisfait les conditions des attributs finals.
            - En réalité, on ne peut pas vérifier tous les cas statiquement. Ainsi, on élimine les cas qui peuvent être traités statiquement, comme l'initialisation ou la modification d'un attribut final en dehors du constructeur.
            - On vérifie la visibilité.
            - Si un de ces points n'est pas vérifié, on refait le même processus pour les classes parentes (en utilisant la fonction `ascendent_fold`).
    - **`check_class`** : L'une des fonctions les plus longues et complexes, elle est découpée en 5 parties :
        - **Étape des initialisations** : À cette étape, on met à jour `pg_state`, en rajoutant la classe courante à la table des classes traitées, et en mettant à jour l'association "this" dans le `tenv`.
        - **Étape de vérification des attributs** : On vérifie la cohérence de chaque attribut avec les expressions d'initialisation qui leur correspondent, s'il y en a (les attributs statiques et non statiques).
        - **Étape de vérification récursive** : On vérifie que la super-classe est cohérente (on note que le séquencement de quelques étapes est très important, plus de détails [ici](#traitement-dincoherences-concernant-labstraction)).
        - **Étape d'ajout des méthodes abstraites de la classe courante à la table des méthodes abstraites trouvées dans `pg_state`** (quand je dis "les méthodes abstraites de la classe courante", je veux dire uniquement cette classe et non celles des super-classes).
        - **Étape de vérification des méthodes non abstraites avec la fonction `check_mdef`** (on note que cette fonction agit sur la table précédente des méthodes abstraites dans le `pg_state`).
        - **Étape de traitement d'incohérences concernant l'abstraction**.
        - On note que le séquencement des étapes est très important puisque la fonction agit sur une variable globale (`pg_state`). L'ordre à garder entre les étapes est : (...appel récursif... -> ...ajout de méthodes abstraites... -> ...vérification des méthodes non abstraites).
        - explications détaillées de l'algorithme se trouves dans le code de la fonction.

    - **`common_verifecation`**: cette méthode est utilisée par les deux méthodes `check_mdef` et `check_s_mdef`, elle consiste à cérifier la cohérence d'une méthode sur certains parties communes entre les méthodes statiques et les méthodes non statiques.
        - plus de détails dans le code de la fonction.

    - **`check_s_mdef`** : On vérifie que la méthode statique n'est pas un constructeur et qu'elle n'utilise pas `this` dans son code. Et bien évidement un appel à comon_verification

    - **`check_mdef`** : Elle se compose de 3 étapes principales :
        - Vérification spéciale pour le constructeur (type de retour `void` et visibilité `PackageProtected`).
        - Appel à `common_verification`.
        - Mise à jour de la table des méthodes abstraites dans `pg_state`, avec une explication détaillée dans le code de la fonction.
    
    - **`close`** : Vérifie qu'une méthode qui a un type de retour différent de `TVoid` est *close*, c'est-à-dire que toutes les branches possibles aboutissent à un appel à `return`. 
    En réalité, ce problème est indécidable, mais il devient décidabilité en restreignant l'ensemble des méthodes à un sous-ensemble plus simple. 
    On exclut même les fonctions de type `if (false) {}` et on les considère comme non close.

## 3. **Interpreter**
  De même, comme pour le typechecker, l'explication suivra le format du code de l'interpréteur.
  Le format du code initial de l'interpréteur est légèrement modifié pour être cohérent avec les résultats attendus. Par exemple, `lenv` est utilisé comme une table de hachage globale, dans laquelle on empile et dépile les arguments et les variables.

  - **Type `value`** : Nous avons ajouté les constructeurs suivants :
    - **`VObj of obj option`** : Représente la valeur `null`. Nous avons ajouté `option` pour permettre de modéliser l'objet `null` comme `VObj None`.
    - **`VArr`** : Représente les tableaux de dimension `n`.
    - **`Null`** : Signifie un espace non initialisé ou l'absence de valeur. Une tentative d'accès en lecture à un champ de type `Null` génère une erreur. Par exemple, dans `new int[5][]`, cette construction génère `[Null; Null; Null; Null; Null]`.
  - **Type `obj`** : Nous avons ajouté le champ **`f_fields`** pour représenter les attributs immuables.
  - **Type `t_cls_env`** : Aka **'type class environment'**. C'est un nouveau type introduit pour traiter l'aspect statique de la classe. Il contient les attributs statiques d'une classe.
  - **`env`, `lenv`, `class_env`** : Les trois environnements utilisés dans l'interpréteur :  
    - **`env`** : L'environnement global, utilisé pour stocker les variables globales.  
    - **`lenv`** : L'environnement local, utilisé lors des appels de méthodes pour stocker les arguments et les variables locales de la méthode appelante. de plus, dans cette environement on stoquer des association de "this" vers des valeurs qui représenteront la valeur de l'objet 'this' (l'objet courant) qui va nous servire par la suite à évaluer l'expression This s'elle existe dans la portion du code à évaluer.
    - **`class_env`** : Utilisé pour manipuler les attributs statiques des classes, considérés comme des variables globales.
  - **`eval_call`** : L'évaluation d'un appel se fait en 4 étapes principales :  
    - **Phase de recherche de la méthode** : Identifier la méthode à appeler en fonction des paramètres et de l'objet.  
    - **Phase d'empilement** : Comme dans la convention d'évaluation d'appels en assembleur, on empile les arguments et les variables locales dans `lenv`. On y ajoute également l'association `'this' -> objet donné en paramètres`, car dans l'évaluation du corps de la méthode, toute utilisation de `'this'` est considérée comme l'utilisation de l'objet passé en paramètre à `eval_call`.  
    - **Phase de traitement du corps de la méthode** : Évaluer le corps de la méthode, ce qui peut générer une exception de type `Return` si une valeur de retour est rencontrée.  
    - **Phase de traitement des valeurs de retour** : Lorsque l'évaluation du corps de la méthode se termine (que ce soit avec une exception `Return` ou sans, dans le cas d'un type `TVoid`), on dépile le
    - **`eval_s_call`**: Exactly like `eval_call`, the only difference is that we search for the method in the list of static methods `o.s_methods`.
    - **`eval`**:
      - In the case of accessing `Field(eo, att)`, we add a check to see if the evaluated object is null. If it is, an execution error is raised: "Trying to access Null pointer value".
      - **Array li**: La création d'un tableau `li` se fait avec la fonction `Array.init` et une référence mutable à la liste, où `f(i) = eval ei`.  
        L'algorithme est expliqué en détail dans les commentaires du code.
    - **get_all_class_s_attributs** : Cette fonction locale est utilisée pour récupérer les tables de hachage des attributs statiques, qu'ils soient finaux ou non finaux, afin de remplir l'environnement des classes (`class_env`) avec ces informations.



done: il faut rajouter la regle if sans le else
il faut revoir l'interpretation au niveau de Set
il faut voir les appels automatiques au super contstructeurs comme dans java
done: unicité de variables
done: si on essaye de modifier deux fois une variable finale dans un constructeur ça ne marchera pas
todo: possibility of calling method/attribut without the keyword this
todo: verify 'this' keyword if it refers the class where we are doing the call
I don't like too much type_method, it is not very efficient
todo: rajou d'une fonction descent_fold, pour les attributs
todo: add NULL value
done: arrays work like in java int[3][]...
done: le sequencement est indéffirencé public, ...
todo: new ne marche pas avec les classes bastraites, continuer check_class
todo: la ligne au dessus est done, il reste a tester