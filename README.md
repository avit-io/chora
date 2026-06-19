# insaturo

<p align="center">
  <img src="logo.svg" width="160" alt="insaturo — φ( ): l'anello col buco è la spec; il segmento d'oro la satura, ⊢ dice che la chiusura è provata"/>
</p>

> *Una specifica è un concetto col buco. L'implementazione non lo descrive —
> lo chiude. E «chiude» o è un teorema, o non è niente.*

Le **specifiche come concetti insaturi** alla Frege, in Agda — una firma con un
buco (`Sig`), gli obblighi che ogni chiusura deve rispettare (`Law`), e il
testimone che una certa impl chiude davvero il buco (`Conforms`). La grammatica
è **un oggetto di prima classe**: la passi, la componi, la mandi a un LLM. È il
precursore di [semeion](https://github.com/avit-io/semeion) — semeion applica
ai *segnali* la stessa distinzione di regime (emergenza vs fedeltà) che qui sta
nel nudo: una spec e le sue due chiusure.

---

## Il problema che ereditiamo

Una spec, di solito, è **sparsa**: una firma in un file, tre lemmi a lato, una
frase in un README («dev'essere monotòna»), un property test in un altro
linguaggio. Quattro pezzi dello stesso contratto, nessuno dei quali sa degli
altri. La domanda «*e nel caso X?*» non ha una risposta nel tipo: la cerchi
nella prosa, e la prosa è ambigua per costruzione.

Frege aveva il nome esatto per cosa manca. Un concetto è **ungesättigt**,
insaturo: `φ( )` ha un posto vuoto. Non è un oggetto finché un argomento non lo
**satura** — `φ(a)`. Una specifica *è* questo: il posto vuoto è ciò che l'impl
deve esibire; saturarlo è fornirlo, **insieme** alla prova che gli obblighi
reggono.

> insaturo non aggiunge teoremi a lato di una firma. Dà alla nozione «spec» un
> **corpo**: la firma, le leggi e il testimone di chiusura vivono nello stesso
> oggetto, e l'oggetto o typecheck o no.

---

## Come funziona

Tre pezzi, uno per costruttore concettuale (`Insaturo/Core.agda`):

```agda
record Sig ℓ : Set (suc ℓ) where
  field Carrier : Set ℓ        -- il DOMINIO del buco: cosa l'impl deve abitare

record Law (C : Set ℓ) : Set (suc ℓ) where
  field Holds : C → Set ℓ      -- un OBBLIGO osservabile sul candidato

record Spec ℓ : Set (suc ℓ) where
  field sig  : Sig ℓ
        laws : List (Law (Carrier sig))
```

`Carrier` è il buco: per una funzione `f : A → B` è `(A → B)`; per una struttura
algebrica è il record dei campi; per un witness è il tipo della prova. Tenerlo
astratto è il punto — la stessa grammatica vale per funzioni, relazioni,
strutture.

### Chiudere il buco è un teorema

`Conforms s impl` è il tipo «`impl` chiude la spec `s`»: un termine che, per
**ogni** legge, ne fornisce la prova su `impl`. È la saturazione fregeana resa
tipo — dato l'argomento mancante, il concetto insaturo diventa un oggetto saturo.

```agda
Conforms s impl = AllHold impl (laws s)          -- tutte le leggi valgono su impl

Sat s = Σ[ impl ∈ Carrier (sig s) ] Conforms s impl
```

`Sat` è l'oggetto che consegni: non «ecco l'impl» ma «ecco l'impl **e** la prova
che chiude la spec». Senza il secondo campo la consegna sarebbe disonesta — e
qui non è *rappresentabile* consegnarla senza prova.

### Il rifiuto è esprimibile quanto la chiusura

Speculare a `Sat`, il tipo «nessuna impl chiude la spec con questo candidato»:

```agda
Refuses s impl = ¬ (Conforms s impl)
```

Una spec onesta deve poter **dire** «questo candidato NON satura», non solo
tacere. È la risposta tipata alla domanda «e nel caso X?»: X è stato considerato
e respinto, e il respingimento è un teorema (`()`), non una riga di README.
*(È il `≢ forced arc` di semeion, un livello più in basso.)*

### Due chiusure, una grammatica — il ponte (regime 2)

Quando l'impl **non** vive in Agda — un LLM scrive Haskell, Rust, Gleam — la
prova non può essere un termine Agda sull'impl reale. Allora ogni legge
**decidibile** si proietta in un obbligo eseguibile: una batteria di check
booleani su campioni golden (`Insaturo/Bridge.agda`).

```agda
record DecLaw (C : Set ℓ) : Set (suc ℓ) where
  field law      : Law C
        Sample   : Set ℓ
        check    : C → Sample → Bool          -- il test, su un campione
        Witness  : C → Sample → Set ℓ
        reflects : ∀ c s → check c s ≡ true → Witness c s   -- il verde NON è vuoto

passesAll : (es : ExternalSpec ℓ) → ECarrier es → Bool
```

Questo è il **regime di fedeltà** (cf. semeion, regime 2): non una prova
emergente, ma un fatto falsificabile sul mondo. Il property test che fallisce è
il controesempio; il golden vector è il testimone esibito. L'onestà sta nel non
spacciare il secondo regime per il primo:

```
Conforms   (Core)   — PROVA:    la spec emerge.      regime 1
passesAll  (Bridge) — FEDELTÀ:  la spec è testata.   regime 2
```

`Obligation` è un tipo **diverso** da `Conforms`, e il tipo di ritorno è `Bool`,
non `Conforms`. Una pila di green test non è una prova — e il tipo lo dice.
Stessa `Spec` a monte; il tipo del testimone dice quale regime hai in mano.

### L'esempio: il README diventa il file `.agda`

`Insaturo/Example.agda` specifica un bound `n ≤ d` in [0,1] — lo stesso dominio
*ratio* di semeion — e mostra le tre frasi che chiudono ogni ambiguità:

```agda
saturated        : Sat ratioSpec                  -- "esiste un'impl che chiude"      ✓ refl
theBoundConforms : Conforms ratioSpec theBound    -- "QUESTA impl la chiude"          ✓ refl
badRefused       : ¬ (5 ≤ 2)                       -- "QUEST'ALTRA è impossibile"      ✓ ()
```

Tre frasi, tre teoremi. Il README diventa il `.agda`: o typechecka o no. È il
*markdown sotto steroidi* — non ambiguo per costruzione.

---

## La metafora

**insaturo** — *ungesättigt*, l'insaturo di Frege. Un concetto `φ( )` ha un
posto vuoto: non designa un oggetto finché un argomento non lo riempie. È la
distinzione fra *funzione* (insatura, con la lacuna `ξ`) e *oggetto* (saturo,
completo) — il cuore della *Begriffsschrift*.

| insaturo            | specifica / implementazione                       |
|---------------------|---------------------------------------------------|
| il concetto `φ( )`  | `Spec` — la firma col buco e i suoi obblighi       |
| il posto vuoto `ξ`  | `Carrier` — il dominio del buco, l'argomento atteso|
| saturare `φ(a)`     | `Conforms` — chiudere il buco, con la prova        |
| l'oggetto saturo    | `Sat` — impl **e** testimone, consegnati insieme   |
| il posto non chiuso | `Refuses` — nessuna saturazione: e lo si dimostra  |
| la chiusura provata | regime 1 (`Conforms`): emerge in Agda              |
| la chiusura testata | regime 2 (`passesAll`): fedeltà su un'impl esterna |

> *Una spec senza il suo testimone di chiusura è un concetto che finge di essere
> un oggetto.*

---

## Come libreria

```nix
# flake.nix del tuo progetto
inputs.insaturo.url = "github:avit-io/insaturo";
inputs.insaturo.inputs.nixpkgs.follows = "nixpkgs";
```

```
# mio-progetto.agda-lib
name: mio-progetto
include: .
depend: standard-library insaturo
```

### Come sviluppatore di insaturo

```bash
git clone https://github.com/avit-io/insaturo
cd insaturo
agda Insaturo/Core.agda      # --safe --without-K, zero postulate
```

---

## Struttura del progetto

```
insaturo/
├── Insaturo/
│   ├── Core.agda       # Sig · Law · Spec · Conforms · Sat · Refuses (la grammatica)
│   ├── Bridge.agda     # DecLaw · ExternalSpec · passesAll (regime 2: l'impl fuori da Agda)
│   └── Example.agda    # il DSL all'opera: saturazione e rifiuto come teoremi
├── insaturo.agda-lib   # depend: standard-library (radice: zero dep d'ecosistema)
└── flake.nix           # packages.lib · lib.mkShell · devShells.default
```

---

## Relazione con l'ecosistema

insaturo è la **macchina nuda**: spec, conformità, rifiuto, e i due regimi di
chiusura. Non parla di nessun dominio. [semeion](https://github.com/avit-io/semeion)
è la stessa distinzione **incarnata** sui segnali SRE: lì `Conforms`/`Refuses`
diventano `forced`/`¬ forced` su un `Display`, e il regime 2 diventa la fedeltà
a un fatto di Grafana. insaturo viene prima nel significato; semeion gli dà un
mondo.

```
        insaturo  ← la grammatica delle spec (Sig · Law · Conforms)
           │         regime 1 = prova · regime 2 = fedeltà
           ▼
        semeion   ← la stessa distinzione, incarnata sui segnali
```

Ordine di dipendenza: entrambe sono **radici** (`depend: standard-library`).
insaturo non importa semeion né viceversa — la parentela è concettuale, non un
`import`.

---

## Garanzie strutturali

- **chiusura non asseribile** — `Sat s` esige `Conforms s impl`: non puoi
  consegnare un'impl senza la prova che chiude la spec. La disonestà non è
  rappresentabile.
- **rifiuto di prima classe** — `Refuses s impl` è un tipo abitabile: «X non
  satura» è un teorema (`()`), non un silenzio. La domanda «e nel caso X?» ha
  una risposta nel tipo.
- **due regimi, due tipi** — `Conforms` (prova) e `passesAll` (`Bool`, fedeltà)
  sono tipi diversi a monte della stessa `Spec`. Un verde di test non si
  traveste da prova: `reflects` garantisce che il verde **porta** un testimone,
  ma solo sui campioni testati — fedeltà, non emergenza.
- **grammatica polimorfa** — `Carrier` è un `Set` qualunque: la stessa `Spec`
  vale per funzioni, relazioni, strutture. Nessun mapping cablato a un dominio.

`--safe --without-K`, zero `postulate`, zero `TERMINATING`, zero `trustMe`.

### Cosa NON è garantito (onestà sopra tutto)

- **il legame law↔decide è scelto dall'autore** — `DecLaw` tiene `Witness` e
  `reflects` come campi: insaturo non impone *una* nozione di «il test riflette
  la legge», la lascia a chi scrive la legge. È flessibilità voluta, ma è fede
  riposta nell'autore della `DecLaw`.
- **`AllHold` è puntuale, non quantificato** — `Conforms` prova le leggi su *un*
  candidato dato, non «per ogni impl». È così che dev'essere (saturazione di un
  argomento), ma non è una prova di universalità.

---

## Roadmap

In ordine di valore:

1. **Composizione di spec** — `Spec → Spec → Spec`: unione delle leggi,
   prodotto dei buchi. Una spec che si compone è ciò che rende la grammatica
   davvero di prima classe (oggi `laws` è una lista, ma non c'è ancora l'algebra).
2. **Il ponte serializzabile sul serio** — `ExternalSpec` è «concettualmente
   serializzabile»; renderlo *davvero* JSON (leggi + golden vector) è ciò che lo
   manda a un LLM come contratto verificabile, chiudendo il giro Agda→Haskell.

---

## Licenza

MIT — il concetto è libero, la chiusura è forzata.

---

> *«Prima di dire che un'impl è corretta, chiediti quale buco chiude — e se la
> chiusura è una prova, o la stai solo asserendo.»*
