# CLAUDE.md — insaturo

## Cos'è questo progetto

insaturo è una libreria **Agda** (tipi dipendenti, `--safe --without-K`) che dà
alla nozione **«specifica»** un corpo di prima classe. Una spec è un **concetto
insaturo** alla Frege: `φ( )`, una firma con un buco. L'implementazione non la
descrive — la **satura**, chiudendo il buco, e «chiude» o è un teorema o non è
niente.

insaturo è una **radice** dell'ecosistema: `depend: standard-library` e basta —
la grammatica nuda delle spec. È il **precursore concettuale** di semeion:
semeion applica ai *segnali* SRE la stessa distinzione di regime (emergenza vs
fedeltà) che qui sta allo stato puro. insaturo non importa semeion né viceversa
— la parentela è nel significato, non in un `import`.

Se per «far valere» una spec sei tentato di scrivere la firma in un file e i
teoremi in un altro e una frase nel README, **ti stai sbagliando**. Quello
sparpagliamento è l'antipattern che questo file esiste per vietare: la spec è
**un oggetto** (`Spec`), con dentro firma, leggi e testimone di chiusura.

## La grammatica — tre pezzi, uno per costruttore concettuale

`Insaturo/Core.agda`:

1. **`Sig`** — il *dominio* del buco: `Carrier`, il tipo che l'impl deve abitare
   (l'argomento mancante del concetto fregeano). Astratto di proposito: vale per
   funzioni, relazioni, strutture.
2. **`Law`** — un *obbligo osservabile* su un candidato: `Holds : C → Set`. Non
   guarda *come* l'impl è scritta, solo cosa fa.
3. **`Conforms`** — il *testimone di saturazione*: per **ogni** legge, la prova
   su `impl`. Abitare `Conforms s impl` è ciò che significa «impl chiude s».

E i due tipi che tengono onesta la consegna:

- **`Sat s = Σ impl (Conforms s impl)`** — impl **e** prova insieme. Senza il
  secondo campo la consegna sarebbe disonesta, e qui non è *rappresentabile*.
- **`Refuses s impl = ¬ (Conforms s impl)`** — «X non satura» è un teorema
  (`()`), non un silenzio. La risposta tipata a «e nel caso X?».

## I due regimi — distinguili sempre

La stessa `Spec` ha **due** chiusure, e vanno tenute separate (è la lezione che
semeion eredita):

1. **regime 1 — prova** (`Conforms`, in `Core`): l'impl vive in Agda, la
   chiusura *emerge* come termine. `refl`/costruzione.
2. **regime 2 — fedeltà** (`passesAll`, in `Bridge`): l'impl vive **fuori** (un
   LLM scrive Haskell/Rust/Gleam). La legge decidibile (`DecLaw`) si proietta in
   una batteria di check booleani su campioni golden. Verdetto `Bool`,
   **falsificabile**: il test rosso è il controesempio, il golden vector il
   testimone esibito.

`Conforms` (regime 1) e `passesAll`/`Bool` (regime 2) sono **tipi diversi** a
monte della stessa `Spec`. Una pila di green test **non** è una prova, e il tipo
lo dice: `reflects` garantisce che il verde *porta* un testimone, ma solo sui
campioni testati — fedeltà, non emergenza. **Non spacciare il regime 2 per il
regime 1.** Se chiudi solo con i test, *dillo*.

## Regola fondamentale: proof-driven

Il flusso corretto:

1. definisci la **spec** (`Sig` + `laws`);
2. enuncia il **testimone** — quale impl la chiude, o quale candidato è respinto;
3. **dimostralo** in Agda (`Conforms`/`Refuses`), oppure, per un'impl esterna,
   proietta le leggi decidibili e verifica (`passesAll`).

**Niente `postulate`, niente `{-# TERMINATING #-}`, niente `trustMe`** per
zittire il checker. Se la prova è scomoda, la prova è il punto.

## L'onestà è nel tipo

La disonestà non deve essere *rappresentabile*:

- non puoi consegnare un'impl senza la sua prova: `Sat` esige `Conforms`;
- non puoi *tacere* su un candidato sbagliato: `Refuses` lo nomina come teorema;
- non puoi far passare un green-test per prova: `passesAll` ritorna `Bool`, non
  `Conforms`, e copre solo i campioni testati.

Se una spec **non** è chiudibile da una classe di impl, **dillo**: è un
risultato (`Refuses`), non un fallimento da mascherare.

## Estensione conservativa

- i teoremi già dimostrati **restano veri** dopo l'estensione (nessun assioma
  aggiunto per comodità);
- un'estensione **aggiunge** costruttori/leggi — mai indebolisce un obbligo
  esistente per far passare un caso;
- se un caso richiede di violare la disciplina (consegnare un'impl senza
  testimone, marcare conforme ciò che non lo è), **fermati**: o la codifica va
  riformulata, o la richiesta è mal posta.

**Il README non resta a penzoloni.** Ogni estensione che cambia tipi o regimi
aggiorna `README.md` (la sezione del tipo, le "Garanzie", "Cosa NON è
garantito", la "Roadmap") **nello stesso commit** — un elemento di roadmap
chiuso si sposta. Lo stesso per i commenti-doc dei moduli toccati.

## Cosa consegnare

Il **sorgente `.agda`** — i tipi e le loro prove — non l'output. La cosa che si
reviewa è la prova. Ogni modulo deve typeckeckare `--safe --without-K`, **zero
`postulate`/`TERMINATING`/`trustMe`**.

Se non riesci a dimostrare che un'impl chiude una spec: **dimmi dove ti blocchi**.
O c'è un buco nella codifica (prezioso, lo chiudiamo), o quell'impl davvero non
satura (e allora è `Refuses`, o è regime 2 — si nomina, non si aggira).

## Struttura

```
Insaturo/
├── Core.agda      # Sig · Law · Spec · Conforms · Sat · Refuses (la grammatica)
├── Bridge.agda    # DecLaw · ExternalSpec · passesAll (regime 2: l'impl fuori da Agda)
├── Wire.agda      # Encode · WireLaw · specJSON (contratto JSON) · toExternal · wireWitness
├── Compose.agda   # _×ˢ_ (prodotto dei buchi) · _∧+_ (rafforzamento) + i teoremi conformità⇔pezzi
└── Example.agda   # il DSL all'opera: saturazione (refl) e rifiuto (()) come teoremi
```

## Toolchain

Agda 2.8 via piforge, flake nix, `nix develop` (solo stdlib in scope — insaturo
è una radice). Typecheck: `agda Insaturo/Core.agda`, `… Bridge.agda`,
`… Wire.agda`, `… Compose.agda`, `… Example.agda`.
