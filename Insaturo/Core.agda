{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — Core
--
-- Una specifica è il CONCETTO INSATURO alla Frege: una firma con un
-- buco. L'implementazione è ciò che lo SATURA. Questo modulo dà alla
-- nozione "spec" un corpo di prima classe — una grammatica — invece di
-- spargere firme e teoremi-a-lato per il codice.
--
-- Tre pezzi, uno per costruttore concettuale:
--
--   Sig       il DOMINIO del buco: cosa un'implementazione deve esibire
--             (l'argomento mancante del concetto fregeano).
--   Law       un OBBLIGO osservabile su un candidato: una proprietà che
--             qualunque saturazione deve rispettare. Osservabile = non
--             guarda *come* l'impl è scritta, solo cosa fa.
--   Conforms  il TESTIMONE di saturazione. Abitare `Conforms s impl` è
--             ciò che significa "impl chiude la spec s".
--
-- Dentro Agda il testimone è una prova. Fuori (un LLM che scrive
-- Haskell/Rust) le stesse `Law` diventano property test / golden vector:
-- la grammatica è una, le chiusure due. Vedi Bridge.agda.
------------------------------------------------------------------------

module Insaturo.Core where

open import Level using (Level; suc)
open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (¬_)

private
  variable
    a b ℓ : Level

------------------------------------------------------------------------
-- Sig — il dominio del buco
--
-- Una firma è insatura: descrive la FORMA di ciò che manca, non lo
-- fornisce. Modelliamo "ciò che manca" come un tipo `Carrier` — il tipo
-- che un'implementazione deve abitare. Per una funzione f : A → B il
-- carrier è (A → B); per una struttura algebrica è il record dei campi.
-- Tenerlo astratto è il punto: la stessa grammatica vale per funzioni,
-- relazioni, strutture.
------------------------------------------------------------------------

record Sig ℓ : Set (suc ℓ) where
  field
    Carrier : Set ℓ          -- il tipo che l'impl deve abitare (il buco)

open Sig public

------------------------------------------------------------------------
-- Law — un obbligo osservabile
--
-- Una legge prende un candidato (un abitante del Carrier) e ne fa una
-- PROPOSIZIONE. Soddisfarla è dare un termine di quel tipo. Le leggi
-- sono il contratto: ciò che resta vero comunque tu scriva l'impl.
--
-- `Holds` è la proposizione; `decide` (opzionale) è ciò che la rende
-- ESEGUIBILE fuori da Agda — un test booleano che riflette la legge.
-- Quando `decide` è presente e `reflects` lega i due, la legge è insieme
-- una prova (dentro) e un property test (fuori). Senza `decide`, la legge
-- vive solo nel regno delle prove (alcune leggi non sono decidibili).
------------------------------------------------------------------------

record Law {ℓ} (C : Set ℓ) : Set (suc ℓ) where
  field
    Holds : C → Set ℓ        -- la proposizione che il candidato deve soddisfare

open Law public

-- Una legge ESEGUIBILE: oltre alla proposizione, un test booleano su un
-- insieme finito di campioni, e la prova che il test riflette la legge.
-- È questo che attraversa il ponte verso Haskell/Rust.
record DecLaw {ℓ} (C : Set ℓ) : Set (suc ℓ) where
  field
    law     : Law C
    Sample  : Set ℓ                       -- spazio dei campioni (input di test)
    check   : C → Sample → Bool           -- il test, su un campione
    -- reflects: se check passa su un campione, la legge "vale lì".
    -- (la forma esatta del legame è scelta dall'autore della legge;
    --  la teniamo come campo per non imporre una sola nozione di reflect)
    Witness : C → Sample → Set ℓ
    reflects : ∀ c s → check c s ≡ true → Witness c s

open DecLaw public

------------------------------------------------------------------------
-- Spec — la grammatica di prima classe
--
-- Una spec impacchetta il buco (`sig`) e la lista delle leggi che ogni
-- saturazione deve rispettare. È un OGGETTO: lo passi, lo componi, lo
-- mappi. Non è più "una firma qua e tre lemmi là".
------------------------------------------------------------------------

record Spec ℓ : Set (suc ℓ) where
  field
    sig  : Sig ℓ
    laws : List (Law (Carrier sig))

open Spec public

------------------------------------------------------------------------
-- Conforms — il testimone di saturazione
--
-- `Conforms s impl` è il tipo "impl chiude la spec s". Un suo abitante è
-- una funzione che, per OGNI legge della spec, ne fornisce la prova su
-- `impl`. È esattamente la saturazione fregeana: dato l'argomento
-- mancante (`impl : Carrier`), il concetto insaturo diventa un oggetto
-- saturo (un termine di tipo `Conforms s impl`).
--
-- Lo definiamo come predicato "tutte le leggi valgono su impl".
------------------------------------------------------------------------

-- Tutte le leggi di una lista valgono su un candidato.
data AllHold {ℓ} {C : Set ℓ} (impl : C) : List (Law C) → Set (suc ℓ) where
  []  : AllHold impl []
  _∷_ : ∀ {l ls}
      → Holds l impl              -- la prova che QUESTA legge vale
      → AllHold impl ls
      → AllHold impl (l ∷ ls)

Conforms : ∀ {ℓ} (s : Spec ℓ) → Carrier (sig s) → Set (suc ℓ)
Conforms s impl = AllHold impl (laws s)

------------------------------------------------------------------------
-- Sat — una saturazione: un'impl INSIEME al suo testimone
--
-- È l'oggetto che vuoi consegnare: non solo "ecco l'impl" ma "ecco
-- l'impl e la prova che chiude la spec". Senza il secondo campo la
-- consegna sarebbe disonesta — e qui non è rappresentabile consegnarla
-- senza prova.
------------------------------------------------------------------------

Sat : ∀ {ℓ} → Spec ℓ → Set (suc ℓ)
Sat s = Σ[ impl ∈ Carrier (sig s) ] Conforms s impl

-- Estrattori
impl-of : ∀ {ℓ} {s : Spec ℓ} → Sat s → Carrier (sig s)
impl-of = proj₁

proof-of : ∀ {ℓ} {s : Spec ℓ} → (sa : Sat s) → Conforms s (impl-of sa)
proof-of = proj₂

------------------------------------------------------------------------
-- Onestà: il RIFIUTO è esprimibile
--
-- Speculare a `Sat`: il tipo "nessuna impl chiude la spec con questo
-- candidato" — la prova di NON-conformità. Una spec onesta deve poter
-- dire "questo candidato NON satura", non solo tacere. Cf. semeion:
-- accanto a `≡ forced arc` c'è `≢ forced arc`.
------------------------------------------------------------------------

Refuses : ∀ {ℓ} (s : Spec ℓ) → Carrier (sig s) → Set (suc ℓ)
Refuses s impl = ¬ (Conforms s impl)
