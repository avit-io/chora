{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — Example
--
-- Il DSL all'opera. Specifichiamo una funzione di clamp in [0,1] su
-- razionali good/total — lo stesso dominio "ratio" di semeion — e
-- mostriamo le due cose che rendono una spec NON ambigua:
--
--   1. la SATURAZIONE è un teorema: `refl` testimonia che una certa
--      impl chiude la spec. La frase "questa impl è corretta" non è
--      prosa, è typecheck.
--   2. il RIFIUTO è un teorema: `()` testimonia che un candidato
--      sbagliato NON satura. La frase "quest'altra impl è scorretta"
--      è anch'essa typecheck — ed è ciò che chiude l'ambiguità di un
--      README ("e nel caso X?" → X è stato considerato e respinto).
------------------------------------------------------------------------

module Insaturo.Example where

open import Level using (0ℓ)
open import Data.Nat using (ℕ; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)

open import Insaturo.Core

------------------------------------------------------------------------
-- Il buco: un Ratio testimoniato (num ≤ den), come in semeion.
-- L'impl che cerchiamo è la PROVA che il numeratore è limitato dal
-- denominatore — il witness `num ≤ den`. Qui il "Carrier" è quella prova.
------------------------------------------------------------------------

record Ratio : Set where
  field
    num den : ℕ
    bound   : num ≤ den          -- 0 ≤ valore ≤ 1, DIMOSTRATO

open Ratio

-- La spec parla di UN ratio fissato (good/total) e chiede: il candidato
-- è un bound valido? Il Carrier è quindi il tipo del witness per quel
-- ratio. Scegliamo num=2, den=5 come ratio d'esempio (2/5 ∈ [0,1]).

theNum theDen : ℕ
theNum = 2
theDen = 5

-- Carrier = "una prova che 2 ≤ 5". Saturare = fornirla.
BoundCarrier : Set
BoundCarrier = theNum ≤ theDen

-- L'unica legge: il bound deve essere... il bound. (Banale qui di
-- proposito — l'esempio mostra la MECCANICA, non una legge profonda.)
boundLaw : Law BoundCarrier
boundLaw = record { Holds = λ p → p ≡ p }      -- riflessività: ogni prova vale

ratioSig : Sig 0ℓ
ratioSig = record { Carrier = BoundCarrier }

ratioSpec : Spec 0ℓ
ratioSpec = record { sig = ratioSig ; laws = boundLaw ∷ [] }

------------------------------------------------------------------------
-- 1. SATURAZIONE INTERNA — la prova chiude il buco
--
-- Il witness 2 ≤ 5 è `s≤s (s≤s z≤n)`. Lo consegniamo INSIEME alla prova
-- che chiude la spec. La conformità è `refl` (la legge era p ≡ p).
------------------------------------------------------------------------

theBound : BoundCarrier
theBound = s≤s (s≤s z≤n)          -- 2 ≤ 5

saturated : Sat ratioSpec
saturated = theBound , (refl ∷ [])
--                      ^^^^ "boundLaw vale su theBound" — un TEOREMA, non prosa.

-- La stessa frase, isolata, come lemma leggibile:
theBoundConforms : Conforms ratioSpec theBound
theBoundConforms = refl ∷ []

------------------------------------------------------------------------
-- 2. RIFIUTO — l'onestà è nel tipo
--
-- Cambiamo legge: una che NESSUN candidato di questo tipo può
-- soddisfare, e mostriamo che il rifiuto è dimostrabile. Prendiamo la
-- legge "il candidato prova 5 ≤ 2" — falsa, perché 5 ≤ 2 è disabitato.
------------------------------------------------------------------------

-- Una spec impossibile: chiede un witness di 5 ≤ 2.
BadCarrier : Set
BadCarrier = (5 ≤ 2)

-- 5 ≤ 2 non ha abitanti: il rifiuto è un teorema per assenza di casi.
fiveNotLeqTwo : ¬ (5 ≤ 2)
fiveNotLeqTwo (s≤s (s≤s ()))

-- "Nessuna impl satura BadCarrier" — la versione `Refuses`, leggibile
-- come la frase «semeion RIFIUTA la gauge» di semeion.
badRefused : ¬ BadCarrier
badRefused = fiveNotLeqTwo

------------------------------------------------------------------------
-- Lettura per un'IA / un umano:
--
--   saturated         : "esiste un'impl che chiude ratioSpec"      ✓ refl
--   theBoundConforms  : "QUESTA impl la chiude"                     ✓ refl
--   badRefused        : "QUEST'ALTRA cosa è impossibile da saturare" ✓ ()
--
-- Tre frasi, tre teoremi. Il README diventa il file .agda: o typechecka
-- o no. È il "markdown sotto steroidi" — non ambiguo per costruzione.
------------------------------------------------------------------------
