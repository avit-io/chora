{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — Bridge
--
-- La stessa grammatica, l'altra chiusura. Quando l'implementazione NON
-- vive in Agda — un LLM scrive Haskell, Rust, Gleam — la spec resta il
-- contratto, ma la prova non può essere un termine Agda sull'impl reale.
-- La soluzione: ogni legge DECIDIBILE si proietta in un OBBLIGO
-- eseguibile (una batteria di check booleani su campioni). L'impl
-- esterna è conforme sse, e nella misura in cui, passa gli obblighi.
--
-- Questo è il regime di FEDELTÀ (cf. semeion regime 2): non una prova
-- emergente, ma un fatto falsificabile sul mondo. Il property test che
-- fallisce è il controesempio; il golden vector è il testimone esibito.
--
-- L'onestà sta nel non spacciare il secondo per il primo: `Obligation`
-- è un tipo DIVERSO da `Conforms`. Una pila di green test non è una
-- prova — e il tipo lo dice.
------------------------------------------------------------------------

module Insaturo.Bridge where

open import Level using (Level; suc)
open import Data.List using (List; []; _∷_)
open import Data.Bool using (Bool; true; _∧_)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Insaturo.Core

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Obligation — la forma eseguibile di una legge
--
-- Una legge decidibile, applicata a un candidato e a una LISTA di
-- campioni, produce un verdetto booleano: "tutti i campioni passano".
-- Questo è ciò che si esporta verso un test runner esterno.
------------------------------------------------------------------------

-- Esegui il check di una DecLaw su un candidato per tutti i campioni dati.
runDecLaw : ∀ {C : Set ℓ} → (d : DecLaw C) → C → List (Sample d) → Bool
runDecLaw d c []        = true
runDecLaw d c (s ∷ ss)  = check d c s ∧ runDecLaw d c ss

-- Verdetto: "il candidato passa la legge su questo set di campioni".
-- È un Bool — esattamente ciò che un runner Haskell/Rust riporta.
Passes : ∀ {C : Set ℓ} → (d : DecLaw C) → C → List (Sample d) → Bool
Passes = runDecLaw

------------------------------------------------------------------------
-- ExternalSpec — una spec proiettata per il consumo esterno
--
-- Le leggi decidibili più, per ciascuna, un set di campioni golden.
-- Questo oggetto è SERIALIZZABILE concettualmente: è ciò che mandi a un
-- LLM come "ecco il contratto e i vettori su cui ti verifico".
------------------------------------------------------------------------

record ExternalSpec ℓ : Set (suc ℓ) where
  field
    ECarrier : Set ℓ
    obligations : List (Σ[ d ∈ DecLaw ECarrier ] List (Sample d))

open ExternalSpec public

-- Un candidato esterno (idealmente: il comportamento osservato dell'impl
-- Haskell, reificato in Agda come funzione) passa una ExternalSpec se
-- passa OGNI obbligo sui suoi campioni.
passesAll : ∀ {ℓ} (es : ExternalSpec ℓ) → ECarrier es → Bool
passesAll es c = go (obligations es)
  where
    go : List (Σ[ d ∈ DecLaw (ECarrier es) ] List (Sample d)) → Bool
    go []             = true
    go ((d , ss) ∷ o) = runDecLaw d c ss ∧ go o

------------------------------------------------------------------------
-- Il legame onesto interno↔esterno
--
-- `reflects` (in DecLaw) garantisce: se il check passa su un campione,
-- allora il `Witness` di quel campione è abitato. Quindi un verdetto
-- verde NON è vuoto — porta con sé un testimone per ogni campione. Ma
-- copre solo i campioni TESTATI: è fedeltà, non emergenza. Il tipo di
-- ritorno `Bool` (non `Conforms`) tiene questa distinzione visibile.
--
-- Lemma di onestà: passare tutti i campioni dà i testimoni per tutti i
-- campioni — niente di più, niente di meno. (Schema; l'autore della
-- DecLaw lo specializza alla sua `Witness`.)
------------------------------------------------------------------------

-- Da un singolo check verde al testimone di quel campione.
greenWitness : ∀ {C : Set ℓ} → (d : DecLaw C) → (c : C) → (s : Sample d)
             → check d c s ≡ true → Witness d c s
greenWitness d c s eq = reflects d c s eq

------------------------------------------------------------------------
-- Riepilogo del ponte:
--
--   Conforms      (Core)   — PROVA: la spec emerge, regime 1.
--   passesAll     (Bridge) — FEDELTÀ: la spec è testata, regime 2.
--
-- Un'impl Agda consegna `Sat` (impl + Conforms).
-- Un'impl LLM-in-Haskell consegna un comportamento + `passesAll ≡ true`.
-- Stessa `Spec` a monte; il tipo del testimone dice quale regime hai.
------------------------------------------------------------------------
