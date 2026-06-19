{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — Wire
--
-- Il ponte (Bridge) dice COME una spec si verifica fuori da Agda: le
-- leggi decidibili, i campioni, il verdotto Bool. Ma `ExternalSpec` era
-- «concettualmente serializzabile» — un oggetto Agda con dentro `Set` e
-- funzioni, niente che esca davvero sul filo.
--
-- Wire lo rende JSON SUL SERIO. Per ogni legge: un nome, un encoder dei
-- campioni, e una tabella di GOLDEN VECTOR — coppie (campione, atteso),
-- dove l'atteso è `check ref` calcolato da un'impl di RIFERIMENTO, non
-- inventato. `specJSON` produce una `String`: il contratto che mandi a
-- un LLM.
--
-- Restano due cose oneste:
--   • il verdetto resta `Bool` (via Bridge.passesAll su `toExternal`):
--     una pila di golden verdi è FEDELTÀ, non `Conforms`. Il tipo non
--     mente sul regime.
--   • `wireWitness`: un golden verde riprodotto dal candidato PORTA il
--     `Witness` di quel campione — ma solo dei campioni in tabella.
--     Niente di più, niente di meno.
------------------------------------------------------------------------

module Insaturo.Wire where

open import Level using (0ℓ)
open import Data.String using (String; _++_)
open import Data.Bool using (Bool; true; false)
open import Data.Bool.Show renaming (show to showBool)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All)
open import Data.Product using (_,_; Σ-syntax)
open import Relation.Binary.PropositionalEquality using (_≡_; trans)

open import Insaturo.Core
open import Insaturo.Bridge

------------------------------------------------------------------------
-- Encode — ciò che rende un campione una String. È la sola cosa che
-- mancava perché un obbligo «uscisse»: senza un modo di scrivere il
-- campione, non c'è JSON.
------------------------------------------------------------------------

record Encode (A : Set) : Set where
  field encode : A → String

open Encode public

------------------------------------------------------------------------
-- WireLaw — un obbligo di Bridge, DECORATO per la serializzazione:
-- la legge decidibile più nome, encoder dei campioni e i campioni. È un
-- elemento di un `ExternalSpec` reso scrivibile sul filo.
------------------------------------------------------------------------

record WireLaw (C : Set) : Set₁ where
  field
    name    : String
    dlaw    : DecLaw C
    encS    : Encode (Sample dlaw)
    samples : List (Sample dlaw)

open WireLaw public

WireSpec : Set → Set₁
WireSpec C = List (WireLaw C)

------------------------------------------------------------------------
-- Rendering JSON — il contratto come String
--
-- Una piccola join per non dipendere da come la stdlib chiama la sua
-- (lazy: tre righe e nessun import da indovinare).
------------------------------------------------------------------------

join : String → List String → String
join sep []           = ""
join sep (x ∷ [])     = x
join sep (x ∷ y ∷ xs) = x ++ sep ++ join sep (y ∷ xs)

-- Un golden vector: (campione serializzato, atteso = check del RIFERIMENTO).
-- L'atteso non è asserito: è calcolato da `ref`. Un campione che il
-- riferimento stesso fallisce esce `out:false`, e il contratto lo mostra.
goldenRow : {C : Set} → (w : WireLaw C) → C → Sample (dlaw w) → String
goldenRow w ref s =
  "{\"in\":\"" ++ encode (encS w) s ++ "\",\"out\":" ++ showBool (check (dlaw w) ref s) ++ "}"

lawJSON : {C : Set} → (w : WireLaw C) → C → String
lawJSON w ref =
  "{\"law\":\"" ++ name w ++ "\",\"golden\":[" ++
  join "," (map (goldenRow w ref) (samples w)) ++ "]}"

-- Il contratto intero, dato un riferimento: ciò che mandi a un LLM.
specJSON : (C : Set) → C → WireSpec C → String
specJSON C ref ws = "[" ++ join "," (map (λ w → lawJSON w ref) ws) ++ "]"

------------------------------------------------------------------------
-- Il verdetto resta in Bridge — Wire non ne inventa uno nuovo
--
-- Una WireSpec, dimenticati nome/encoder, È un ExternalSpec: la verifica
-- è la stessa `passesAll` (Bool). La serializzazione aggiunge SOLO come
-- scrivere il contratto, non un nuovo modo di accettarlo.
------------------------------------------------------------------------

toExternal : (C : Set) → WireSpec C → ExternalSpec 0ℓ
toExternal C ws = record
  { ECarrier    = C
  ; obligations = map (λ w → dlaw w , samples w) ws
  }

-- Il verdetto serializzabile È quello di Bridge.
passesWire : (C : Set) → WireSpec C → C → Bool
passesWire C ws cand = passesAll (toExternal C ws) cand

------------------------------------------------------------------------
-- L'onestà attraversa il filo — `wireWitness`
--
-- Un candidato esterno «riproduce» un golden se dà lo stesso verdetto
-- del riferimento su quel campione. Se l'atteso è verde e il candidato
-- lo riproduce, `reflects` consegna il `Witness` per il candidato — ma
-- solo su quel campione. È `greenWitness` di Bridge, ora sul golden
-- vettore serializzato: fedeltà, non emergenza.
------------------------------------------------------------------------

-- Il candidato riproduce ogni verdetto del riferimento sui campioni.
ReproducesGolden : {C : Set} → (w : WireLaw C) → (ref cand : C) → Set
ReproducesGolden w ref cand =
  All (λ s → check (dlaw w) cand s ≡ check (dlaw w) ref s) (samples w)

wireWitness : {C : Set} (w : WireLaw C) (ref cand : C) (s : Sample (dlaw w))
            → check (dlaw w) ref  s ≡ true                       -- l'atteso golden è verde
            → check (dlaw w) cand s ≡ check (dlaw w) ref s        -- il candidato lo riproduce
            → Witness (dlaw w) cand s
wireWitness w ref cand s eRef eMatch = reflects (dlaw w) cand s (trans eMatch eRef)

------------------------------------------------------------------------
-- Self-check: il rendering produce ESATTAMENTE quel JSON (refl = il test)
------------------------------------------------------------------------

private
  open import Data.Nat using (ℕ; _≡ᵇ_)
  open import Data.Nat.Show renaming (show to showℕ)
  open import Data.Unit using (⊤; tt)
  open import Relation.Binary.PropositionalEquality using (refl)

  -- una DecLaw concreta: «il candidato vale come il campione» (c ≡ᵇ s).
  -- Witness banale: il self-check prova il PONTE (rendering + plumbing),
  -- non una legge profonda.
  decEq : DecLaw ℕ
  decEq = record
    { law      = record { Holds = λ _ → ⊤ }
    ; Sample   = ℕ
    ; check    = λ c s → c ≡ᵇ s
    ; Witness  = λ _ _ → ⊤
    ; reflects = λ _ _ _ → tt
    }

  wlaw : WireLaw ℕ
  wlaw = record
    { name    = "eqRef"
    ; dlaw    = decEq
    ; encS    = record { encode = showℕ }
    ; samples = 1 ∷ 2 ∷ []
    }

  -- riferimento = 1: check 1 1 = true, check 1 2 = false. Il JSON lo dice.
  _ : specJSON ℕ 1 (wlaw ∷ [])
    ≡ "[{\"law\":\"eqRef\",\"golden\":[{\"in\":\"1\",\"out\":true},{\"in\":\"2\",\"out\":false}]}]"
  _ = refl
