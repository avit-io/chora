{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — Codec
--
-- Wire serializza un campione con un `Encode` (A → String). Ma fra il
-- golden scritto sul filo e il campione su cui `check` gira, c'era un
-- salto di FEDE: che la stringa "2/5" ritorni davvero `s`. Il runner
-- esterno PARSA la stringa — e niente garantiva che il parse recuperi
-- proprio quel campione.
--
-- Un `Codec` chiude il salto: encode più un `decode : String → Maybe A`
-- e la legge di ROUND-TRIP `decode (encode a) ≡ just a`. Da lì il
-- teorema `runnerSound`: il runner che decodifica l'input serializzato
-- calcola il `check` sul campione INTESO — non su uno ricostruito a
-- caso. L'encoder esce dalla lista «cosa NON è garantito»: resta solo
-- l'obbligo di FORNIRE un Codec la cui legge regge (per ℚ/ℕ è un parser
-- verificato — vedi roadmap).
------------------------------------------------------------------------

module Insaturo.Codec where

open import Data.String using (String)
open import Data.Bool using (Bool)
open import Data.Maybe using (Maybe; just; map)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Insaturo.Core
open import Insaturo.Wire

------------------------------------------------------------------------
-- Codec — un Encode con l'inverso parziale e la legge di round-trip.
-- `decode` è parziale (non ogni stringa è un campione valido); la legge
-- vincola SOLO le stringhe nate da `encode`.
------------------------------------------------------------------------

record Codec (A : Set) : Set where
  field
    enc     : Encode A
    decode  : String → Maybe A
    inverse : (a : A) → decode (encode enc a) ≡ just a    -- decode ∘ encode ≡ just

open Codec public

-- Un Codec è anche un Encode: guida `Wire.specJSON` come prima.
codecEncode : {A : Set} → Codec A → Encode A
codecEncode = enc

------------------------------------------------------------------------
-- Il runner esterno, modellato: legge la stringa, la decodifica, e se è
-- un campione valido ci gira il `check` del candidato.
------------------------------------------------------------------------

runnerVerdict : {C : Set} (d : DecLaw C) → Codec (Sample d) → C → String → Maybe Bool
runnerVerdict d cdc cand str = map (check d cand) (decode cdc str)

-- ROUND-TRIP come teorema: dato l'input serializzato di un campione `s`,
-- il runner calcola ESATTAMENTE `check cand s`. Il parse recupera il
-- campione inteso — non è più fede, è `inverse`.
runnerSound : {C : Set} (d : DecLaw C) (cdc : Codec (Sample d)) (cand : C) (s : Sample d)
            → runnerVerdict d cdc cand (encode (enc cdc) s) ≡ just (check d cand s)
runnerSound d cdc cand s rewrite inverse cdc s = refl

------------------------------------------------------------------------
-- Self-check: il round-trip all'opera (il Codec identità su String —
-- l'inverso è `refl`; un Codec verificato per ℕ/ℚ è la roadmap).
------------------------------------------------------------------------

private
  open import Data.Bool using (true)
  open import Data.Unit using (⊤; tt)

  idCodec : Codec String
  idCodec = record
    { enc     = record { encode = λ s → s }
    ; decode  = just
    ; inverse = λ _ → refl
    }

  -- una DecLaw banale su String (il punto è il round-trip, non la legge).
  decS : DecLaw String
  decS = record
    { law      = record { Holds = λ _ → ⊤ }
    ; Sample   = String
    ; check    = λ _ _ → true
    ; Witness  = λ _ _ → ⊤
    ; reflects = λ _ _ _ → tt
    }

  -- il runner, riparsando l'input serializzato, dà il check sul campione inteso.
  _ : runnerVerdict decS idCodec "cand" (encode (enc idCodec) "abc")
    ≡ just (check decS "cand" "abc")
  _ = runnerSound decS idCodec "cand" "abc"
