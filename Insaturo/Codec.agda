{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — Codec
--
-- Wire serializza un campione in una `String`. Ma fra il golden scritto
-- sul filo e il campione su cui `check` gira c'era un salto di FEDE: che
-- la stringa ritorni davvero `s`. Il runner esterno PARSA — e niente
-- garantiva che il parse recuperi proprio quel campione.
--
-- Un `Codec W A` chiude il salto: `enc : A → W`, `dec : W → Maybe A`, e
-- la legge di ROUND-TRIP `dec (enc a) ≡ just a`. Da lì `runnerSound`: il
-- runner che decodifica l'input calcola `check` sul campione INTESO.
--
-- Perché il filo `W` è PARAMETRO e non fissato a `String`? Perché la
-- `String` di Agda è un primitivo OPACO: l'unico legame `String ↔ List
-- Char` (`toList∘fromList`) vive in `Data.String.Unsafe`, provato per
-- `trustMe`. Sotto `--safe` non è disponibile. Quindi un round-trip che
-- attraversa `String` NON è dimostrabile senza trustMe. La conseguenza
-- onesta: il round-trip verificato vive su un filo INDUTTIVO (`List
-- Char`), e il salto finale `List Char → String` resta l'unica fede
-- primitiva — la nominiamo, non la nascondiamo. Per `W = String` con
-- `enc = id` la legge è comunque `refl` (nessun primitivo attraversato).
------------------------------------------------------------------------

module Insaturo.Codec where

open import Data.String using (String; fromList)
open import Data.Char using (Char)
open import Data.Bool using (Bool)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Insaturo.Core
open import Insaturo.Wire using (Encode; encode)

------------------------------------------------------------------------
-- Codec — encode su un filo `W`, decode parziale, legge di round-trip.
-- `dec` è parziale (non ogni `W` è un campione valido); la legge vincola
-- SOLO i `W` nati da `enc`.
------------------------------------------------------------------------

record Codec (W A : Set) : Set where
  field
    enc     : A → W
    dec     : W → Maybe A
    inverse : (a : A) → dec (enc a) ≡ just a       -- dec ∘ enc ≡ just

open Codec public

-- Un codec su `String` è anche un `Encode`: guida `Wire.specJSON`.
codecEncode : {A : Set} → Codec String A → Encode A
codecEncode cdc = record { encode = enc cdc }

------------------------------------------------------------------------
-- Il runner esterno, modellato: legge dal filo, decodifica, e se è un
-- campione valido ci gira il `check` del candidato.
------------------------------------------------------------------------

runnerVerdict : {C W : Set} (d : DecLaw C) → Codec W (Sample d) → C → W → Maybe Bool
runnerVerdict d cdc cand w = map (check d cand) (dec cdc w)

-- ROUND-TRIP come teorema: dato l'input di un campione `s`, il runner
-- calcola ESATTAMENTE `check cand s`. Il parse recupera il campione
-- inteso — non è più fede, è `inverse`.
runnerSound : {C W : Set} (d : DecLaw C) (cdc : Codec W (Sample d)) (cand : C) (s : Sample d)
            → runnerVerdict d cdc cand (enc cdc s) ≡ just (check d cand s)
runnerSound d cdc cand s rewrite inverse cdc s = refl

------------------------------------------------------------------------
-- natCodec — un Codec VERIFICATO per ℕ, su filo induttivo `List Char`.
--
-- Codifica unaria: `n` ↦ `n` barre. La codifica unaria, non decimale, è
-- una scelta di ONESTÀ sul prezzo: il round-trip si dimostra per
-- induzione strutturale, senza i lemmi di div/mod (e senza la ricorsione
-- ben fondata di `show`). Stesso TEOREMA (`inverse`), prova alla portata.
-- Un codec decimale verificato è lo stesso `inverse` con prova più cara.
------------------------------------------------------------------------

bar : Char
bar = '|'

unary : ℕ → List Char
unary n = replicate n bar          -- n copie di '|'

parseBars : List Char → Maybe ℕ
parseBars []         = just zero
parseBars ('|' ∷ cs) = map suc (parseBars cs)
parseBars (_   ∷ _)  = nothing      -- un carattere estraneo: input non valido

parse-unary : (n : ℕ) → parseBars (unary n) ≡ just n
parse-unary zero    = refl
parse-unary (suc n) = cong (map suc) (parse-unary n)

natCodec : Codec (List Char) ℕ
natCodec = record { enc = unary ; dec = parseBars ; inverse = parse-unary }

-- Il salto finale verso il filo-stringa: `List Char → String` è
-- PRIMITIVO (String opaca). Lo isoliamo qui, nominato — è la sola fede
-- che resta, e NON è specifica di ℕ.
renderNat : ℕ → String
renderNat n = fromList (unary n)

------------------------------------------------------------------------
-- Self-check
------------------------------------------------------------------------

private
  open import Data.Bool using (true)
  open import Data.Unit using (⊤; tt)

  -- 1) il Codec identità su String: round-trip per `refl` (niente primitivo).
  idCodec : Codec String String
  idCodec = record { enc = λ s → s ; dec = just ; inverse = λ _ → refl }

  decS : DecLaw String
  decS = record
    { law = record { Holds = λ _ → ⊤ } ; Sample = String
    ; check = λ _ _ → true ; Witness = λ _ _ → ⊤ ; reflects = λ _ _ _ → tt }

  _ : runnerVerdict decS idCodec "cand" (enc idCodec "abc")
    ≡ just (check decS "cand" "abc")
  _ = runnerSound decS idCodec "cand" "abc"

  -- 2) natCodec: il round-trip è una PROVA, non refl su un'identità.
  _ : dec natCodec (enc natCodec 3) ≡ just 3
  _ = inverse natCodec 3
