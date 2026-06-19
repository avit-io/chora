{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — CodecNat
--
-- Un `Codec` DECIMALE verificato per ℕ, sul filo induttivo `List Char`
-- (vedi Codec.agda sul perché non `String`). A differenza dell'unario di
-- Codec.agda, qui il filo è leggibile: `305` ↦ "305".
--
-- Tre strati, ciascuno col suo round-trip:
--   1. cifra ↔ carattere   (`Fin 10 ↔ Char`, bijezione finita)
--   2. lista di cifre ↔ caratteri
--   3. numero ↔ cifre       (decimale, con i lemmi div/mod)
-- e la `inverse` finale li compone, con `reverse` (LSB→MSB) che si
-- cancella per involuzione.
--
-- La ricorsione di `toDigits` è su un CARBURANTE (`fuel`) — non su `n/10`
-- — così è strutturale sotto `--safe` (niente ricorsione ben fondata,
-- niente {-# TERMINATING #-}). `fuel = n` basta sempre: ogni passo `n`
-- cala di ≥1, quindi 0 si raggiunge in ≤ n passi.
------------------------------------------------------------------------

module Insaturo.CodecNat where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; z≤n; s≤s; _/_; _%_; _+_; _*_)
open import Data.Nat.DivMod using (_mod_; m%n<n; m≡m%n+[m/n]*n; m/n<m)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-pred; *-comm)
open import Data.Fin using (Fin; toℕ)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F; 4F; 5F; 6F; 7F; 8F; 9F)
open import Data.Fin.Properties using (toℕ-fromℕ<)
open import Data.Char using (Char)
open import Data.List using (List; []; _∷_; map; reverse)
open import Data.List.Properties using (reverse-involutive)
open import Data.Maybe using (Maybe; just; nothing; _>>=_)
open import Relation.Binary.PropositionalEquality
  using (_≡_; refl; cong; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Insaturo.Codec using (Codec)

------------------------------------------------------------------------
-- Strato 1: cifra ↔ carattere — bijezione finita su Fin 10
------------------------------------------------------------------------

toChar : Fin 10 → Char
toChar 0F = '0'
toChar 1F = '1'
toChar 2F = '2'
toChar 3F = '3'
toChar 4F = '4'
toChar 5F = '5'
toChar 6F = '6'
toChar 7F = '7'
toChar 8F = '8'
toChar 9F = '9'

charDig : Char → Maybe (Fin 10)
charDig '0' = just 0F
charDig '1' = just 1F
charDig '2' = just 2F
charDig '3' = just 3F
charDig '4' = just 4F
charDig '5' = just 5F
charDig '6' = just 6F
charDig '7' = just 7F
charDig '8' = just 8F
charDig '9' = just 9F
charDig _   = nothing

charDig-toChar : (d : Fin 10) → charDig (toChar d) ≡ just d
charDig-toChar 0F = refl
charDig-toChar 1F = refl
charDig-toChar 2F = refl
charDig-toChar 3F = refl
charDig-toChar 4F = refl
charDig-toChar 5F = refl
charDig-toChar 6F = refl
charDig-toChar 7F = refl
charDig-toChar 8F = refl
charDig-toChar 9F = refl

------------------------------------------------------------------------
-- Strato 2: lista di cifre ↔ caratteri
------------------------------------------------------------------------

digitsToChars : List (Fin 10) → List Char
digitsToChars = map toChar

charsToDigits : List Char → Maybe (List (Fin 10))
charsToDigits []       = just []
charsToDigits (c ∷ cs) = charDig c >>= λ d → charsToDigits cs >>= λ ds → just (d ∷ ds)

charsToDigits-inv : (ds : List (Fin 10)) → charsToDigits (digitsToChars ds) ≡ just ds
charsToDigits-inv []       = refl
charsToDigits-inv (d ∷ ds) rewrite charDig-toChar d | charsToDigits-inv ds = refl

------------------------------------------------------------------------
-- Strato 3: numero ↔ cifre (LSB-first), decimale
------------------------------------------------------------------------

fromDigits : List (Fin 10) → ℕ
fromDigits []       = 0
fromDigits (d ∷ ds) = toℕ d + 10 * fromDigits ds

toDigits : (fuel n : ℕ) → List (Fin 10)
toDigits zero    _       = []
toDigits (suc f) zero    = []
toDigits (suc f) (suc m) = (suc m mod 10) ∷ toDigits f (suc m / 10)

fromDigits-toDigits : (fuel n : ℕ) → n ≤ fuel → fromDigits (toDigits fuel n) ≡ n
fromDigits-toDigits zero    zero    _  = refl
fromDigits-toDigits zero    (suc m) ()
fromDigits-toDigits (suc f) zero    _  = refl
fromDigits-toDigits (suc f) (suc m) le = begin
  toℕ (suc m mod 10) + 10 * fromDigits (toDigits f (suc m / 10))
    ≡⟨ cong (λ z → toℕ (suc m mod 10) + 10 * z)
            (fromDigits-toDigits f (suc m / 10) bound) ⟩
  toℕ (suc m mod 10) + 10 * (suc m / 10)
    ≡⟨ cong (_+ 10 * (suc m / 10)) (toℕ-fromℕ< (m%n<n (suc m) 10)) ⟩
  suc m % 10 + 10 * (suc m / 10)
    ≡⟨ cong (suc m % 10 +_) (*-comm 10 (suc m / 10)) ⟩
  suc m % 10 + (suc m / 10) * 10
    ≡⟨ sym (m≡m%n+[m/n]*n (suc m) 10) ⟩
  suc m ∎
  where
    1<10 : 1 < 10
    1<10 = s≤s (s≤s z≤n)
    -- suc m / 10 < suc m ⇒ suc m / 10 ≤ m ≤ f
    bound : suc m / 10 ≤ f
    bound = ≤-trans (≤-pred (m/n<m (suc m) 10 1<10)) (≤-pred le)

------------------------------------------------------------------------
-- Il Codec decimale: MSB-first (leggibile), 0 ↦ "0"
------------------------------------------------------------------------

encNat : ℕ → List Char
encNat zero    = '0' ∷ []
encNat (suc m) = digitsToChars (reverse (toDigits (suc m) (suc m)))

decNat : List Char → Maybe ℕ
decNat cs = charsToDigits cs >>= λ ds → just (fromDigits (reverse ds))

inverseNat : (n : ℕ) → decNat (encNat n) ≡ just n
inverseNat zero = refl
inverseNat (suc m)
  rewrite charsToDigits-inv (reverse (toDigits (suc m) (suc m)))
        | reverse-involutive (toDigits (suc m) (suc m))
        | fromDigits-toDigits (suc m) (suc m) ≤-refl
        = refl

natCodec10 : Codec (List Char) ℕ
natCodec10 = record { enc = encNat ; dec = decNat ; inverse = inverseNat }

------------------------------------------------------------------------
-- Self-check: è davvero decimale, leggibile, e il round-trip regge
------------------------------------------------------------------------

private
  _ : encNat 305 ≡ '3' ∷ '0' ∷ '5' ∷ []        -- MSB-first, con lo zero interno
  _ = refl

  _ : decNat ('4' ∷ '2' ∷ []) ≡ just 42
  _ = refl

  _ : Codec.dec natCodec10 (Codec.enc natCodec10 7) ≡ just 7
  _ = Codec.inverse natCodec10 7
