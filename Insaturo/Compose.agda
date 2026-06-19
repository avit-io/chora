{-# OPTIONS --safe --without-K #-}

------------------------------------------------------------------------
-- insaturo — Compose
--
-- La grammatica è di prima classe solo se le spec SI COMPONGONO. Due
-- modi, uno per costruttore concettuale:
--
--   _×ˢ_   PRODOTTO dei buchi: due spec su buchi diversi (C e D) danno
--          una spec sul buco-coppia (C × D). Le leggi di ciascun lato si
--          tirano indietro lungo la proiezione. È come si specificano due
--          componenti insieme tenendo separati i loro obblighi.
--
--   _∧+_   RAFFORZAMENTO: una spec sullo STESSO buco, con più obblighi.
--          È l'unione delle leggi: stesso Carrier, leggi congiunte. Più
--          leggi = spec più stretta (mai più larga).
--
-- Il punto non sono i costruttori ma i TEOREMI: conformità al composto
-- ⇔ conformità ai pezzi. Da lì cadono i corollari onesti — la
-- saturazione del prodotto EMERGE da quelle delle parti (`sat×ˢ`), e il
-- rifiuto di un pezzo RIFIUTA il tutto (`refuse×ˢˡ/ʳ`).
------------------------------------------------------------------------

module Insaturo.Compose where

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)

open import Insaturo.Core

private
  variable
    ℓ : Level

------------------------------------------------------------------------
-- Costruttori di servizio
------------------------------------------------------------------------

-- Una spec da un Carrier e le sue leggi (rende `Carrier (sig …)` ridotto).
spec : (C : Set ℓ) → List (Law C) → Spec ℓ
spec C ls = record { sig = record { Carrier = C } ; laws = ls }

-- Tira indietro una legge lungo f : D → C. La stessa proposizione,
-- osservata sul componente f-esimo del candidato.
mapLaw : ∀ {C D : Set ℓ} → (D → C) → Law C → Law D
mapLaw f l = record { Holds = λ d → Holds l (f d) }

------------------------------------------------------------------------
-- Lemmi su AllHold: ++ e map distribuiscono
------------------------------------------------------------------------

-- `++` si spacca / si ricuce su AllHold.
allHold-split : ∀ {C : Set ℓ} {impl : C} (xs ys : List (Law C))
              → AllHold impl (xs ++ ys) → AllHold impl xs × AllHold impl ys
allHold-split []       ys h        = [] , h
allHold-split (x ∷ xs) ys (px ∷ h) with allHold-split xs ys h
... | hx , hy = (px ∷ hx) , hy

allHold-join : ∀ {C : Set ℓ} {impl : C} (xs ys : List (Law C))
             → AllHold impl xs → AllHold impl ys → AllHold impl (xs ++ ys)
allHold-join []       ys []        hy = hy
allHold-join (x ∷ xs) ys (px ∷ hx) hy = px ∷ allHold-join xs ys hx hy

-- `map (mapLaw f)` su AllHold equivale a osservare in `f d`.
-- (Holds (mapLaw f l) d ≡ Holds l (f d) per definizione: niente da provare.)
allHold-map→ : ∀ {C D : Set ℓ} {d : D} (f : D → C) (ls : List (Law C))
             → AllHold d (map (mapLaw f) ls) → AllHold (f d) ls
allHold-map→ f []       []       = []
allHold-map→ f (l ∷ ls) (p ∷ h)  = p ∷ allHold-map→ f ls h

allHold-map← : ∀ {C D : Set ℓ} {d : D} (f : D → C) (ls : List (Law C))
             → AllHold (f d) ls → AllHold d (map (mapLaw f) ls)
allHold-map← f []       []       = []
allHold-map← f (l ∷ ls) (p ∷ h)  = p ∷ allHold-map← f ls h

------------------------------------------------------------------------
-- _×ˢ_ — PRODOTTO dei buchi
--
-- Funziona su DUE spec qualunque: il buco diventa la coppia, ogni lato
-- conserva i suoi obblighi tirati indietro lungo la proiezione.
------------------------------------------------------------------------

_×ˢ_ : Spec ℓ → Spec ℓ → Spec ℓ
s ×ˢ t = spec (Carrier (sig s) × Carrier (sig t))
              (map (mapLaw proj₁) (laws s) ++ map (mapLaw proj₂) (laws t))

-- Conformità al prodotto ⇔ conformità ai due pezzi sui due componenti.
×ˢ-split : (s t : Spec ℓ) (i : Carrier (sig s)) (j : Carrier (sig t))
         → Conforms (s ×ˢ t) (i , j) → Conforms s i × Conforms t j
×ˢ-split s t i j h with allHold-split (map (mapLaw proj₁) (laws s))
                                       (map (mapLaw proj₂) (laws t)) h
... | hi , hj = allHold-map→ proj₁ (laws s) hi , allHold-map→ proj₂ (laws t) hj

×ˢ-join : (s t : Spec ℓ) (i : Carrier (sig s)) (j : Carrier (sig t))
        → Conforms s i → Conforms t j → Conforms (s ×ˢ t) (i , j)
×ˢ-join s t i j hi hj =
  allHold-join (map (mapLaw proj₁) (laws s)) (map (mapLaw proj₂) (laws t))
    (allHold-map← proj₁ (laws s) hi) (allHold-map← proj₂ (laws t) hj)

-- COROLLARIO: la saturazione del prodotto EMERGE da quelle delle parti.
-- Saturi i due componenti separatamente, il tutto è saturato — teorema.
sat×ˢ : {s t : Spec ℓ} → Sat s → Sat t → Sat (s ×ˢ t)
sat×ˢ {s = s} {t = t} (i , hi) (j , hj) = (i , j) , ×ˢ-join s t i j hi hj

-- DUALE: se un pezzo RIFIUTA, il prodotto rifiuta. L'onestà si propaga.
refuse×ˢˡ : {s t : Spec ℓ} (i : Carrier (sig s)) (j : Carrier (sig t))
          → Refuses s i → Refuses (s ×ˢ t) (i , j)
refuse×ˢˡ {s = s} {t = t} i j r h = r (proj₁ (×ˢ-split s t i j h))

refuse×ˢʳ : {s t : Spec ℓ} (i : Carrier (sig s)) (j : Carrier (sig t))
          → Refuses t j → Refuses (s ×ˢ t) (i , j)
refuse×ˢʳ {s = s} {t = t} i j r h = r (proj₂ (×ˢ-split s t i j h))

------------------------------------------------------------------------
-- _∧+_ — RAFFORZAMENTO (unione delle leggi sullo stesso buco)
--
-- Stesso Carrier, più obblighi. È l'unione: una spec con le leggi di
-- partenza PIÙ quelle aggiunte.
------------------------------------------------------------------------

_∧+_ : (s : Spec ℓ) → List (Law (Carrier (sig s))) → Spec ℓ
s ∧+ extra = record { sig = sig s ; laws = laws s ++ extra }

-- Conformità alla spec rafforzata ⇔ conformità a quella base E ai nuovi obblighi.
∧+-split : (s : Spec ℓ) (extra : List (Law (Carrier (sig s)))) (impl : Carrier (sig s))
         → Conforms (s ∧+ extra) impl → Conforms s impl × AllHold impl extra
∧+-split s extra impl h = allHold-split (laws s) extra h

∧+-join : (s : Spec ℓ) (extra : List (Law (Carrier (sig s)))) (impl : Carrier (sig s))
        → Conforms s impl → AllHold impl extra → Conforms (s ∧+ extra) impl
∧+-join s extra impl h e = allHold-join (laws s) extra h e

-- COROLLARIO: rafforzare RESTRINGE — chi chiude la spec più stretta
-- chiude anche quella base. Mai il contrario (più leggi, meno impl).
∧+-weaken : (s : Spec ℓ) (extra : List (Law (Carrier (sig s)))) (impl : Carrier (sig s))
          → Conforms (s ∧+ extra) impl → Conforms s impl
∧+-weaken s extra impl h = proj₁ (∧+-split s extra impl h)

------------------------------------------------------------------------
-- Self-check: la composizione all'opera (typecheck = il test)
------------------------------------------------------------------------

private
  open import Level using (0ℓ)
  open import Data.Nat using (ℕ)
  open import Data.Unit using (⊤; tt)

  triv : ∀ {C : Set} → Law C
  triv = record { Holds = λ _ → ⊤ }

  specA specB : Spec 0ℓ
  specA = spec ℕ (triv ∷ [])
  specB = spec ℕ (triv ∷ [])

  satA : Sat specA
  satA = 7 , (tt ∷ [])
  satB : Sat specB
  satB = 9 , (tt ∷ [])

  -- la saturazione del prodotto cade fuori dalle due — non si ricostruisce.
  satAB : Sat (specA ×ˢ specB)
  satAB = sat×ˢ satA satB

  -- rafforzare specA con un'altra legge e richiuderla.
  satA′ : Sat (specA ∧+ (triv ∷ []))
  satA′ = 7 , ∧+-join specA (triv ∷ []) 7 (tt ∷ []) (tt ∷ [])
