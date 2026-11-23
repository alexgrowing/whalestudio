import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

def embPsi (g : R.Psi) : H.E →+* ℂ := H.emb (g : R.GG)

structure IsClsF (ξ : HChar H.E) : Prop where
  unitary : ξ.IsUnitary
  unr : ∀ v, ξ.UnrAt v
  inf : ∀ k, ξ.inf k = 1
  triv : ξ.TrivOn H.F

structure IsEtaT (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta H.F
  inf : χ.HasInf (embPsi H) (fun _ => 1)

def etaAlg (χ : HChar H.E) (v : HeightOneSpectrum (𝓞 H.E)) : ℂ := χ.valTw (1 / 2) v

def IsEtaAlg (χa : HChar H.E) : Prop := ∃ χ : HChar H.E, IsEtaT H χ ∧ χ.IsUnitaryNormOf χa (1 / 2)

def EtaTExists : Prop := ∃ χ : HChar H.E, IsEtaT H χ

structure IsChiPsi (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  triv : χ.TrivOn H.F
  inf : χ.HasInf (embPsi H) (fun _ => 2)

structure PiBar where
  pb : Fin 2 → HeightOneSpectrum (𝓞 H.K)
  pb_over : ∀ k, ((H.g k : ℕ) : 𝓞 H.K) ∈ (pb k).asIdeal

def PiBar.Div {H : Formalism.BasicNotions.Host R} (P : PiBar H) (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  w.under (𝓞 H.K) = P.pb k

structure Omg where
  om : ∀ k : Fin 2, (ZMod (H.g k))ˣ →* ℂˣ
  gen : ∀ k, Function.Injective (om k)

variable {H}

structure IsMu0 (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn H.F
  inf : χ.HasInfQ (embPsi H) (fun τ => -e τ)
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → χ.locK w x = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹

def Mu0Exists (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) : Prop := ∃ χ : HChar H.E, IsMu0 P W e j χ

structure IsDelta (p : ℕ) (χ : HChar H.E) : Prop where
  fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  unr : ∀ v, ¬ OverP H p v → χ.UnrAt v
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → χ.loc v x ^ n = 1) ↔ 15 ∣ n

def DeltaExists (p : ℕ) : Prop := ∃ χ : HChar H.E, IsDelta (H := H) p χ

structure IsPsi (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E) : Prop where
  ord : ∃ a : ℕ, χ.OrderDvd (l ^ a)
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  ram : ∀ v, χ.UnrAt v ↔ v ∉ Q
  atl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1
  split : ∀ v ∈ Q, IsSplitPl H v

def SplitsCompletely (Q : Finset (HeightOneSpectrum (𝓞 H.E))) : Prop :=
  ∀ v ∈ Q, ∀ p : ℕ, p.Prime → OverP H p v → ∀ v' : HeightOneSpectrum (𝓞 H.E), OverP H p v' →
    Ideal.absNorm v'.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v'.asIdeal ^ 2

end Formalism.L2.Host
