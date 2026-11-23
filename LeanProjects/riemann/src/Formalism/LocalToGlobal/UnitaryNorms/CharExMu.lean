import Formalism.LocalToGlobal.UnitaryNorms.CharExFrame
import Formalism.LocalToGlobal.UnitaryNorms.RealPl

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

def infVal (H : Formalism.BasicNotions.Host R) (n : R.Psi → ℤ) (k : H.Eˣ) : ℂ :=
  ∏ τ, (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ n τ

open Classical in

def InfEven (H : Formalism.BasicNotions.Host R) (n : R.Psi → ℤ) : Prop := ∀ (w : InfinitePlace H.F) (k : H.Fˣ),
  (∏ i ∈ Finset.univ.filter (fun i => InfinitePlace.mk (embPsi H i) ∈ aboveInf (L := H.E) H.F w),
    (embPsi H i ((upF H.F k : H.Eˣ) : H.E) / ((‖embPsi H i ((upF H.F k : H.Eˣ) : H.E)‖ : ℝ) : ℂ)) ^ n i) = 1

structure Mu0F (P : PiBar H) (W : Omg H) (n : R.Psi → ℤ) (j : ℕ) (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles H.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  infTriv : ∀ w x, Φ (infIdele H.E w x) = 1
  trivFin : ∀ v k, Φ (aF H.F v k) = 1
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → ∀ x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion H.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele H.E v x) = 1
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → Φ (localIdele H.E w (atFin w x)) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹
  recF : ∀ a : H.Fˣ, ((Φ (diagUnits H.E (upF H.F a)) : ℂˣ) : ℂ) * infVal H n (upF H.F a) = 1
  sqrtD : ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → ((Φ (diagUnits H.E s) : ℂˣ) : ℂ) * infVal H n s = 1

end CharEx

end Formalism.L2.Host
