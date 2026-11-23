import Formalism.LocalToGlobal.UnitaryNorms.CharExEta
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CharExtend
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.IdeleUnitsOpen

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

namespace CharEx

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

structure Mu0L (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  unitU : ∀ u ∈ unitIdeles H.E, ‖((Φ u : ℂˣ) : ℂ)‖ = 1
  trivFin : ∀ v k, Φ (aF H.F v k) = 1
  trivInf : ∀ w k, Φ (aFi H.F w k) = 1
  inf : ∃ n : R.Psi → ℤ, (∀ τ, (n τ : ℚ) = 2 * (-e τ)) ∧ ∀ k : H.Eˣ, ((Φ (infDiag k) : ℂˣ) : ℂ) =
    ∏ τ, (embPsi H τ (k : H.E) / ((‖embPsi H τ (k : H.E)‖ : ℝ) : ℂ)) ^ n τ
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → ∀ x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion H.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele H.E v x) = 1
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → Φ (localIdele H.E w (atFin w x)) = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹
  recF : ∀ a : H.Fˣ, Φ (diagUnits H.E (upF H.F a)) = 1
  sqrtD : ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → Φ (diagUnits H.E s) = 1

structure DeltaL (p : ℕ) (Φ : Ideles H.E →* ℂˣ) : Prop where
  cont : Continuous Φ
  finU : ∃ n : ℕ, 0 < n ∧ ∀ u ∈ unitIdeles H.E, Φ u ^ n = 1
  trivFin : ∀ v k, Φ (aF H.F v k) = 1
  trivInf : ∀ w k, Φ (aFi H.F w k) = 1
  tame : ∀ v x, IsUnitAt v x → Valued.v ((x : v.adicCompletion H.E) - 1) ≤ WithZero.exp (-((1 : ℕ) : ℤ)) →
    Φ (localIdele H.E v x) = 1
  unr : ∀ v, ¬ OverP H p v → ∀ x, IsUnitAt v x → Φ (localIdele H.E v x) = 1
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → Φ (localIdele H.E v x) ^ n = 1) ↔ 15 ∣ n
  recF : ∀ a : H.Fˣ, Φ (diagUnits H.E (upF H.F a)) = 1
  sqrtD : ∀ s : H.Eˣ, (s : H.E) = H.sqrtMinusD → Φ (diagUnits H.E s) = 1

end CharEx

end Formalism.L2.Host
