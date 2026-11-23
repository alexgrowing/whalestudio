import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSupportingTupleSmoothConeCmField
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open IsLocalRing GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supportingTuple_smoothCone_cmField : ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (φ : InvFun (NumberField.RingOfIntegers E)) (X : Type) [AddCommGroup X] [Module (NumberField.RingOfIntegers E) X] [Module.Finite (NumberField.RingOfIntegers E) X] [Module.Projective (NumberField.RingOfIntegers E) X], IsPolFanOn H.bar φ X → ∀ (r : ℕ) (γ : Fin r → LinearMap.BilinForm ℤ X), IsCone H.bar φ γ → ∃ (d m : ℕ) (a : Fin m → X), 1 ≤ d ∧ Supports H.bar φ d γ a := by
  first | exact @GlobalTheory.Poinc.exists_supports_cm | exact GlobalTheory.Poinc.exists_supports_cm | (intros; apply GlobalTheory.Poinc.exists_supports_cm <;> assumption)
