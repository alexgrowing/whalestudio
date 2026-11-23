import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralSphericalUnit
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_orbital_integral_spherical_unit : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ y : GLw n w, (nrmL n w y).val.charpoly = atPl w P → twOrb (thL n w) (GlobalTheory.LFun.KGL w n) y ((GlobalTheory.LFun.KGL w n : Set (GLw n w)).indicator 1) = if ∃ g : GLw n w, g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w n then 1 else 0 := by
  first | exact @GlobalTheory.UnitOrb.twOrb_unit_eventually | exact GlobalTheory.UnitOrb.twOrb_unit_eventually | (intros; apply GlobalTheory.UnitOrb.twOrb_unit_eventually <;> assumption)
