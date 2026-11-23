import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PureWeightSectionToTwistedPolarisationPower
import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
theorem _root_.GlobalTheory.T.pureWeightSection_to_twistedPolarisationPower : (∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (N d : ℕ) (π : Φ.Pol N) (α : Φ.E.X), 1 ≤ N → 1 ≤ d → (∀ φ : (Φ.H d).Sec, Φ.Pure α φ → ∃ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ((∀ j, s.f j = 0) → ∀ l, φ.f l = 0) ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) ∧ ∀ s : LB.Sec (Out.twistLB π.PB.A π.PB.L (N * d) (π.c α)), ∃ φ : (Φ.H d).Sec, Φ.Pure α φ ∧ ∀ x : Φ.Pt, (⊤ ≤ x.left ⁻¹ᵁ Out.nonzeroLocus φ ↔ ⊤ ≤ (Out.ptSecT π.PB.A (x ≫ Φ.D.q ≫ π.β.hom)).left ⁻¹ᵁ Out.nonzeroLocus s)) := by
  first | exact @GlobalTheory.ZH.TwSec.pure_sec_twist | exact GlobalTheory.ZH.TwSec.pure_sec_twist | (intros; apply GlobalTheory.ZH.TwSec.pure_sec_twist <;> assumption)
