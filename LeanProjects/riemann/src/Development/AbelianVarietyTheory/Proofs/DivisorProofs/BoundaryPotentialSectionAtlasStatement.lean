import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSectionAtlas
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSNCAtlasOfIsEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt GlobalTheory.SNCComp
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_potential_section_atlas : ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas d X) (m : ℕ) (α : LocPot X) (Λ : Fin m → LocPot X) (σ : Fin m → X → X → ℂ) (c : ℝ),
    IsBoundarySetting A α Λ σ c →
    ∀ (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s → (∀ y, normSec L s y ≤ 1) →
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [CompactSpace Y] [T2Space Y] (B : FinHolAtlas (n + 1) Y),
    IsProjective B → ∀ (μ : Y → X) (hμ : HoloMap B A μ) (r : ℕ) (W : Fin r → Set Y)
    (e : Fin (m + 1) → Fin r → ℕ),
    IsJointSNC B μ (Fin.cons L Λ) (Fin.cons s σ) W e →
    ∀ (w : ℕ → X → ℝ) (K : ℝ), (∀ R, A.Smooth (w R)) → (∀ R, IsPsh A (α + LocPot.ofFun (w R))) →
    (∀ R x, x ∉ boundary σ →
        -(K * (1 + ∑ i, Real.log (rFun (Λ i) (σ i) x))) ≤ w R x ∧ w R x ≤ 0) →
    ∀ (k : Fin r) (Ck : FinHolAtlas n (W k)), HoloMap Ck B Subtype.val →
    GlobalTheory.SNCComp.IsSNCAtlas B μ (Fin.cons L Λ) (Fin.cons s σ) W e k Ck →
    1 ≤ e 0 k → (∀ i : Fin m, e i.succ k = 0) →
    ∃ C : ℝ, ∀ (R : ℕ) (T : Fin n → LocPot Y),
      (∀ i, T i = (α + LocPot.ofFun (w R)).pullback μ hμ.1 ∨ T i = α.pullback μ hμ.1) →
        -C ≤ mInt Ck (fun i => (T i).pullback Subtype.val continuous_subtype_val) (fun y => w R (μ y.1)) := by
  first | exact @GlobalTheory.SNCCompBound.component_term_bounded | exact GlobalTheory.SNCCompBound.component_term_bounded | (intros; apply GlobalTheory.SNCCompBound.component_term_bounded <;> assumption)
