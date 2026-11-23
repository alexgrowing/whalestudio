import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ModelDdcForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundaryPotentialSmoothOffDivisorStatement
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.ModelDdcForms MeasureTheory
open scoped ContDiff

namespace GlobalTheory.PoincarePotOn

theorem exp_one_le_rComp {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {m : ℕ}
    (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (hB : IsBoundary A L s D) (i : Fin m) (y : X) : Real.exp 1 ≤ rComp L s i y := by
  have h0 : 0 ≤ normSec (L i) (s i) y := by unfold normSec; positivity
  have h1 : normSec (L i) (s i) y ≤ 1 := (hB i).2.2.2 y
  have h2 : Real.log (normSec (L i) (s i) y ^ 2) ≤ 0 :=
    Real.log_nonpos (by positivity) (pow_le_one₀ h0 h1)
  unfold rComp
  linarith

theorem poincarePot_isPotentialOn : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X)
    (K : LocPot X) {m : ℕ} (L : Fin m → LocPot X) (s : Fin m → X → X → ℂ) (D : Fin m → Set X)
    (c : ℝ), IsPotential A K → IsBoundary A L s D →
    IsPotentialOn A (⋃ i, D i)ᶜ (poincarePot K L s c) := by
  intro e X _ A K m L s D c hK hB
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hcompat : IsCompatChart A (A.chart j) := fun k => ⟨A.holo k j, A.holo j k⟩
    have hKs : ContDiffOn ℝ ∞ (K.φ x ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((poincarePot K L s c).U x ∩ (⋃ i, D i)ᶜ)) :=
      (hK.1 x j).mono (fun z hz => ⟨hz.1, hz.2.1.1⟩)
    have hu : ContDiffOn ℝ ∞
        ((fun y => -(c / 2) * ∑ i, Real.log (rComp L s i y)) ∘ (A.chart j).symm)
        ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ((poincarePot K L s c).U x ∩ (⋃ i, D i)ᶜ)) := by
      intro z hz
      apply ContDiffAt.contDiffWithinAt
      have hnot : ∀ i, (A.chart j).symm z ∉ D i := fun i hi =>
        hz.2.2 (Set.mem_iUnion.2 ⟨i, hi⟩)
      have hsum : ContDiffAt ℝ ∞
          (fun z => ∑ i, Real.log (rComp L s i ((A.chart j).symm z))) z := by
        apply ContDiffAt.sum
        intro i _
        exact (GlobalTheory.T.boundary_potential_smooth_off_divisor A L s D hB i (A.chart j) hcompat z hz.1 (hnot i)).log
          (ne_of_gt (lt_of_lt_of_le (Real.exp_pos 1) (exp_one_le_rComp A L s D hB i _)))
      exact contDiffAt_const.mul hsum
    exact hKs.add hu
  · obtain ⟨W, hW, hyW, G, hG, hGe⟩ := hK.2 x x' y ⟨hy.1.1.1, hy.1.2.1⟩
    refine ⟨W, hW, hyW, G, hG, fun z hz => ?_⟩
    have hz' := hGe z ⟨⟨hz.1.1.1, hz.1.1.2.1⟩, hz.1.2.1⟩
    change K.φ x z + (-(c / 2) * ∑ i, Real.log (rComp L s i z)) -
      (K.φ x' z + (-(c / 2) * ∑ i, Real.log (rComp L s i z))) = _
    rw [← hz']
    ring

end GlobalTheory.PoincarePotOn
