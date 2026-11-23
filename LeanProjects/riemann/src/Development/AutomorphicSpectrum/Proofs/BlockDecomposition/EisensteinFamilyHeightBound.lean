import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FamMajorant

theorem fam_majorant : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
    ∀ (χ : (AE D)ˣ →* Circle) (s₁ : ℂ) (φ : G D n → ℂ), Continuous φ → IsLaw χ s₁ φ →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : ℂ) (g : G D n), ‖fam H φ s₁ z g‖ ≤ B * (H g : ℝ) ^ (z.re + (n : ℝ) / 2) := by
  rintro D n H hH ⟨C, hC, hcov⟩ χ s₁ φ hφ hlaw
  have hHpos : ∀ g, 0 < (H g : ℝ) := fun g => NNReal.coe_pos.2 (hH.2.1 g)
  have hpos : ∀ g, 0 < (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := fun g => Real.rpow_pos_of_pos (hHpos g) _
  have hcont : Continuous fun g => ‖φ g‖ / (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
    hφ.norm.div ((NNReal.continuous_coe.comp hH.1).rpow_const fun g => Or.inl (hHpos g).ne') fun g => (hpos g).ne'
  obtain ⟨δ, hδ⟩ := hC.exists_bound_of_continuousOn hcont.continuousOn
  have hB0 : 0 ≤ max δ 0 := le_max_right _ _
  have hon : ∀ c ∈ C, ‖φ c‖ ≤ max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro c hc
    have h1 := (hδ c hc).trans (le_max_left δ 0)
    rwa [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (hpos c).le), div_le_iff₀ (hpos c)] at h1
  have hall : ∀ g, ‖φ g‖ ≤ max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    intro g
    obtain ⟨q, hq, c, hc, rfl⟩ := hcov g
    obtain ⟨a, ha⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_blkA hq
    have hr : 0 < absA D (Matrix.GeneralLinearGroup.det a) := hom_pos _ _
    rw [hlaw q hq a ha c, hH.2.2 q hq a ha c]
    have e1 : ‖npow (absA D (Matrix.GeneralLinearGroup.det a)) (s₁ + (n : ℂ) / 2)‖ =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [norm_npow hr]; congr 1; simp
    have e2 : ((absA D (Matrix.GeneralLinearGroup.det a) * H c : ℝ≥0) : ℝ) ^ (s₁.re + (n : ℝ) / 2) =
        (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
      rw [NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]
    rw [e2, norm_mul, norm_mul, e1]
    simp only [Circle.norm_coe, one_mul]
    have h0 : 0 ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) :=
      Real.rpow_nonneg (NNReal.coe_nonneg _) _
    calc _ ≤ (absA D (Matrix.GeneralLinearGroup.det a) : ℝ) ^ (s₁.re + (n : ℝ) / 2) *
          (max δ 0 * (H c : ℝ) ^ (s₁.re + (n : ℝ) / 2)) := mul_le_mul_of_nonneg_left (hon c hc) h0
      _ = _ := by ring
  refine ⟨max δ 0, hB0, fun z g => ?_⟩
  have e3 : ‖npow (H g) (z - s₁)‖ = (H g : ℝ) ^ (z.re - s₁.re) := by
    rw [norm_npow (hH.2.1 g)]; congr 1
  have e4 : (H g : ℝ) ^ (z.re + (n : ℝ) / 2) = (H g : ℝ) ^ (z.re - s₁.re) * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2) := by
    rw [← Real.rpow_add (hHpos g)]; congr 1; ring
  have h0 : 0 ≤ (H g : ℝ) ^ (z.re - s₁.re) := (Real.rpow_pos_of_pos (hHpos g) _).le
  simp only [fam]
  rw [norm_mul, e3, e4]
  calc _ ≤ (H g : ℝ) ^ (z.re - s₁.re) * (max δ 0 * (H g : ℝ) ^ (s₁.re + (n : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left (hall g) h0
    _ = _ := by ring

end GlobalTheory.CompanionTheory.FamMajorant

end
