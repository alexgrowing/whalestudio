import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpBallUMemNhds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpqLocallyCompactGroup

open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal

namespace GlobalTheory.ExpBallCompare

variable {P Q : ℕ}

theorem entry_le_l1 (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) (i j) : ‖Z i j‖ ≤ l1 Z :=
  (Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i))

theorem l1_add_le (Z W : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) :
    l1 (Z + W) ≤ l1 Z + l1 W := by
  unfold l1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun j _ => norm_add_le _ _

theorem l1_neg (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) : l1 (-Z) = l1 Z := by
  simp [l1]

theorem exists_l1_ball {S : Set (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)} (hS : S ∈ 𝓝 0) :
    ∃ δ > 0, ∀ Z, l1 Z < δ → Z ∈ S := by
  have hS' : S ∈ 𝓝 (0 : (Fin P ⊕ Fin Q) → (Fin P ⊕ Fin Q) → ℂ) := hS
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hS'
  refine ⟨δ, hδ, fun Z hZ => h ?_⟩
  exact mem_ball_zero_iff.2 ((pi_norm_lt_iff hδ).2 fun i => (pi_norm_lt_iff hδ).2 fun j =>
    (entry_le_l1 Z i j).trans_lt hZ)

theorem exp_isLittleO (A : Type) [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] :
    (fun Z : A => NormedSpace.exp Z - 1 - Z) =o[𝓝 0] fun Z => Z := by
  have h := (hasFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := A)).isLittleO
  simpa using h

theorem eventually_l1_exp {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ in 𝓝 0,
      l1 (NormedSpace.exp Z - 1 - Z) ≤ ε * l1 Z := by
  let : NormedRing (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedRing
  let : NormedAlgebra ℂ (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := Matrix.linftyOpNormedAlgebra
  have : CompleteSpace (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) := FiniteDimensional.complete ℂ _
  have hrow : ∀ (Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) i, ∑ j, ‖Z i j‖ ≤ ‖Z‖ := by
    intro Z i
    rw [Matrix.linfty_opNorm_def]
    have := Finset.le_sup (f := fun i => ∑ j, ‖Z i j‖₊) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa using h2
  have h1 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z ≤ (P + Q : ℝ) * ‖Z‖ := by
    intro Z
    have := Finset.sum_le_card_nsmul Finset.univ (fun i => ∑ j, ‖Z i j‖) ‖Z‖ fun i _ => hrow Z i
    simpa [l1] using this
  have h2 : ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, ‖Z‖ ≤ l1 Z := by
    intro Z
    rw [Matrix.linfty_opNorm_def]
    have : (Finset.univ.sup fun i => ∑ j, ‖Z i j‖₊) ≤ ∑ i, ∑ j, ‖Z i j‖₊ :=
      Finset.sup_le fun i _ => Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖₊)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have h2 := NNReal.coe_le_coe.2 this
    simpa [l1] using h2
  have hN : (0 : ℝ) < P + Q + 1 := by positivity
  have h3 := (exp_isLittleO (Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ)).def (div_pos hε hN)
  filter_upwards [h3] with Z hZ
  calc l1 (NormedSpace.exp Z - 1 - Z) ≤ (P + Q : ℝ) * ‖NormedSpace.exp Z - 1 - Z‖ := h1 _
    _ ≤ (P + Q + 1 : ℝ) * (ε / (P + Q + 1) * ‖Z‖) :=
      mul_le_mul (by linarith) hZ (norm_nonneg _) hN.le
    _ = ε * ‖Z‖ := by field_simp
    _ ≤ ε * l1 Z := mul_le_mul_of_nonneg_left (h2 Z) hε.le

theorem exists_l1_exp {t : ℝ} (ht : 1 < t) : ∃ δ > 0,
    ∀ Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ, l1 Z < δ →
      l1 (NormedSpace.exp Z - 1) ≤ t * l1 Z ∧ l1 Z ≤ t * l1 (NormedSpace.exp Z - 1) := by
  have ht0 : 0 < t := by linarith
  have hε : 0 < 1 - t⁻¹ := sub_pos.2 (inv_lt_one_of_one_lt₀ ht)
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball
    ((eventually_l1_exp (P := P) (Q := Q) hε).and (eventually_l1_exp (sub_pos.2 ht)))
  refine ⟨δ, hδ, fun Z hZ => ?_⟩
  obtain ⟨h1, h2⟩ := h Z hZ
  constructor
  · have := l1_add_le (NormedSpace.exp Z - 1 - Z) Z
    rw [sub_add_cancel] at this
    linarith
  · have := l1_add_le (NormedSpace.exp Z - 1) (-(NormedSpace.exp Z - 1 - Z))
    rw [l1_neg, ← sub_eq_add_neg, sub_sub_cancel] at this
    have h3 : t⁻¹ * l1 Z ≤ l1 (NormedSpace.exp Z - 1) := by linarith
    exact (inv_mul_le_iff₀ ht0).1 h3

theorem exists_gauge_ball {S : Set (UpqT P Q)} (hS : S ∈ 𝓝 (1 : UpqT P Q)) :
    ∃ δ > 0, ∀ g, gauge g < δ → g ∈ S := by
  rw [GlobalTheory.UpqTopology.isClosedEmbedding_mat.isInducing.nhds_eq_comap] at hS
  obtain ⟨T, hT, hTS⟩ := hS
  have h1 : UpqT.mat (1 : UpqT P Q) = 1 := rfl
  have c : Continuous fun Z : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ => Z + 1 :=
    continuous_id.add continuous_const
  obtain ⟨δ, hδ, h⟩ := exists_l1_ball (c.continuousAt.preimage_mem_nhds (x := 0) (t := T)
    (by rw [zero_add, ← h1]; exact hT))
  refine ⟨δ, hδ, fun g hg => hTS ?_⟩
  simpa using h _ hg

theorem expBall_compare : ∀ (P Q : ℕ) (t : ℝ), 1 < t → ∀ᶠ r in 𝓝[>] (0 : ℝ), expBall P Q (t⁻¹ * r) ⊆ {g : UpqT P Q | gauge g < r} ∧ {g : UpqT P Q | gauge g < r} ⊆ expBall P Q (t * r) := by
  intro P Q t ht
  have ht0 : 0 < t := by linarith
  obtain ⟨δ, hδ, h⟩ := exists_l1_exp (P := P) (Q := Q) ht
  obtain ⟨η, hη, h'⟩ := exists_gauge_ball (GlobalTheory.ExpBallNhds.exp_ballU_mem_nhds P Q δ hδ)
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hη)] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrδ : r < δ := hr1.trans_le (min_le_left _ _)
  have hrη : r < η := hr1.trans_le (min_le_right _ _)
  constructor
  · rintro g ⟨X, hX, hg⟩
    have hX' : l1 (X : Matrix (Fin P ⊕ Fin Q) (Fin P ⊕ Fin Q) ℂ) < t⁻¹ * r := hX
    have h1 : t⁻¹ * r ≤ r := mul_le_of_le_one_left hr0.le (inv_lt_one_of_one_lt₀ ht).le
    have h2 := (h X (by linarith)).1
    have h3 := (lt_inv_mul_iff₀ ht0).1 hX'
    show l1 (UpqT.mat g - 1) < r
    rw [hg]
    linarith
  · intro g hg
    have hg' : l1 (UpqT.mat g - 1) < r := hg
    obtain ⟨X, hX, hgX⟩ := h' g (lt_trans hg hrη)
    refine ⟨X, ?_, hgX⟩
    have h2 := (h X hX).2
    rw [hgX] at hg'
    exact h2.trans_lt (mul_lt_mul_of_pos_left hg' ht0)

end GlobalTheory.ExpBallCompare
