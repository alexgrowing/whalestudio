import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions MeasureTheory Filter Topology Matrix

noncomputable section

namespace GlobalTheory.UpqExpChart

section General

variable {n : Type} [Fintype n] [DecidableEq n]

theorem continuous_matExp : Continuous (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ) := by
  open scoped Matrix.Norms.Operator in
  exact NormedSpace.exp_continuous

theorem exists_chart : ∃ e : OpenPartialHomeomorph (Matrix n n ℂ) (Matrix n n ℂ),
    (e : Matrix n n ℂ → Matrix n n ℂ) = NormedSpace.exp ∧ (0 : Matrix n n ℂ) ∈ e.source := by
  open scoped Matrix.Norms.Operator in
  have h : HasStrictFDerivAt (NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ)
      ((ContinuousLinearEquiv.refl ℂ (Matrix n n ℂ) : Matrix n n ℂ ≃L[ℂ] Matrix n n ℂ) :
        Matrix n n ℂ →L[ℂ] Matrix n n ℂ) 0 :=
    hasStrictFDerivAt_exp_zero (𝕂 := ℂ) (𝔸 := Matrix n n ℂ)
  open scoped Matrix.Norms.Operator in
  exact ⟨h.toOpenPartialHomeomorph _, rfl, h.mem_toOpenPartialHomeomorph_source⟩

theorem exists_ball_subset {W : Set (Matrix n n ℂ)} (hW : W ∈ 𝓝 (0 : Matrix n n ℂ)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ Z : Matrix n n ℂ, ∑ i, ∑ j, ‖Z i j‖ < δ → Z ∈ W := by
  open scoped Matrix.Norms.Elementwise in
  obtain ⟨δ, hδ, h⟩ := Metric.mem_nhds_iff.1 hW
  refine ⟨δ, hδ, fun Z hZ => h ?_⟩
  open scoped Matrix.Norms.Elementwise in
  rw [mem_ball_zero_iff, Matrix.norm_lt_iff hδ]
  intro i j
  refine lt_of_le_of_lt ?_ hZ
  calc ‖Z i j‖ ≤ ∑ j, ‖Z i j‖ :=
        Finset.single_le_sum (f := fun j => ‖Z i j‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i, ∑ j, ‖Z i j‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖Z i j‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)

theorem exp_mul_exp_neg (X : Matrix n n ℂ) : NormedSpace.exp X * NormedSpace.exp (-X) = 1 := by
  rw [← Matrix.exp_add_of_commute X (-X) (Commute.refl X).neg_right, add_neg_cancel,
    NormedSpace.exp_zero]

theorem exp_neg_mul_exp (X : Matrix n n ℂ) : NormedSpace.exp (-X) * NormedSpace.exp X = 1 := by
  simpa using exp_mul_exp_neg (-X)

theorem exp_conj_invol {J : Matrix n n ℂ} (hJ : J * J = 1) (X : Matrix n n ℂ) :
    NormedSpace.exp (J * X * J) = J * NormedSpace.exp X * J :=
  Matrix.exp_units_conj (⟨J, J, hJ, hJ⟩ : (Matrix n n ℂ)ˣ) X

theorem exp_unitary {J : Matrix n n ℂ} (hJ : J * J = 1) {X : Matrix n n ℂ}
    (hX : Xᴴ * J + J * X = 0) : (NormedSpace.exp X)ᴴ * J * NormedSpace.exp X = J := by
  have h1 : Xᴴ = J * (-X) * J := by
    have : Xᴴ * J = J * (-X) := by rw [Matrix.mul_neg]; exact eq_neg_of_add_eq_zero_left hX
    rw [← this, Matrix.mul_assoc, hJ, Matrix.mul_one]
  rw [← Matrix.exp_conjTranspose, h1, exp_conj_invol hJ, Matrix.mul_assoc _ J J, hJ,
    Matrix.mul_one, Matrix.mul_assoc, exp_neg_mul_exp, Matrix.mul_one]

theorem exp_twist {J : Matrix n n ℂ} (hJ : J * J = 1) {Z : Matrix n n ℂ}
    (hZ : (NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z = J) :
    NormedSpace.exp (J * (-Z)ᴴ * J) = NormedSpace.exp Z := by
  rw [exp_conj_invol hJ, Matrix.exp_conjTranspose]
  have h1 : (NormedSpace.exp (-Z))ᴴ * (NormedSpace.exp Z)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, exp_mul_exp_neg, Matrix.conjTranspose_one]
  have h2 : (NormedSpace.exp (-Z))ᴴ * J = J * NormedSpace.exp Z := by
    calc (NormedSpace.exp (-Z))ᴴ * J
        = (NormedSpace.exp (-Z))ᴴ * ((NormedSpace.exp Z)ᴴ * J * NormedSpace.exp Z) := by rw [hZ]
      _ = J * NormedSpace.exp Z := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]
  rw [Matrix.mul_assoc, h2, ← Matrix.mul_assoc, hJ, Matrix.one_mul]

end General

theorem jpq_sq (P Q : ℕ) : Formalism.UG.Jpq P Q * Formalism.UG.Jpq P Q = 1 := by
  simp [Formalism.UG.Jpq, Matrix.fromBlocks_multiply]

theorem mat_unitary {P Q : ℕ} (g : UpqT P Q) :
    (UpqT.mat g)ᴴ * Formalism.UG.Jpq P Q * UpqT.mat g = Formalism.UG.Jpq P Q := g.2

theorem continuous_mat {P Q : ℕ} : Continuous (UpqT.mat : UpqT P Q → _) :=
  Units.continuous_val.comp continuous_subtype_val

def expU (P Q : ℕ) (X : lieU P Q) : UpqT P Q :=
  (⟨⟨NormedSpace.exp X.1, NormedSpace.exp (-X.1), exp_mul_exp_neg _, exp_neg_mul_exp _⟩,
    exp_unitary (jpq_sq P Q) X.2⟩ : Formalism.UG.Upq P Q)

theorem continuous_expU (P Q : ℕ) : Continuous (expU P Q) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · exact continuous_matExp.comp continuous_subtype_val
  · exact continuous_matExp.comp continuous_subtype_val.neg

end GlobalTheory.UpqExpChart
