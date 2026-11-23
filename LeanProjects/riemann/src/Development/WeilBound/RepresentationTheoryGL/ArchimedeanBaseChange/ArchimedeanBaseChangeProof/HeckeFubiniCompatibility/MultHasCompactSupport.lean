import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.EntZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LengthContinuousProperSublevelStatement

noncomputable section

open MeasureTheory Matrix
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG

variable {n : ℕ}

theorem val_mem_GLs (y : G n) : y.val ∈ GLs n :=
  ((Matrix.isUnit_iff_isUnit_det _).1 y.isUnit).ne_zero

theorem isUnit_det_unitary (u : Matrix.unitaryGroup (Fin n) ℂ) : IsUnit (u.1.det) :=
  Matrix.isUnit_det_of_left_inverse (Unitary.star_mul_self_of_mem u.2)

theorem mul_mem_GLs {y : Mat n} (hy : y ∈ GLs n) (u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ) :
    u₁.1 * y * u₂.1 ∈ GLs n := by
  show (u₁.1 * y * u₂.1).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero (isUnit_det_unitary u₁).ne_zero hy) (isUnit_det_unitary u₂).ne_zero

section Mult

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {M : KMod n} {k : Mat n → (M.V →L[ℂ] M.V)}
  {val : Inf n → ℂ} {T : ℝ}

theorem mult_continuous (h : IsMult μ M k val T) : Continuous fun y : G n => k y.val := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  have e : (fun y : G n => k y.val) = fun y => ∑ i, c i • ks i y.val :=
    funext fun y => hk _ (val_mem_GLs y)
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((hks i).2.1.continuousOn.comp_continuous Units.continuous_val val_mem_GLs).const_smul (c i)

theorem mult_exists_lg (h : IsMult μ M k val T) : ∃ R : ℝ, ∀ y ∈ GLs n, R < lg y → k y = 0 := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  choose R hR using fun i => (hks i).2.2.1
  refine ⟨∑ i, |R i|, fun y hy hlt => ?_⟩
  rw [hk _ hy]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hR i y hy (lt_of_le_of_lt ((le_abs_self _).trans
    (Finset.single_le_sum (fun j _ => abs_nonneg (R j)) (Finset.mem_univ i))) hlt), smul_zero]

theorem mult_hasCompactSupport (h : IsMult μ M k val T) : HasCompactSupport fun y : G n => k y.val := by
  obtain ⟨R, hR⟩ := mult_exists_lg h
  exact HasCompactSupport.intro ((GlobalTheory.T.length_continuous_proper_sublevel n).2 R) fun y hy => hR _ (val_mem_GLs y) (not_le.1 hy)

theorem mult_equivariant (h : IsMult μ M k val T) : ∀ y ∈ GLs n, ∀ u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ,
    k (u₁.1 * y * u₂.1) = M.ρ u₁ * k y * M.ρ u₂ := by
  obtain ⟨m, c, w, g, ks, hks, hk, -⟩ := h
  intro y hy u₁ u₂
  rw [hk _ (mul_mem_GLs hy u₁ u₂), hk _ hy, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [(hks i).2.2.2.1 y hy u₁ u₂]
  simp only [mul_smul_comm, smul_mul_assoc]

theorem mult_equivariant_val (h : IsMult μ M k val T) (y : G n) (u₁ u₂ : Matrix.unitaryGroup (Fin n) ℂ) :
    k (u₁.1 * y.val * u₂.1) = M.ρ u₁ * k y.val * M.ρ u₂ :=
  mult_equivariant h _ (val_mem_GLs y) u₁ u₂

end Mult

section Ent

variable {M : KMod n}

theorem continuous_ent {X : Type} [TopologicalSpace X] {f : X → (M.V →L[ℂ] M.V)} (hf : Continuous f) (i j : Ix M) :
    Continuous fun x => ent M (f x) i j :=
  continuous_const.inner (hf.clm_apply continuous_const)

theorem hasCompactSupport_ent {X : Type} [TopologicalSpace X] {f : X → (M.V →L[ℂ] M.V)} (hf : HasCompactSupport f)
    (i j : Ix M) : HasCompactSupport fun x => ent M (f x) i j :=
  hf.comp_left (g := fun A => ent M A i j) (ent_zero M i j)

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {k : Mat n → (M.V →L[ℂ] M.V)} {val : Inf n → ℂ} {T : ℝ}

theorem mult_ent (h : IsMult μ M k val T) (i j : Ix M) :
    Continuous (fun y : G n => ent M (k y.val) i j) ∧ HasCompactSupport (fun y : G n => ent M (k y.val) i j) :=
  ⟨continuous_ent (mult_continuous h) i j, hasCompactSupport_ent (mult_hasCompactSupport h) i j⟩

end Ent

end PositivityTheory.Rg.BcB.CG

end
