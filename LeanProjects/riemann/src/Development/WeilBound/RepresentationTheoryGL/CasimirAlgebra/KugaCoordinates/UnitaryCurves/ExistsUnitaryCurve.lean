import Mathlib

noncomputable section

open Matrix

namespace PositivityTheory.Rg.Cz.GK

theorem exists_comb_of_sep {V ι : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ev : ι → Module.Dual ℂ V) (hsep : ∀ v, (∀ i, ev i v = 0) → v = 0) (lam : Module.Dual ℂ V) :
    ∃ (s : Finset ι) (c : ι → ℂ), ∀ v, lam v = ∑ i ∈ s, c i * ev i v := by
  classical
  set W := Submodule.span ℂ (Set.range ev)
  have hW : W = ⊤ := by
    have h1 : W.dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      exact (Submodule.mem_bot ℂ).2 (hsep v fun i => hv _ (Submodule.subset_span ⟨i, rfl⟩))
    have h2 := Subspace.dualCoannihilator_dualAnnihilator_eq (W := W)
    rw [h1, Submodule.dualAnnihilator_bot] at h2
    exact h2.symm
  have hl : lam ∈ W := hW ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hl
  refine ⟨c.support, c, fun v => ?_⟩
  rw [← hc, Finsupp.sum, LinearMap.sum_apply]
  simp [smul_eq_mul]

theorem exists_unitary_curve {a : ℕ} (Y : Matrix (Fin a) (Fin a) ℂ) (hY : Yᴴ = -Y) :
    ∃ U : ℝ → Matrix (Fin a) (Fin a) ℂ, (∀ t, star (U t) * U t = 1) ∧ U 0 = 1 ∧
      ∀ i j, HasDerivAt (fun t => U t i j) (Y i j) 0 := by
  refine ⟨fun t => NormedSpace.exp (t • Y), fun t => ?_, by simp, fun i j => ?_⟩
  · have h1 : star (NormedSpace.exp (t • Y)) = NormedSpace.exp (-(t • Y)) := by
      rw [Matrix.star_eq_conjTranspose, ← Matrix.exp_conjTranspose, Matrix.conjTranspose_smul, hY, star_trivial,
        smul_neg]
    rw [h1, Matrix.exp_neg]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.isUnit_exp _))
  · letI : NormedRing (Matrix (Fin a) (Fin a) ℂ) := Matrix.linftyOpNormedRing
    let _ : NormedAlgebra ℝ (Matrix (Fin a) (Fin a) ℂ) := Matrix.linftyOpNormedAlgebra
    let _ : NormedAlgebra ℚ (Matrix (Fin a) (Fin a) ℂ) := NormedAlgebra.restrictScalars ℚ ℝ _
    have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
    simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
    let L : Matrix (Fin a) (Fin a) ℂ →L[ℝ] ℂ :=
      LinearMap.toContinuousLinearMap
        { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

end PositivityTheory.Rg.Cz.GK

end
