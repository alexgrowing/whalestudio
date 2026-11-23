import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix
open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem mulVec_injective_map {E : Type*} [Field E] {n j : ℕ} (f : E →+* ℂ)
    (Bm : Matrix (Fin n) (Fin j) E) (hB : Function.Injective Bm.mulVec) :
    Function.Injective (Bm.map f).mulVec := by
  classical
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' Bm)
    (by
      rw [LinearMap.ker_eq_bot]
      intro x y hxy
      apply hB
      simpa [Matrix.toLin'_apply] using hxy)
  have hC : LinearMap.toMatrix' g * Bm = 1 := by
    have h1 := congrArg LinearMap.toMatrix' hg
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id, LinearMap.toMatrix'_toLin'] at h1
  have h2 : (LinearMap.toMatrix' g).map f * Bm.map f = 1 := by
    rw [← Matrix.map_mul, hC]
    exact Matrix.map_one f (map_zero f) (map_one f)
  intro x y hxy
  have h3 := congrArg ((LinearMap.toMatrix' g).map f).mulVec hxy
  simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h3
  exact h3

theorem gram_det_re_pos (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) {j : ℕ}
    (b : Fin j → Fin I.n → I.E) (hb : LinearIndependent I.E b) : 0 < (gramV I x v b).det.re := by
  classical
  set A : Matrix (Fin I.n) (Fin I.n) ℂ := uMat (x.1 v)⁻¹ * (I.P v)⁻¹ with hA
  set Bm : Matrix (Fin I.n) (Fin j) I.E := Matrix.of fun i a => b a i with hBm
  have hgram : gramV I x v b = (A * Bm.map (I.φ v))ᴴ * (A * Bm.map (I.φ v)) := by
    ext a c
    have e : ∀ a i, coordV I x v (b a) i = (A * Bm.map (I.φ v)) i a := by
      intro a i
      simp [coordV, A, Bm, Matrix.mulVec, dotProduct, Matrix.mul_apply]
    simp only [gramV, e, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hB : Function.Injective Bm.mulVec := by
    intro c c' h
    have hs : ∑ a, (c a - c' a) • b a = 0 := by
      ext i
      have := congrFun h i
      simp only [Bm, Matrix.mulVec, dotProduct, Matrix.of_apply] at this
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib,
        Pi.zero_apply]
      rw [sub_eq_zero]
      simpa only [mul_comm] using this
    funext a
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb _ hs a)
  have hAu : IsUnit A := (Units.isUnit _).mul (Matrix.isUnit_nonsing_inv_iff.2 (I.P_unit v))
  have hC : Function.Injective (A * Bm.map (I.φ v)).mulVec := by
    intro w w' h
    simp only [← Matrix.mulVec_mulVec] at h
    exact mulVec_injective_map (I.φ v) Bm hB (Matrix.mulVec_injective_iff_isUnit.2 hAu h)
  have hpos := (Matrix.PosDef.conjTranspose_mul_self _ hC).det_pos
  rw [hgram]
  exact (Complex.pos_iff.1 hpos).1

theorem packet_conditions_closed (h1 : LatticeFinitelyGenerated) (h2 : ExistsBoundedBasis) : HeightsPositive := by
  unfold HeightsPositive
  intro I x s
  unfold ht
  obtain ⟨M, hMfg, hM⟩ := h1 I x
  cases s
  apply div_pos
  · apply Finset.prod_pos
    intro v _
    apply gram_det_re_pos
    assumption
  · rw [Nat.cast_pos]
    refine @Nat.card_pos _ _ (h2 _ _ _ M _ _ hMfg ?_ ?_ ?_ ?_)
    all_goals first
      | assumption
      | (intro y hy; rw [← SetLike.mem_coe, hM]; aesop)
      | aesop

end Formalism.L2.SG.Pf.Tau
