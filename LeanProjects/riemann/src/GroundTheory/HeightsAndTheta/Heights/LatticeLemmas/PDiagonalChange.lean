import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LatticeLemmas

open NumberField NumberField.ComplexEmbedding TensorProduct ComplexAt Matrix
open GroundTheory.Heights₂.Heights

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {E : Type*} [AddCommGroup E] [Module (𝓞 K) E]
  [Module.Finite (𝓞 K) E] [Module.Projective (𝓞 K) E]

theorem span_fibreVec_eq_top (h : HermitianMetric K E) (σ : K →+* ℂ) {ι : Type*} [Fintype ι]
    {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i)) = ⊤ := by
  set N := Submodule.span (𝓞 K) (Set.range s)
  have := finite_quotient_span hs hcard
  set m := Nat.card (E ⧸ N)
  have hm : 0 < m := Nat.card_pos
  have hmem : ∀ e : E, m • e ∈ N := fun e ↦
    (Submodule.Quotient.mk_eq_zero N).mp (by rw [Submodule.Quotient.mk_smul]; exact card_nsmul_eq_zero')
  set W := Submodule.span ℂ (Set.range fun i ↦ fibreVec h σ (s i))
  have h1 : ∀ e ∈ N, fibreVec h σ e ∈ W := by
    intro e he
    induction he using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp [fibreVec]
    | add x y _ _ hx hy => rw [fibreVec_add]; exact W.add_mem hx hy
    | smul a x _ hx => rw [fibreVec_smul]; exact W.smul_mem _ hx
  have h2 : ∀ e : E, fibreVec h σ e ∈ W := by
    intro e
    have := h1 _ (hmem e)
    rw [← Nat.cast_smul_eq_nsmul (𝓞 K) m e, fibreVec_smul] at this
    have hc : (σ ((m : 𝓞 K) : K)) = (m : ℂ) := by simp
    rw [hc] at this
    exact (W.smul_mem_iff (Nat.cast_ne_zero.mpr hm.ne')).mp this
  rw [eq_top_iff]
  rintro x -
  obtain ⟨y, rfl⟩ := (FibreSpace.equiv h σ).surjective x
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact W.zero_mem
  | add y z hy hz => rw [map_add]; exact W.add_mem hy hz
  | tmul z e =>
    have hz : (z ⊗ₜ[𝓞 K] e : Fibre σ E) = ((ofComplex σ).symm z) • ((1 : ComplexAt σ) ⊗ₜ e) := by
      rw [← fibre_smul_eq, smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul]
    exact W.smul_mem _ (h2 e)

theorem gramDet_eq_of_norm_eq (h h' : HermitianMetric K E) (σ : K →+* ℂ)
    (T : Fibre σ E →ₗ[ℂ] Fibre σ E)
    (hT : ∀ x, ‖FibreSpace.equiv h' σ x‖ = ‖FibreSpace.equiv h σ (T x)‖) {ι : Type*} [Fintype ι]
    [DecidableEq ι] {s : ι → E} (hs : LinearIndependent (𝓞 K) s)
    (hcard : Fintype.card ι = Module.finrank (𝓞 K) E) :
    gramDet h' σ s = ‖LinearMap.det T‖ ^ 2 * gramDet h σ s := by
  have kadd : ∀ (c : ℂ) (x y : Fibre σ E), ‖FibreSpace.equiv h' σ x + c • FibreSpace.equiv h' σ y‖ =
      ‖FibreSpace.equiv h σ (T x) + c • FibreSpace.equiv h σ (T y)‖ := by
    intro c x y
    rw [← map_smul, ← map_add, hT, map_add, map_add, map_smul, map_smul]
  have ksub : ∀ (c : ℂ) (x y : Fibre σ E), ‖FibreSpace.equiv h' σ x - c • FibreSpace.equiv h' σ y‖ =
      ‖FibreSpace.equiv h σ (T x) - c • FibreSpace.equiv h σ (T y)‖ := by
    intro c x y
    rw [← map_smul, ← map_sub, hT, map_sub, map_sub, map_smul, map_smul]
  have hinner : ∀ x y : Fibre σ E, inner ℂ (FibreSpace.equiv h' σ x) (FibreSpace.equiv h' σ y) =
      inner ℂ (FibreSpace.equiv h σ (T x)) (FibreSpace.equiv h σ (T y)) := by
    intro x y
    have e1 := kadd 1 x y
    have e2 := ksub 1 x y
    simp only [one_smul] at e1 e2
    rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (FibreSpace.equiv h' σ x),
      inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (FibreSpace.equiv h σ (T x)), e1, e2, kadd, ksub]
  let bv : Module.Basis ι ℂ (FibreSpace h σ) :=
    Module.Basis.mk (linearIndependent_fibreVec h σ hs) (span_fibreVec_eq_top h σ hs hcard).ge
  let S : FibreSpace h σ →ₗ[ℂ] FibreSpace h σ := (FibreSpace.equiv h σ).conj T
  let B := LinearMap.toMatrix bv bv S
  have hS : ∀ e : E, S (fibreVec h σ e) = FibreSpace.equiv h σ (T ((1 : ComplexAt σ) ⊗ₜ e)) := by
    intro e
    simp only [S, LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, fibreVec,
      LinearEquiv.symm_apply_apply]
  have hgram : (gram ℂ fun i ↦ fibreVec h' σ (s i)) = gram ℂ fun j ↦ ∑ i, B i j • bv i := by
    ext i j
    simp only [gram_apply]
    have hj : ∀ j, ∑ i, B i j • bv i = S (fibreVec h σ (s j)) := by
      intro j
      have := bv.sum_repr (S (bv j))
      simp only [B, LinearMap.toMatrix_apply]
      rw [this, Module.Basis.mk_apply]
    rw [hj, hj, hS, hS]
    exact hinner _ _
  have hbv : (⇑bv : ι → FibreSpace h σ) = fun i ↦ fibreVec h σ (s i) := funext fun i ↦ Module.Basis.mk_apply _ _ _
  have hdet : B.det = LinearMap.det T := by
    rw [LinearMap.det_toMatrix]
    exact LinearMap.det_conj T (FibreSpace.equiv h σ)
  simp only [gramDet]
  rw [hgram, gram_comb, hbv, det_mul, det_mul, det_conjTranspose, mul_comm _ B.det, ← mul_assoc,
    RCLike.star_def, Complex.mul_conj, Complex.re_ofReal_mul, Complex.normSq_eq_norm_sq, hdet]

theorem DiagonalChange.proof : DiagonalChange.Statement := by
  intro K _ _ M h' T hT _
  classical
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := M.carrier)
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) M.carrier)) =
      Module.finrank (𝓞 K) M.carrier := Fintype.card_fin _
  have hlog : ∀ σ : K →+* ℂ, Real.log (gramDet h' σ s) =
      2 * Real.log ‖LinearMap.det (T σ)‖ + Real.log (gramDet M.metric σ s) := by
    intro σ
    have hp := gramDet_pos h' σ hs
    have hp0 := gramDet_pos M.metric σ hs
    rw [gramDet_eq_of_norm_eq M.metric h' σ (T σ) (hT σ) hs hcard] at hp ⊢
    have hd : ‖LinearMap.det (T σ)‖ ≠ 0 := by
      intro h0
      rw [h0] at hp
      simp at hp
    rw [Real.log_mul (pow_ne_zero 2 hd) hp0.ne', Real.log_pow]
    push_cast
    ring
  simp only [HermitianBundle.deg, HermitianBundle.arithDegree]
  rw [arithDegree_eq h' hs hcard, arithDegree_eq M.metric hs hcard]
  simp only [degreeWith, hlog, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end

end GroundTheory.Heights₂.Heights.LatticeLemmas
