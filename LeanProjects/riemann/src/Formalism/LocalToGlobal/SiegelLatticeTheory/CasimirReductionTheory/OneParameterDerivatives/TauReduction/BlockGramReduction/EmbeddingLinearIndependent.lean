import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.LatticeVectorsBoundedBelow

set_option autoImplicit false

noncomputable section

open NumberField Matrix Module
open scoped ComplexOrder

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

theorem complex_embedding_cases (I : AutInst) (σ : I.E →+* ℂ) :
    ∃ v, σ = I.φ v ∨ σ = (starRingEnd ℂ).comp (I.φ v) := by
  classical
  haveI := I.cm.totReal
  let ψ : I.F →+* ℂ := σ.comp (algebraMap I.F I.E)
  let v : InfinitePlace I.F := InfinitePlace.mk ψ
  have hreal : ComplexEmbedding.IsReal ψ := InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal v)
  have hemb : v.embedding = ψ := InfinitePlace.embedding_mk_eq_of_isReal hreal
  have hagree : ∀ x : I.F, σ (algebraMap I.F I.E x) = I.φ v (algebraMap I.F I.E x) := by
    intro x
    rw [I.φ_over, hemb]
    rfl
  have hF : ∀ t : I.E, star t = t → σ t = I.φ v t := by
    intro t ht
    obtain ⟨x, rfl⟩ := (I.cm.fixed t).mp ht
    exact hagree x
  have key : ∀ a : I.E, σ a = I.φ v a ∨ σ a = starRingEnd ℂ (I.φ v a) := by
    intro a
    have ht := hF (a + star a) (by rw [star_add, star_star, add_comm])
    have hm := hF (a * star a) (by rw [star_mul, star_star])
    rw [map_add, map_add] at ht
    rw [map_mul, map_mul] at hm
    have hprod : (σ a - I.φ v a) * (σ a - I.φ v (star a)) = 0 := by
      linear_combination (σ a) * ht - hm
    rcases mul_eq_zero.mp hprod with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · right
      rw [sub_eq_zero.mp h]
      exact I.cm.cmUnram.2.1 (I.φ v) a
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon v
  obtain ⟨a, ha⟩ : ∃ a, σ a ≠ I.φ v a := by
    by_contra h
    push_neg at h
    exact h1 (RingHom.ext h)
  obtain ⟨b, hb⟩ : ∃ b, σ b ≠ starRingEnd ℂ (I.φ v b) := by
    by_contra h
    push_neg at h
    exact h2 (RingHom.ext h)
  have ha' := (key a).resolve_left ha
  have hb' := (key b).resolve_right hb
  rcases key (a + b) with h | h
  · apply ha
    rw [map_add, map_add] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add, map_add, map_add] at h
    linear_combination h - ha'

theorem embedding_linear_independent (I : AutInst) :
    LinearIndependent ℝ (fun i : Free.ChooseBasisIndex ℤ (𝓞 I.E) =>
      fun v : InfinitePlace I.F => I.φ v (integralBasis I.E i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcard : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 I.E)) = Fintype.card (I.E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← NumberField.RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e := Fintype.equivOfCardEq hcard
  have hdet : (Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis I.E) e).det ≠ 0 := by
    intro h0
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis I.E) e
    rw [h0] at h1
    exact Algebra.discr_not_zero_of_basis ℚ (integralBasis I.E)
      ((map_eq_zero_iff (algebraMap ℚ ℂ) (algebraMap ℚ ℂ).injective).mp (by rw [h1]; ring))
  have hall : ∀ σ : I.E →+* ℂ, ∑ i, (g i : ℂ) * σ (integralBasis I.E i) = 0 := by
    intro σ
    obtain ⟨v, hv | hv⟩ := complex_embedding_cases I σ
    · have := congrFun hg v
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul] at this
      rw [hv]
      exact this
    · have := congrArg (starRingEnd ℂ) (congrFun hg v)
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, Complex.real_smul, map_sum, map_mul,
        Complex.conj_ofReal, map_zero] at this
      rw [hv]
      simp only [RingHom.coe_comp, Function.comp_apply]
      exact this
  have hvec : (fun i => (g i : ℂ)) ᵥ* Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis I.E) e = 0 := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix,
      Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.refl_symm, Equiv.refl_apply, Equiv.symm_symm,
      Matrix.of_apply, Pi.zero_apply]
    exact hall (e j).toRingHom
  have h0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hvec
  intro i
  have hi := congrFun h0 i
  simp only [Pi.zero_apply] at hi
  exact_mod_cast hi

theorem card_infinite_places (I : AutInst) : Fintype.card (InfinitePlace I.F) = I.f := by
  haveI := I.cm.totReal
  have h := NumberField.InfinitePlace.card_add_two_mul_card_eq_rank I.F
  rw [NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, mul_zero, add_zero] at h
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero, h]
  rfl

theorem card_integral_basis (I : AutInst) : Fintype.card (Free.ChooseBasisIndex ℤ (𝓞 I.E)) = 2 * I.f := by
  rw [← Module.finrank_eq_card_chooseBasisIndex, NumberField.RingOfIntegers.rank,
    ← Module.finrank_mul_finrank ℚ I.F I.E, I.cm.deg2]
  show Module.finrank ℚ I.F * 2 = 2 * Module.finrank ℚ I.F
  ring

theorem finrank_places_complex (I : AutInst) : finrank ℝ (InfinitePlace I.F → ℂ) = 2 * I.f := by
  rw [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
    card_infinite_places, smul_eq_mul]
  ring

def embeddingBasis (I : AutInst) : Basis (Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (InfinitePlace I.F → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank (embedding_linear_independent I)
    (by rw [card_integral_basis, finrank_places_complex])

theorem embeddingBasis_apply (I : AutInst) (i : Free.ChooseBasisIndex ℤ (𝓞 I.E)) :
    embeddingBasis I i = fun v => I.φ v (integralBasis I.E i) := by
  unfold embeddingBasis
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]

def complexToEuclidean {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ} (e : Fin 2 × ι ≃ Fin d) :
    (ι → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin d) :=
  ((Complex.basisOneI.smulTower (Pi.basisFun ℂ ι)).reindex e).equivFun.trans
    (EuclideanSpace.equiv (Fin d) ℝ).toLinearEquiv.symm

open scoped MatrixOrder in

theorem gram_factor_invertible {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (hC : Function.Injective C.mulVec) :
    ∃ R : Matrix (Fin j) (Fin j) ℂ, Cᴴ * C = Rᴴ * R ∧ R.det ≠ 0 := by
  have hpd : (Cᴴ * C).PosDef := Matrix.PosDef.conjTranspose_mul_self C hC
  have h0 : 0 ≤ Cᴴ * C := Matrix.nonneg_iff_posSemidef.mpr hpd.posSemidef
  refine ⟨CFC.sqrt (Cᴴ * C), ?_, ?_⟩
  · have hsa : (CFC.sqrt (Cᴴ * C))ᴴ = CFC.sqrt (Cᴴ * C) := by
      have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (Cᴴ * C))).star_eq
      rwa [Matrix.star_eq_conjTranspose] at this
    rw [hsa, CFC.sqrt_mul_sqrt_self _ h0]
  · intro hdet
    have hd : (Cᴴ * C).det ≠ 0 := (hpd.posSemidef.posDef_iff_det_ne_zero).mp hpd
    rw [← CFC.sqrt_mul_sqrt_self _ h0, Matrix.det_mul, hdet, zero_mul] at hd
    exact hd rfl

theorem norm_sq_eq_of_gram_eq {n j : ℕ} (C : Matrix (Fin n) (Fin j) ℂ) (R : Matrix (Fin j) (Fin j) ℂ)
    (h : Cᴴ * C = Rᴴ * R) (z : Fin j → ℂ) :
    ∑ i, ‖(C *ᵥ z) i‖ ^ 2 = ∑ k, ‖(R *ᵥ z) k‖ ^ 2 := by
  have key : ∀ {m : Type} [Fintype m] (M : Matrix m (Fin j) ℂ),
      ((∑ i, ‖(M *ᵥ z) i‖ ^ 2 : ℝ) : ℂ) = star z ⬝ᵥ ((Mᴴ * M) *ᵥ z) := by
    intro m _ M
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec]
    simp only [dotProduct, Pi.star_apply, Complex.ofReal_sum, Complex.ofReal_pow]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.star_def, Complex.conj_mul']
  apply Complex.ofReal_injective
  rw [key C, key R, h]

end Formalism.L2.SG.Pf.Tau
