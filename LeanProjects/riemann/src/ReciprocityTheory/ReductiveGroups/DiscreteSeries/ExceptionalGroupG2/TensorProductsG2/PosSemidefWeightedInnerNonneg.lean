import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.FormulaF
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.TensorProductsG2.ContinuousUnitaryMatrix
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExpInPPosDef
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.AnyDec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.DataGenSubIrred
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.ExistenceG2.HasGelfandCharSigLam

noncomputable section

open Finset MeasureTheory
open scoped ComplexOrder Matrix

namespace ReciprocityTheory.ChartRestriction.DS.G2

variable {n : ℕ}

def ob2TauF (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (ξ : Fin n → T.V) : Fin n → T.V :=
  fun c => ∑ d, (cond dual (star (S7.toMK k c d)) (S7.toMK k c d)) • T.op k (ξ d)

def ob2PsiCoef (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∑ c, inner ℂ (ξ c) (∑ d, (cond dual ((g⁻¹) d c) (g c d)) • Ψ g (ζ d))

def ob2SI {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ξ η : Fin n → V) : ℂ :=
  ∑ c, inner ℂ (ξ c) (η c)

theorem onb_sum_inner_independent {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) (F G : E →ₗ[ℂ] V) :
    ∑ j, inner ℂ (F (b j)) (G (b j)) = ∑ i, inner ℂ (F (c i)) (G (c i)) := by
  calc ∑ j, inner ℂ (F (b j)) (G (b j))
      = ∑ j, ∑ i, inner ℂ (c i) (b j) * inner ℂ (F (b j)) (G (c i)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        have e : G (b j) = ∑ i, inner ℂ (c i) (b j) • G (c i) := by
          conv_lhs => rw [← c.sum_repr' (b j)]
          simp only [map_sum, map_smul]
        rw [e, inner_sum]
        simp only [inner_smul_right]
    _ = ∑ i, ∑ j, inner ℂ (c i) (b j) * inner ℂ (F (b j)) (G (c i)) := Finset.sum_comm
    _ = ∑ i, inner ℂ (F (c i)) (G (c i)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have e : F (c i) = ∑ j, inner ℂ (b j) (c i) • F (b j) := by
          conv_lhs => rw [← b.sum_repr' (c i)]
          simp only [map_sum, map_smul]
        rw [e, sum_inner]
        simp only [inner_smul_left, inner_conj_symm]

theorem onb_sum_vector_inner_independent {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (b : OrthonormalBasis ι ℂ E) (c : OrthonormalBasis κ ℂ E) (F G : E →ₗ[ℂ] (Fin n → V)) :
    ∑ j, ob2SI (F (b j)) (G (b j)) = ∑ i, ob2SI (F (c i)) (G (c i)) := by
  unfold ob2SI
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ =>
    onb_sum_inner_independent b c ((LinearMap.proj d).comp F) ((LinearMap.proj d).comp G)

theorem onb_expand_vector_inner {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℂ E) (ι₀ : E →ₗ[ℂ] (Fin n → V)) (z : Fin n → V) (y : E) :
    ∑ i, starRingEnd ℂ (ob2SI (ι₀ (b i)) z) * inner ℂ (b i) y = ob2SI z (ι₀ y) := by
  conv_rhs => rw [← b.sum_repr' y]
  simp only [ob2SI, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, inner_sum, inner_smul_right,
    inner_conj_symm, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => by ring

theorem k_type_op_inner_preserved {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε) (x y : T.V) :
    inner ℂ (T.op k x) (T.op k y) = inner ℂ x y :=
  ContinuousLinearMap.inner_map_map_of_mem_unitary (T.τ k).2 x y

theorem k_matrix_conjTranspose_mul_self {ε : Fin n → Bool} (k : S7.KG ε) :
    (S7.toMK k)ᴴ * S7.toMK k = 1 := by
  have hk : S7.toMK k ∈ Kset ε := k.2
  have := (Matrix.mem_unitaryGroup_iff').1 hk.1
  simpa [Matrix.star_eq_conjTranspose] using this

theorem k_matrix_columns_orthonormal {ε : Fin n → Bool} (k : S7.KG ε) (e f : Fin n) :
    ∑ c, star (S7.toMK k c e) * S7.toMK k c f = if e = f then 1 else 0 := by
  have := congrFun (congrFun (k_matrix_conjTranspose_mul_self k) e) f
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

theorem k_twist_vector_inner_preserved (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) (k : S7.KG ε)
    (ξ η : Fin n → T.V) : ob2SI (ob2TauF dual T k ξ) (ob2TauF dual T k η) = ob2SI ξ η := by
  have hc : ∀ e f, ∑ c, starRingEnd ℂ (cond dual (star (S7.toMK k c e)) (S7.toMK k c e)) *
      cond dual (star (S7.toMK k c f)) (S7.toMK k c f) = if e = f then 1 else 0 := by
    intro e f
    cases dual
    · simpa using k_matrix_columns_orthonormal k e f
    · have h := congrArg star (k_matrix_columns_orthonormal k e f)
      simp only [star_sum, star_mul, star_star] at h
      simp only [cond_true, Complex.star_def, Complex.conj_conj] at h ⊢
      conv_lhs => arg 2; ext c; rw [mul_comm]
      rw [h]
      split_ifs <;> simp
  unfold ob2SI ob2TauF
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, k_type_op_inner_preserved]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h1 : ∀ e', ∑ c, cond dual (star (S7.toMK k c e)) (S7.toMK k c e) *
      ((starRingEnd ℂ) (cond dual (star (S7.toMK k c e')) (S7.toMK k c e')) * inner ℂ (ξ e') (η e)) =
      (if e' = e then 1 else 0) * inner ℂ (ξ e') (η e) := fun e' => by
    rw [← hc e' e, Finset.sum_mul]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl fun e' _ => h1 e']
  simp

def ob2B (dual : Bool) {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)) (g : Matrix (Fin n) (Fin n) ℂ) :
    (Fin n → V) →ₗ[ℂ] (Fin n → V) where
  toFun ζ c := ∑ d, oa1Phi dual g c d • Ψ g (ζ d)
  map_add' ζ ζ' := by funext c; simp [smul_add, Finset.sum_add_distrib]
  map_smul' a ζ := by funext c; simp [Finset.smul_sum, smul_comm a]

theorem psi_coef_eq_inner_twist (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) :
    ob2PsiCoef dual Ψ ξ ζ g = ob2SI ξ (ob2B dual Ψ g ζ) := rfl

theorem tensor_phi_k_mul (dual : Bool) {ε : Fin n → Bool} (k : S7.KG ε) (E : Matrix (Fin n) (Fin n) ℂ)
    (c d : Fin n) :
    oa1Phi dual (S7.toMK k * E) c d =
      ∑ e, cond dual (star (S7.toMK k c e)) (S7.toMK k c e) * oa1Phi dual E e d := by
  cases dual
  · simp [oa1Phi, Matrix.mul_apply]
  · have hki : (S7.toMK k)⁻¹ = (S7.toMK k)ᴴ := Matrix.inv_eq_left_inv (k_matrix_conjTranspose_mul_self k)
    simp only [oa1Phi, cond_true, Matrix.mul_inv_rev, hki, Matrix.mul_apply, Matrix.conjTranspose_apply]
    exact Finset.sum_congr rfl fun e _ => mul_comm _ _

theorem psi_twist_k_mul (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ)
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (k : S7.KG ε) (E : Matrix (Fin n) (Fin n) ℂ)
    (hΨ : Ψ (S7.toMK k * E) = T.op k * Ψ E) (ζ : Fin n → T.V) :
    ob2B dual Ψ (S7.toMK k * E) ζ = ob2TauF dual T k (ob2B dual Ψ E ζ) := by
  funext c
  simp only [ob2B, LinearMap.coe_mk, AddHom.coe_mk, ob2TauF, hΨ, tensor_phi_k_mul, ContinuousLinearMap.mul_apply,
    map_sum, map_smul, Finset.smul_sum, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]

open scoped MatrixOrder in
theorem posSemidef_weighted_inner_nonneg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) {R : V →L[ℂ] V} (hR : R.IsPositive)
    (u : Fin n → V) : 0 ≤ ∑ c, ∑ d, M c d * inner ℂ (u c) (R (u d)) := by
  obtain ⟨S, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM.nonneg
  have e : ∑ c, ∑ d, (star S * S) c d * inner ℂ (u c) (R (u d)) =
      ∑ e, inner ℂ (∑ c, S e c • u c) (R (∑ d, S e d • u d)) := by
    simp only [Matrix.mul_apply, Matrix.star_apply, map_sum, map_smul, sum_inner, inner_sum, inner_smul_left,
      inner_smul_right, Finset.sum_mul, Finset.mul_sum]
    conv_lhs => rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun e _ => ?_
    simp only [Complex.star_def]
    ring
  rw [e]
  exact Finset.sum_nonneg fun e _ => hR.inner_nonneg_right _

theorem vector_inner_smul_right {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ξ η : Fin n → V) (a : ℂ) :
    ob2SI ξ (a • η) = a * ob2SI ξ η := by
  simp [ob2SI, Finset.mul_sum]

theorem psi_pairing_eq_inner (dual : Bool) {ε : Fin n → Bool} {Λ Λ' : Fin n → ℝ} {T : S7.KType ε Λ} {T' : S7.KType ε Λ'}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (g : Matrix (Fin n) (Fin n) ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i))
        (ι₀ (stdOrthonormalBasis ℂ T'.V j)) g) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' g (stdOrthonormalBasis ℂ T'.V j))) =
    ∑ j, ob2SI (ob2B dual Ψ g (ι₀ (stdOrthonormalBasis ℂ T'.V j)))
      (ι₀ (Ψ' g (stdOrthonormalBasis ℂ T'.V j))) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [psi_coef_eq_inner_twist]
  exact onb_expand_vector_inner _ ι₀ _ _

theorem psi_twist_exp_positive (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) {Y : Matrix (Fin n) (Fin n) ℂ} (hY : inP ε Y)
    (hR : (Ψ (NormedSpace.exp Y)).IsPositive) (u : Fin n → T.V) :
    0 ≤ ob2SI (ob2B dual Ψ (NormedSpace.exp Y) u) u := by
  set E := NormedSpace.exp Y with hEdef
  have hE : E.PosDef := S7.exp_noncompactPart_posDef hY
  set M : Matrix (Fin n) (Fin n) ℂ := cond dual (E⁻¹)ᵀ E with hMdef
  have hM : M.PosSemidef := by
    cases dual
    · exact hE.posSemidef
    · exact hE.inv.transpose.posSemidef
  have hφ : ∀ c d, oa1Phi dual E c d = M c d := by
    intro c d; cases dual <;> rfl
  have h0 := posSemidef_weighted_inner_nonneg hM hR u
  have e : ob2SI (ob2B dual Ψ E u) u = star (∑ c, ∑ d, M c d * inner ℂ (u c) (Ψ E (u d))) := by
    simp only [ob2SI, ob2B, LinearMap.coe_mk, AddHom.coe_mk, hφ, sum_inner, inner_smul_left, star_sum, star_mul',
      Complex.star_def, inner_conj_symm]
  rw [e]
  exact star_nonneg_iff.mpr h0

theorem k_matrix_of_one {ε : Fin n → Bool} : S7.toMK (1 : S7.KG ε) = 1 := rfl

theorem k_type_op_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : S7.KType ε Λ) : T.op 1 = 1 := by
  simp [S7.KType.op]

theorem psi_pairing_nonneg (dual : Bool) {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)}
    {T' : S7.KType ε (lowK ε lam')}
    {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}
    (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V))
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ob2TauF dual T k (ι₀ v))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) :
    0 ≤ ∑ i, ∑ j, starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i))
        (ι₀ (stdOrthonormalBasis ℂ T'.V j)) g) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' g (stdOrthonormalBasis ℂ T'.V j)) := by
  rw [psi_pairing_eq_inner]
  obtain ⟨k0, hk0, Y, hY, rfl⟩ := polar_UJ (show g ∈ UJset ε from hg)
  obtain ⟨k, rfl⟩ := ffa_Kset hk0
  have hE : inUJ ε (NormedSpace.exp Y) := by
    have h1 : NormedSpace.exp Y ∈ UJset ε := by simpa using exp_smul_mem_UJset hY.1 1
    exact h1
  have hΨ : Ψ (S7.toMK k * NormedSpace.exp Y) = T.op k * Ψ (NormedSpace.exp Y) := by
    have := hP.1 k 1 _ hE
    rwa [k_matrix_of_one, Matrix.mul_one, k_type_op_one, mul_one] at this
  have hΨ' : Ψ' (S7.toMK k * NormedSpace.exp Y) = T'.op k * Ψ' (NormedSpace.exp Y) := by
    have := hP'.1 k 1 _ hE
    rwa [k_matrix_of_one, Matrix.mul_one, k_type_op_one, mul_one] at this
  set b := stdOrthonormalBasis ℂ T'.V
  set E := NormedSpace.exp Y
  have step : ∀ j, ob2SI (ob2B dual Ψ (S7.toMK k * E) (ι₀ (b j))) (ι₀ (Ψ' (S7.toMK k * E) (b j))) =
      ob2SI (ob2B dual Ψ E (ι₀ (b j))) (ι₀ (Ψ' E (b j))) := by
    intro j
    rw [psi_twist_k_mul dual T Ψ k E hΨ, hΨ', ContinuousLinearMap.mul_apply, hK, k_twist_vector_inner_preserved]
  rw [Finset.sum_congr rfl fun j _ => step j]
  have hQ := (hpos' Y hY).toLinearMap
  have hs := hQ.isSymmetric
  set c := hs.eigenvectorBasis rfl
  have h := onb_sum_vector_inner_independent b c ((ob2B dual Ψ E).comp ι₀) (ι₀.comp (Ψ' E : T'.V →ₗ[ℂ] T'.V))
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe] at h
  rw [h]
  refine Finset.sum_nonneg fun i _ => ?_
  have hc := hs.apply_eigenvectorBasis rfl i
  simp only [ContinuousLinearMap.coe_coe] at hc
  rw [hc, map_smul, vector_inner_smul_right]
  exact mul_nonneg (Complex.zero_le_real.mpr (hQ.nonneg_eigenvalues rfl i)) (psi_twist_exp_positive dual Ψ hY (hpos Y hY) _)

end ReciprocityTheory.ChartRestriction.DS.G2
