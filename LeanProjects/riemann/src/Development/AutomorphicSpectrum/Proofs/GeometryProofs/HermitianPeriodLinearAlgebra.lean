import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannFormPeriodDeterminantBoundStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.LinFlat

open Matrix
open scoped ComplexOrder

local notation "HF" => ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm

theorem hermForm_sum_left {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    HF Hm (∑ i, c i • V i) w = ∑ i, c i * HF Hm (V i) w := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, sum_dotProduct, smul_dotProduct]

theorem hermForm_sum_right {g : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (c : κ → ℂ) (V : κ → Fin g → ℂ) (z : Fin g → ℂ) :
    HF Hm z (∑ i, c i • V i) = ∑ i, star (c i) * HF Hm z (V i) := by
  simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_sum, Matrix.mulVec_sum, dotProduct_sum,
    Matrix.mulVec_smul, dotProduct_smul]

theorem star_hermForm {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : star (HF Hm z w) = HF Hm w z := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm
  rw [← star_dotProduct_star, Matrix.star_mulVec, star_star, hH.eq, Matrix.dotProduct_mulVec]

theorem coef_unique {r g : ℕ} {V : Fin r → Fin g → ℂ} (hV : LinearIndependent ℂ V)
    (c d : Fin r → ℂ) (h : ∑ i, c i • V i = ∑ i, d i • V i) : c = d := by
  have := Fintype.linearIndependent_iff.mp hV (fun i => c i - d i)
    (by simp [sub_smul, Finset.sum_sub_distrib, h])
  funext i
  exact sub_eq_zero.mp (this i)

theorem exists_rightInverse {p : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix (Fin p) κ ℂ) (hA : A.rank = p) : ∃ C : Matrix (Fin p) κ ℂ, A * Cᵀ = 1 := by
  have hs : Function.Surjective A.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using hA
  choose c hc using fun a : Fin p => hs (Pi.single a 1)
  refine ⟨Matrix.of c, ?_⟩
  ext a b
  have := congrFun (hc b) a
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.one_apply, Pi.single_apply,
    eq_comm] using this

theorem eq_zero_of_vecMul_eq_zero {q : ℕ} {κ : Type*} [Fintype κ]
    (F : Matrix (Fin q) κ ℂ) (hF : F.rank = q) (y : Fin q → ℂ) (hy : y ᵥ* F = 0) : y = 0 := by
  have hFt : Fᵀ.rank = q := by rw [Matrix.rank_transpose, hF]
  have hk : LinearMap.ker Fᵀ.mulVecLin = ⊥ := by
    have h0 := LinearMap.finrank_range_add_finrank_ker Fᵀ.mulVecLin
    have h1 : Module.finrank ℂ (LinearMap.range Fᵀ.mulVecLin) = q := hFt
    rw [h1] at h0
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h0
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hm : y ∈ LinearMap.ker Fᵀ.mulVecLin := by
    simp [Matrix.mulVec_transpose, hy]
  rw [hk] at hm
  simpa using hm

theorem det_fromRows_ne_zero {p q : ℕ} (A C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (hAF : A * Fᵀ = 0) (hF : F.rank = q)
    (hC : A * Cᵀ = 1) : (fromRows C F).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr h0
  have hCA : C * Aᵀ = 1 := by
    have := congrArg Matrix.transpose hC
    simpa [Matrix.transpose_mul] using this
  have hFA : F * Aᵀ = 0 := by
    have := congrArg Matrix.transpose hAF
    simpa [Matrix.transpose_mul] using this
  have h1 : (v ∘ Sum.inl) ᵥ* C + (v ∘ Sum.inr) ᵥ* F = 0 := by
    rw [← hv0]
    ext n
    simp [Matrix.vecMul, dotProduct, Fintype.sum_sum_type]
  have hx : v ∘ Sum.inl = 0 := by
    have := congrArg (fun u => u ᵥ* Aᵀ) h1
    simpa [Matrix.add_vecMul, Matrix.vecMul_vecMul, hCA, hFA] using this
  have hy : v ∘ Sum.inr = 0 := by
    apply eq_zero_of_vecMul_eq_zero F hF
    simpa [hx] using h1
  apply hv
  ext (i | j)
  · exact congrFun hx i
  · exact congrFun hy j

theorem det_fromRows_eq {p q : ℕ} (A C C' : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (F : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (hAF : A * Fᵀ = 0) (hF : F.rank = q)
    (hC : A * Cᵀ = 1) (hC' : A * C'ᵀ = 1) : (fromRows C' F).det = (fromRows C F).det := by
  have hdet := det_fromRows_ne_zero A C F hAF hF hC
  have hU : IsUnit (fromRows C F).det := isUnit_iff_ne_zero.mpr hdet
  have hCA : C * Aᵀ = 1 := by
    have := congrArg Matrix.transpose hC
    simpa [Matrix.transpose_mul] using this
  have hCA' : C' * Aᵀ = 1 := by
    have := congrArg Matrix.transpose hC'
    simpa [Matrix.transpose_mul] using this
  have hFA : F * Aᵀ = 0 := by
    have := congrArg Matrix.transpose hAF
    simpa [Matrix.transpose_mul] using this
  obtain ⟨Z₁, Z₂, hZ⟩ : ∃ (Z₁ : Matrix (Fin p) (Fin p) ℂ) (Z₂ : Matrix (Fin p) (Fin q) ℂ),
      Z₁ * C + Z₂ * F = C' := by
    refine ⟨(C' * (fromRows C F)⁻¹).toCols₁, (C' * (fromRows C F)⁻¹).toCols₂, ?_⟩
    rw [← fromCols_mul_fromRows, fromCols_toCols, Matrix.nonsing_inv_mul_cancel_right _ _ hU]
  have hZ1 : Z₁ = 1 := by
    have := congrArg (fun M => M * Aᵀ) hZ
    simpa [Matrix.add_mul, Matrix.mul_assoc, hCA, hCA', hFA] using this
  subst hZ1
  have hfac : fromRows C' F = fromBlocks 1 Z₂ 0 1 * fromRows C F := by
    rw [fromBlocks_mul_fromRows, hZ]
    simp
  rw [hfac, Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

theorem gram_expand {g r : ℕ} {κ : Type*} [Fintype κ] (Hm : Matrix (Fin g) (Fin g) ℂ)
    (V : Fin r → Fin g → ℂ) (A : Matrix (Fin r) κ ℂ) (m n : κ) :
    (Aᵀ * (Matrix.of fun a b => HF Hm (V a) (V b)) * A.map star) m n =
      HF Hm (∑ i, A i m • V i) (∑ i, A i n • V i) := by
  rw [hermForm_sum_left]
  simp_rw [hermForm_sum_right]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.map_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_posDef {r g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (HF Hm z z).re)
    (V : Fin r → Fin g → ℂ) (hV : LinearIndependent ℂ V) :
    (Matrix.of fun a b => HF Hm (V a) (V b)).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext a b
    simp [Matrix.conjTranspose_apply, star_hermForm hH]
  · have hy : ∑ a, star (x a) • V a ≠ 0 := by
      intro h0
      have := Fintype.linearIndependent_iff.mp hV _ h0
      apply hx
      ext a
      simpa using this a
    have key : star x ⬝ᵥ ((Matrix.of fun a b => HF Hm (V a) (V b)) *ᵥ x) =
        HF Hm (∑ a, star (x a) • V a) (∑ a, star (x a) • V a) := by
      rw [hermForm_sum_left]
      simp_rw [hermForm_sum_right]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.of_apply, Finset.mul_sum, star_star]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [key, Complex.pos_iff]
    refine ⟨hpos _ hy, ?_⟩
    have hs := star_hermForm hH (∑ a, star (x a) • V a) (∑ a, star (x a) • V a)
    exact (Complex.conj_eq_iff_im.mp hs).symm

theorem reindexed {p q : ℕ} (A : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ)
    (B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)
    (H₁ : Matrix (Fin p) (Fin p) ℂ) (H₂ : Matrix (Fin q) (Fin q) ℂ)
    (h₁ : H₁.PosDef) (h₂ : H₂.PosDef) (hS : S.det ≠ 0)
    (hrel : Aᵀ * H₁ * A.map star - (Bᵀ * H₂ * B.map star)ᵀ = (2 * Complex.I) • S) :
    A * ((Sᵀ)⁻¹ * Bᵀ) = 0 ∧ A.rank = p ∧ ((Sᵀ)⁻¹ * Bᵀ).rank = q := by
  let e : Fin q ⊕ Fin p ≃ Fin p ⊕ Fin q := Equiv.sumComm _ _
  have hrel' : (A.submatrix id e)ᵀ * H₁ * (A.submatrix id e).map star -
      ((B.submatrix id e)ᵀ * H₂ * (B.submatrix id e).map star)ᵀ =
      (2 * Complex.I) • S.submatrix e e := by
    ext m n
    have := congrFun (congrFun hrel (e m)) (e n)
    simpa [Matrix.mul_apply] using this
  have hdet : (S.submatrix e e).det ≠ 0 := by
    rwa [Matrix.det_submatrix_equiv_self]
  obtain ⟨t₁, t₂, t₃, -⟩ := GlobalTheory.T.riemann_form_period_determinant p q (A.submatrix id e) (B.submatrix id e)
    (S.submatrix e e) H₁ H₂ h₁ h₂ hdet hrel'
  have hG : ((S.submatrix e e)ᵀ)⁻¹ * (B.submatrix id e)ᵀ = ((Sᵀ)⁻¹ * Bᵀ).submatrix e id := by
    rw [Matrix.transpose_submatrix, Matrix.transpose_submatrix, Matrix.inv_submatrix_equiv,
      Matrix.submatrix_mul_equiv]
  rw [hG] at t₁ t₃
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv] at t₁
    simpa using t₁
  · have := Matrix.rank_submatrix A (Equiv.refl _) e
    simpa [t₂] using this.symm
  · have := Matrix.rank_submatrix ((Sᵀ)⁻¹ * Bᵀ) e (Equiv.refl _)
    simpa [t₃] using this.symm

theorem flatSection_linearAlgebra : ∀ (p q g : ℕ) (T T' : (Fin g → ℂ) → (Fin g → ℂ)) (V : Fin p → Fin g → ℂ) (W : Fin q → Fin g → ℂ) (π : Fin p ⊕ Fin q → Fin g → ℂ) (S : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) (Hm : Matrix (Fin g) (Fin g) ℂ), IsLinearMap ℂ T → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → S.det ≠ 0 → LinearIndependent ℂ V → LinearIndependent ℂ W → (∀ n, T (π n) ∈ Submodule.span ℂ (Set.range V)) → (∀ n, T' (π n) ∈ Submodule.span ℂ (Set.range W)) → (∀ m n, hermForm Hm (T (π m)) (T (π n)) - star (hermForm Hm (T' (π m)) (T' (π n))) = 2 * Complex.I * S m n) → ∃! x : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × Matrix (Fin q) (Fin p ⊕ Fin q) ℂ × ℂ, (∀ n, T' (π n) = ∑ j, x.2.1 j n • W j) ∧ (∀ j n, ∑ m, x.1 j m * S m n = x.2.1 j n) ∧ x.2.2 ≠ 0 ∧ (∃ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, ∀ a, T (∑ m, C a m • π m) = V a) ∧ ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ, (∀ a, T (∑ m, C a m • π m) = V a) → (Matrix.fromRows C x.1).det = x.2.2 := by
  intro p q g T T' V W π S Hm hT hH hpos hS hV hW hTV hTW hrel
  choose a ha using fun n => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hTV n)
  choose b hb using fun n => (Submodule.mem_span_range_iff_exists_fun ℂ).mp (hTW n)
  let A : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ := Matrix.of fun i n => a n i
  let B : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ := Matrix.of fun j n => b n j
  have hA : ∀ n, ∑ i, A i n • V i = T (π n) := ha
  have hB : ∀ n, ∑ j, B j n • W j = T' (π n) := hb
  clear_value A B
  have hrel' : Aᵀ * (Matrix.of fun i j => HF Hm (V i) (V j)) * A.map star -
      (Bᵀ * (Matrix.of fun i j => HF Hm (W i) (W j)) * B.map star)ᵀ = (2 * Complex.I) • S := by
    ext m n
    rw [Matrix.sub_apply, Matrix.transpose_apply, gram_expand, gram_expand, hA, hA, hB, hB,
      ← star_hermForm hH (T' (π m)) (T' (π n)), hrel m n]
    simp
  obtain ⟨h0, hrA, hrG⟩ := reindexed A B S _ _ (gram_posDef Hm hH hpos V hV)
    (gram_posDef Hm hH hpos W hW) hS hrel'
  have hSu : IsUnit S.det := isUnit_iff_ne_zero.mpr hS
  have hSt : IsUnit (Sᵀ).det := by rwa [Matrix.det_transpose]
  let Fm : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ := ((Sᵀ)⁻¹ * Bᵀ)ᵀ
  have hAF : A * Fmᵀ = 0 := by simpa [Fm] using h0
  have hrF : Fm.rank = q := (Matrix.rank_transpose _).trans hrG
  have hFS : Fm * S = B := by
    have h1 : Sᵀ * ((Sᵀ)⁻¹ * Bᵀ) = Bᵀ := Matrix.mul_nonsing_inv_cancel_left _ _ hSt
    have h2 := congrArg Matrix.transpose h1
    simpa [Matrix.transpose_mul, Fm] using h2
  clear_value Fm
  have hexp : ∀ (C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ) (i : Fin p),
      T (∑ m, C i m • π m) = ∑ k, (A * Cᵀ) k i • V k := by
    intro C i
    have h1 : T (∑ m, C i m • π m) = ∑ m, C i m • T (π m) := by
      have := map_sum (hT.mk' T) (fun m => C i m • π m) Finset.univ
      simpa [hT.map_smul] using this
    rw [h1]
    simp_rw [← hA, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp [mul_comm]
  have hlift : ∀ C : Matrix (Fin p) (Fin p ⊕ Fin q) ℂ,
      (∀ i, T (∑ m, C i m • π m) = V i) ↔ A * Cᵀ = 1 := by
    intro C
    constructor
    · intro h
      ext k i
      have := coef_unique hV (fun k => (A * Cᵀ) k i) (fun k => (1 : Matrix _ _ ℂ) k i)
        (by rw [← hexp, h]; simp [Matrix.one_apply])
      exact congrFun this k
    · intro h i
      rw [hexp, h]
      simp [Matrix.one_apply]
  obtain ⟨C₀, hC₀⟩ := exists_rightInverse A hrA
  refine ⟨(Fm, B, (fromRows C₀ Fm).det), ⟨?_, ?_, ?_, ⟨C₀, (hlift C₀).mpr hC₀⟩, ?_⟩, ?_⟩
  · intro n
    exact (hB n).symm
  · intro j n
    show ∑ m, Fm j m * S m n = B j n
    rw [← hFS, Matrix.mul_apply]
  · exact det_fromRows_ne_zero A C₀ Fm hAF hrF hC₀
  · intro C hC
    exact det_fromRows_eq A C₀ C Fm hAF hrF hC₀ ((hlift C).mp hC)
  · rintro ⟨F', B', d'⟩ ⟨h1, h2, -, -, h5⟩
    simp only at h1 h2 h5
    have hBB : B' = B := by
      ext j n
      have := coef_unique hW (fun j => B' j n) (fun j => B j n) (by rw [← h1 n, hB n])
      exact congrFun this j
    subst hBB
    have hFF : F' * S = Fm * S := by
      rw [hFS]
      ext j n
      rw [Matrix.mul_apply]
      exact h2 j n
    have hF' : F' = Fm := by
      have := congrArg (fun M => M * S⁻¹) hFF
      simpa [Matrix.mul_nonsing_inv_cancel_right _ _ hSu] using this
    subst hF'
    have hd := h5 C₀ ((hlift C₀).mpr hC₀)
    simp only [Prod.mk.injEq, true_and]
    exact hd.symm

end GlobalTheory.CompanionTheory.Ar.LinFlat
