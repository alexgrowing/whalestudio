import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.HermFrame

open Matrix

section Exists

variable {m l n : Type} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
  [DecidableEq n]

open scoped MatrixOrder in

theorem exists_chg_eq_one {H : Matrix n n ℂ} (hH : H.PosDef) :
    ∃ R : Matrix n n ℂ, IsUnit R.det ∧ chg R H = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.transpose.posSemidef.nonneg
  have hd : Hᵀ.det ≠ 0 := hH.transpose.det_pos.ne'
  have hu : IsUnit B.det := by
    rw [hB, det_mul] at hd
    exact (right_ne_zero_of_mul hd).isUnit
  refine ⟨B⁻¹, isUnit_nonsing_inv_det _ hu, ?_⟩
  apply transpose_injective
  have e : (chg B⁻¹ H)ᵀ = (B⁻¹)ᴴ * Hᵀ * B⁻¹ := by
    simp only [chg, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e, hB, star_eq_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc, Matrix.mul_assoc,
    mul_nonsing_inv _ hu, Matrix.mul_one,
    nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hu.star), transpose_one]

theorem exists_chg_fromBlocks_eq_one {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hH : H.PosDef)
    {R : Matrix l l ℂ} (hR : chg R (quotGram H) = 1) :
    ∃ (A : Matrix m m ℂ) (B : Matrix m l ℂ), IsUnit A.det ∧ chg (fromBlocks A B 0 R) H = 1 := by
  obtain ⟨A, hA, hA1⟩ := exists_chg_eq_one (posDef_subGram hH)
  have hs : IsUnit H.toBlocks₁₁.det := (posDef_subGram hH).det_pos.ne'.isUnit
  set B : Matrix m l ℂ := -(orthCoeff H * R) with hBdef
  have hBt : Bᵀ = -(Rᵀ * (H.toBlocks₂₁ * H.toBlocks₁₁⁻¹)) := by
    simp [hBdef, orthCoeff, transpose_mul, transpose_nonsing_inv]
  have hW : Bᵀ * H.toBlocks₁₁ + Rᵀ * H.toBlocks₂₁ = 0 := by
    rw [hBt, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hs,
      Matrix.mul_one, neg_add_cancel]
  have hZ : Bᵀ * H.toBlocks₁₂ + Rᵀ * H.toBlocks₂₂ = Rᵀ * quotGram H := by
    rw [hBt, quotGram, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    abel
  have hherm : (chg (fromBlocks A B 0 R) H).IsHermitian := by
    have := isHermitian_mul_mul_conjTranspose (fromBlocks A B 0 R)ᵀ hH.isHermitian
    rwa [show (fromBlocks A B 0 R)ᵀᴴ = (fromBlocks A B 0 R)ᴴᵀ from rfl] at this
  have e21 : (chg (fromBlocks A B 0 R) H).toBlocks₂₁ = 0 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₂₁, hW, Matrix.zero_mul]
  have e12 : (chg (fromBlocks A B 0 R) H).toBlocks₁₂ = 0 := by
    have := conjTranspose_toBlocks₁₂ hherm
    rw [e21] at this
    simpa using congrArg conjTranspose this
  have e11 : (chg (fromBlocks A B 0 R) H).toBlocks₁₁ = 1 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₁₁]; exact hA1
  have e22 : (chg (fromBlocks A B 0 R) H).toBlocks₂₂ = 1 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₂₂, hW, hZ, Matrix.zero_mul, zero_add]; exact hR
  refine ⟨A, B, hA, ?_⟩
  rw [← fromBlocks_toBlocks (chg (fromBlocks A B 0 R) H), e11, e12, e21, e22, fromBlocks_one]

theorem exists_triangular_chg_eq_one {H : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} (hH : H.PosDef) :
    ∃ (A₁ : Matrix m m ℂ) (B : Matrix m (l ⊕ n) ℂ) (A₂ : Matrix l l ℂ) (C : Matrix l n ℂ)
      (A₃ : Matrix n n ℂ), IsUnit A₁.det ∧ IsUnit A₂.det ∧ IsUnit A₃.det ∧
        chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) H = 1 := by
  have hQ := posDef_quotGram hH
  obtain ⟨A₃, h₃, e₃⟩ := exists_chg_eq_one (posDef_quotGram hQ)
  obtain ⟨A₂, C, h₂, e₂⟩ := exists_chg_fromBlocks_eq_one hQ e₃
  obtain ⟨A₁, B, h₁, e₁⟩ := exists_chg_fromBlocks_eq_one hH e₂
  exact ⟨A₁, B, A₂, C, A₃, h₁, h₂, h₃, e₁⟩

theorem chg_submatrix_first (A₁ : Matrix m m ℂ) (B : Matrix m (l ⊕ n) ℂ) (A₂ : Matrix l l ℂ)
    (C : Matrix l n ℂ) (A₃ : Matrix n n ℂ) (H : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ) :
    (chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) H).submatrix (Sum.map id Sum.inl)
        (Sum.map id Sum.inl) =
      chg (fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
        (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) := by
  set J : Matrix (m ⊕ (l ⊕ n)) (m ⊕ l) ℂ :=
    (1 : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ).submatrix id (Sum.map id Sum.inl) with hJ
  have h0 : ∀ T : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ,
      chg (T.submatrix id (Sum.map id Sum.inl)) H =
        (chg T H).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := fun T => by
    have := chg_submatrix T H (Equiv.refl _) (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n))
    simpa using this
  have h1 : H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) = chg J H := by
    rw [hJ, h0, chg_one]
  have h2 : (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)).submatrix id (Sum.map id Sum.inl)
      = J * fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂ := by
    ext (a | a | a) (b | b) <;>
      simp [hJ, mul_apply, Fintype.sum_sum_type, one_apply]
  rw [h1, chg_chg, ← h2, h0]

end Exists

section Forms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l n : Type} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m]
  [DecidableEq l] [DecidableEq n]

theorem extTrace_eq_sum_of_eq_one {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (h1 : K z = 1) (ξ η : E) :
    extTrace K z ξ η = kappa * ∑ a : m, ∑ b : l,
      mdel K z ξ (Sum.inl a) (Sum.inr b) * star (mdel K z η (Sum.inl a) (Sum.inr b)) := by
  have hs : subGram (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ) = 1 := by
    ext a b; simp [subGram, toBlocks₁₁, one_apply]
  have hq : quotGram (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ) = 1 := by
    have e1 : (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ).toBlocks₂₁ = 0 := by
      ext a b; simp [toBlocks₂₁, one_apply]
    have e2 : (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ).toBlocks₂₂ = 1 := by
      ext a b; simp [toBlocks₂₂, one_apply]
    rw [quotGram, e1, e2]; simp
  have hb : ∀ ξ, secondForm K z ξ = (mdel K z ξ).toBlocks₁₂ᵀ := fun ξ => by
    rw [secondForm_eq, conn, h1, transpose_one, inv_one, Matrix.one_mul]; rfl
  rw [extTrace_eq h hp, secondFormAdj, h1, hs, hq, hb, hb, adj]
  simp only [transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, trace, diag_apply, mul_apply,
    transpose_apply, conjTranspose_apply, toBlocks₁₂, of_apply]
  rw [Finset.sum_comm]

theorem mdel_quotGram_of_eq_one {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (h1 : K z = 1) (ξ : E) :
    mdel (fun x => quotGram (K x)) z ξ = (mdel K z ξ).toBlocks₂₂ := by
  have hu : IsUnit (subGram (K z)).det := by
    have : subGram (K z) = 1 := by rw [h1]; ext a b; simp [subGram, toBlocks₁₁, one_apply]
    rw [this]; simp
  have e12 : (K z).toBlocks₁₂ = 0 := by rw [h1]; ext a b; simp [toBlocks₁₂, one_apply]
  have e21 : (K z).toBlocks₂₁ = 0 := by rw [h1]; ext a b; simp [toBlocks₂₁, one_apply]
  have h21 : MContDiffAt 1 (fun x => (K x).toBlocks₂₁) z := h.submatrix Sum.inr Sum.inl
  have h12 : MContDiffAt 1 (fun x => (K x).toBlocks₁₂) z := h.submatrix Sum.inl Sum.inr
  have h22 : MContDiffAt 1 (fun x => (K x).toBlocks₂₂) z := h.submatrix Sum.inr Sum.inr
  have h11 : MContDiffAt 1 (fun x => (K x).toBlocks₁₁⁻¹) z := h.subGram.inv hu
  have hP := h21.mul h11
  have e : (fun x => quotGram (K x)) =
      fun x => (K x).toBlocks₂₂ + -((K x).toBlocks₂₁ * (K x).toBlocks₁₁⁻¹ * (K x).toBlocks₁₂) := by
    funext x; rw [quotGram, sub_eq_add_neg]
  rw [e, mdel_add h22 (hP.mul h12).neg, mdel_neg, mdel_mul hP h12, e12, e21]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, neg_zero]
  rfl

theorem extTrace_add_of_eq_one {K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (h1 : K z = 1) (ξ η : E) :
    extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ξ η +
        extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ξ η =
      extTrace K z ξ η + extTrace (fun x => quotGram (K x)) z ξ η := by
  have hf : Function.Injective (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n)) :=
    Function.injective_id.sumMap Sum.inl_injective
  have he := (Equiv.sumAssoc m l n).injective
  have hsub : subGram (K z) = 1 := by rw [h1]; ext a b; simp [subGram, toBlocks₁₁, one_apply]
  have hu : IsUnit (subGram (K z)).det := by rw [hsub]; simp
  have hq : quotGram (K z) = 1 := by
    have e1 : (K z).toBlocks₂₁ = 0 := by rw [h1]; ext a b; simp [toBlocks₂₁, one_apply]
    have e2 : (K z).toBlocks₂₂ = 1 := by rw [h1]; ext a b; simp [toBlocks₂₂, one_apply]
    rw [quotGram, e1, e2]; simp
  rw [extTrace_eq_sum_of_eq_one (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix hf)
      (by rw [h1]; exact submatrix_one _ hf),
    extTrace_eq_sum_of_eq_one (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix he)
      (by rw [h1]; exact submatrix_one _ he),
    extTrace_eq_sum_of_eq_one h hp h1,
    extTrace_eq_sum_of_eq_one (h.quotGram hu) (hp.mono fun x hx => posDef_quotGram hx) hq,
    mdel_quotGram_of_eq_one h h1, mdel_quotGram_of_eq_one h h1]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, mdel_apply, submatrix_apply,
    Sum.map_inl, Sum.map_inr, id, Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr,
    Equiv.sumAssoc_apply_inr, toBlocks₂₂, of_apply]
  ring

variable {K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} {z : E}

theorem extTrace_add_chg (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef)
    {A₁ : Matrix m m ℂ} (B : Matrix m (l ⊕ n) ℂ) {A₂ : Matrix l l ℂ} (C : Matrix l n ℂ)
    {A₃ : Matrix n n ℂ} (h₁ : IsUnit A₁.det) (h₂ : IsUnit A₂.det) (h₃ : IsUnit A₃.det) :
    let A := fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)
    extTrace (fun x => (chg A (K x)).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z =
        extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ∧
      extTrace (fun x => (chg A (K x)).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z =
        extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ∧
      extTrace (fun x => chg A (K x)) z = extTrace K z ∧
      extTrace (fun x => quotGram (chg A (K x))) z = extTrace (fun x => quotGram (K x)) z := by
  intro A
  have hf : Function.Injective (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n)) :=
    Function.injective_id.sumMap Sum.inl_injective
  have he := (Equiv.sumAssoc m l n).injective
  have hA₂ : IsUnit (fromBlocks A₂ C 0 A₃).det := by
    rw [det_fromBlocks_zero₂₁]; exact h₂.mul h₃
  have hA : IsUnit A.det := by
    simp only [A]; rw [det_fromBlocks_zero₂₁]; exact h₁.mul hA₂
  have hs : IsUnit (subGram (K z)).det := (posDef_subGram hp.self_of_nhds).det_pos.ne'.isUnit
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (fun x => (chg A (K x)).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) =
        fun x => chg (fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
          ((K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) :=
      funext fun x => chg_submatrix_first A₁ B A₂ C A₃ (K x)
    rw [e]
    refine extTrace_chg (A := fun _ => fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
      (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix hf) (mContDiffAt_const _)
      (by rw [det_fromBlocks_zero₂₁]; exact h₁.mul h₂) (fun η => mdbar_const _ _ _)
      (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)
  · have e : (fun x => (chg A (K x)).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) =
        fun x => chg (A.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))
          ((K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) :=
      funext fun x => (chg_submatrix A (K x) (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)).symm
    rw [e]
    refine extTrace_chg (A := fun _ => A.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))
      (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix he) (mContDiffAt_const _)
      (by rw [det_submatrix_equiv_self]; exact hA) (fun η => mdbar_const _ _ _)
      (.of_forall fun _ => ?_)
    ext a (b | b) <;> simp [A, toBlocks₂₁]
  · exact extTrace_chg (A := fun _ => A) h hp (mContDiffAt_const _) hA
      (fun η => mdbar_const _ _ _) (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)
  · rw [extTrace_congr (K' := fun x => chg (fromBlocks A₂ C 0 A₃) (quotGram (K x)))
      (hp.mono fun x hx => quotGram_chg B _ h₁ (posDef_subGram hx).det_pos.ne'.isUnit)]
    exact extTrace_chg (A := fun _ => fromBlocks A₂ C 0 A₃) (h.quotGram hs)
      (hp.mono fun x hx => posDef_quotGram hx) (mContDiffAt_const _) hA₂
      (fun η => mdbar_const _ _ _) (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)

end Forms

theorem extTrace_add_extTrace :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
      (m l n : Type) [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
      [DecidableEq n] (K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ) (z ξ η : E),
      MContDiffAt 1 K z → (∀ᶠ x in 𝓝 z, (K x).PosDef) →
      extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ξ η +
          extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ξ η =
        extTrace K z ξ η + extTrace (fun x => quotGram (K x)) z ξ η := by
  intro E _ _ _ _ m l n _ _ _ _ _ _ K z ξ η h hp
  obtain ⟨A₁, B, A₂, C, A₃, h₁, h₂, h₃, e⟩ := exists_triangular_chg_eq_one hp.self_of_nhds
  obtain ⟨t₁, t₂, t₃, t₄⟩ := extTrace_add_chg h hp B C h₁ h₂ h₃
  have hA : IsUnit (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)).det := by
    rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]; exact h₁.mul (h₂.mul h₃)
  have := extTrace_add_of_eq_one (K := fun x => chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) (K x))
    (((mContDiffAt_const _).mul h).mul (mContDiffAt_const _))
    (hp.mono fun x hx => posDef_chg ((isUnit_iff_isUnit_det _).2 hA) hx) e ξ η
  rwa [t₁, t₂, t₃, t₄] at this

end GlobalTheory.HermFrame
