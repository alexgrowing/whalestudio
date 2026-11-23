import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace PositivityTheory.Xgf

section Ultra

variable {A : Type} [NormedField A] [IsUltrametricDist A]

theorem norm_sign_smul {I : Type} [Fintype I] [DecidableEq I] (σ : Equiv.Perm I) (x : A) :
    ‖Equiv.Perm.sign σ • x‖ = ‖x‖ := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h, Units.smul_def]

theorem ultrametric_norm_sum_lt {ι : Type} (s : Finset ι) (f : ι → A) {C : ℝ} (hC : 0 < C) (h : ∀ i ∈ s, ‖f i‖ < C) :
    ‖∑ i ∈ s, f i‖ < C := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simpa using hC
  obtain ⟨i, hi, hle⟩ := IsUltrametricDist.exists_norm_finsetSum_le_of_nonempty hs f
  exact hle.trans_lt (h i hi)

theorem ultrametric_norm_prod_sub_lt {ι : Type} (s : Finset ι) (a b : ι → A) {r : ℝ} (hr : 0 < r) (ha : ∀ i ∈ s, ‖a i‖ ≤ r)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ r) (hab : ∀ i ∈ s, ‖a i - b i‖ < r) :
    ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ < r ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.card_insert_of_notMem hj]
    have ih' := ih (fun i hi => ha i (Finset.mem_insert_of_mem hi)) (fun i hi => hb i (Finset.mem_insert_of_mem hi))
      (fun i hi => hab i (Finset.mem_insert_of_mem hi))
    have e : a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i =
        a j * (∏ i ∈ s, a i - ∏ i ∈ s, b i) + (a j - b j) * ∏ i ∈ s, b i := by ring
    rw [e]
    have hpb : ‖∏ i ∈ s, b i‖ ≤ r ^ s.card := by
      rw [norm_prod]
      calc ∏ i ∈ s, ‖b i‖ ≤ ∏ _i ∈ s, r :=
            Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i hi => hb i (Finset.mem_insert_of_mem hi)
        _ = r ^ s.card := Finset.prod_const r
    have hpos : 0 < r ^ (s.card + 1) := pow_pos hr _
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · rw [norm_mul, pow_succ']
      rcases (norm_nonneg (a j)).eq_or_lt with h0 | h0
      · rw [← h0, zero_mul]; exact pow_pos hr _ |>.trans_le (by rw [pow_succ'])
      · calc ‖a j‖ * ‖∏ i ∈ s, a i - ∏ i ∈ s, b i‖ < ‖a j‖ * r ^ s.card := mul_lt_mul_of_pos_left ih' h0
          _ ≤ r * r ^ s.card := mul_le_mul_of_nonneg_right (ha j (Finset.mem_insert_self _ _)) (pow_nonneg hr.le _)
    · rw [norm_mul, pow_succ']
      exact mul_lt_mul_of_lt_of_le_of_nonneg_of_pos (hab j (Finset.mem_insert_self _ _)) hpb (norm_nonneg _)
        (pow_pos hr _)

end Ultra

theorem ultrametric_det_norm_stable : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I := by
  intro A _ _ I _ _ M M' r hr hM hM' hdet
  have hM'b : ∀ a b, ‖M' a b‖ ≤ r := fun a b => by
    have := IsUltrametricDist.norm_add_le_max (M' a b - M a b) (M a b)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hM' a b).le (hM a b))
  have hdiff : ‖M'.det - M.det‖ < r ^ Fintype.card I := by
    rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
    refine ultrametric_norm_sum_lt _ _ (pow_pos hr _) fun σ _ => ?_
    rw [← smul_sub, norm_sign_smul, ← Finset.card_univ]
    exact ultrametric_norm_prod_sub_lt _ _ _ hr (fun i _ => hM'b _ _) (fun i _ => hM _ _) fun i _ => hM' _ _
  have e : M'.det = M.det + (M'.det - M.det) := by ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hdet]; exact hdiff.ne'), hdet]
  exact max_eq_left hdiff.le

theorem negDef_block_of_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef := by
  intro p q A B C hA hB hC
  let C1 : Matrix (Fin q) (Fin p) ℂ := fun a i => C a (Sum.inl i)
  let C2 : Matrix (Fin q) (Fin q) ℂ := fun a i => C a (Sum.inr i)
  have hsplit : C * Matrix.fromBlocks A 0 0 B * Cᴴ = C1 * A * C1ᴴ + C2 * B * C2ᴴ := by
    have hCe : C = Matrix.fromCols C1 C2 := by ext a (i | i) <;> rfl
    rw [hCe, Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromBlocks,
      Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  have hP : (C2 * (-B) * C2ᴴ).PosDef := by
    have e : C2 * (-B) * C2ᴴ = -(C * Matrix.fromBlocks A 0 0 B * Cᴴ) + C1 * A * C1ᴴ := by
      rw [hsplit]; noncomm_ring
    rw [e]
    exact hC.add_posSemidef (hA.posSemidef.mul_mul_conjTranspose_same C1)
  have hinj : Function.Injective (C2ᴴ).mulVec := by
    intro x y hxy
    by_contra hne
    have hz : x - y ≠ 0 := sub_ne_zero.mpr hne
    have h0 : (C2ᴴ) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have := hP.dotProduct_mulVec_pos hz
    rw [← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hU : IsUnit (C2ᴴ) := Matrix.mulVec_injective_iff_isUnit.mp hinj
  have hG : C2ᴴ * (C2ᴴ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)
  have hGinj : Function.Injective ((C2ᴴ)⁻¹).mulVec := fun x y hxy => by
    have := congrArg (C2ᴴ).mulVec hxy
    rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec, Matrix.one_mulVec] at this
  have key := hP.conjTranspose_mul_mul_same (B := (C2ᴴ)⁻¹) hGinj
  have h1 : ((C2ᴴ)⁻¹)ᴴ * C2 = 1 := by
    have := congrArg Matrix.conjTranspose hG
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one] at this
  have e : ((C2ᴴ)⁻¹)ᴴ * (C2 * -B * C2ᴴ) * (C2ᴴ)⁻¹ = -B := by
    calc ((C2ᴴ)⁻¹)ᴴ * (C2 * -B * C2ᴴ) * (C2ᴴ)⁻¹ = (((C2ᴴ)⁻¹)ᴴ * C2) * -B * (C2ᴴ * (C2ᴴ)⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = -B := by rw [h1, hG, Matrix.one_mul, Matrix.mul_one]
  rwa [e] at key

end PositivityTheory.Xgf
