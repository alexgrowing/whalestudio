import Formalism.FlagUnipotentLattices.DetIndexProductHyperbolicInequality
import Formalism.FlagUnipotentLattices.DetIndexProductPlacesInequalitySq
import Formalism.HyperbolicPlaceProducts.SecondLevelArithmeticNorm
import Formalism.HyperbolicPlaceProducts.ArithmeticCountRevised

open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure nonZeroDivisors
set_option linter.all false

namespace Formalism.HermitianLatticeCounting.P

theorem card_range_nsmul_mul_card_le : Formalism.HermitianLatticeCounting.LocalIntegralStructure.TorsionIndex := Formalism.SLP.Final.torsionIndex
theorem unipotent_upper_entries : Formalism.HermitianLatticeCounting.LocalIntegralStructure.EntriesOfSignaturePreserving := Formalism.SLP.GlobalBoundRefinements.Final.local_integral_entries_of_signature_preserving

theorem orthogonal_complement_formula : PerpCompl := by
  intro K U _ _ _ _ σ hσ B hR hL r A A' hU hA hA' hsup
  have mem : ∀ (S : Submodule K U) (x : U), x ∈ perpR B S ↔ ∀ a ∈ S, B a x = 0 := by
    intro S x; simp [perpR, Submodule.mem_iInf]
  have lower : ∀ S : Submodule K U, finrank K S = r + 1 → r + 1 ≤ finrank K (perpR B S) := by
    intro S hS
    let bs := Module.finBasisOfFinrankEq K S hS
    let Φ : U →ₗ[K] (Fin (r + 1) → K) :=
      { toFun := fun x i => σ (B (bs i : U) x)
        map_add' := by intro x y; ext i; simp
        map_smul' := by intro k x; ext i; simp [hσ] }
    have hker : LinearMap.ker Φ = perpR B S := by
      ext x; rw [LinearMap.mem_ker, mem]; constructor
      · intro h a ha
        have hi : ∀ i, B (bs i : U) x = 0 := by
          intro i
          have h2 : σ (B (bs i : U) x) = 0 := congrFun h i
          exact (map_eq_zero σ).mp h2
        have h3 : a = ∑ i, (bs.repr ⟨a, ha⟩ i) • (bs i : U) := by
          have h4 := congrArg (S.subtype) (bs.sum_repr ⟨a, ha⟩)
          rw [map_sum] at h4
          simpa only [map_smul, Submodule.subtype_apply] using h4.symm
        rw [h3]; simp [hi]
      · intro h; ext i
        show σ (B (bs i : U) x) = 0
        rw [h _ (bs i).2, map_zero]
    have h1 := LinearMap.finrank_range_add_finrank_ker Φ
    have hr : finrank K (LinearMap.range Φ) ≤ r + 1 := by
      simpa using Submodule.finrank_le (LinearMap.range Φ)
    rw [hker] at h1; omega
  have hinf : perpR B A ⊓ perpR B A' = ⊥ := by
    rw [eq_bot_iff]; intro x hx
    obtain ⟨h1, h2⟩ := hx
    have h1' := (mem A x).mp h1
    have h2' := (mem A' x).mp h2
    refine (Submodule.mem_bot K).mpr (hR x fun y => ?_)
    have hy : y ∈ A ⊔ A' := by rw [hsup]; trivial
    obtain ⟨a, ha, a', ha', rfl⟩ := Submodule.mem_sup.mp hy
    simp [h1' a ha, h2' a' ha']
  have hs := Submodule.finrank_sup_add_finrank_inf_eq (perpR B A) (perpR B A')
  rw [hinf, finrank_bot, add_zero] at hs
  have hle := Submodule.finrank_le (perpR B A ⊔ perpR B A')
  have l1 := lower A hA
  have l2 := lower A' hA'
  refine ⟨by omega, by omega, ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr ?_⟩⟩
  exact Submodule.eq_top_of_finrank_eq (by omega)

theorem cofactor_vector_formula : CofactorVec := by
  intro R _ r Z
  refine ⟨fun a => ?_, ?_⟩
  · have h := congrFun (congrFun (Matrix.adjugate_mul Z) (Fin.last r)) a
    rw [Matrix.mul_apply] at h
    rw [h]
    by_cases ha : a = Fin.last r
    · subst ha
      simp
    · simp [Matrix.one_apply, ha, Ne.symm ha]
  · rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
    have h2 : ((-1 : R) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
      rw [← two_mul, pow_mul]
      simp
    rw [h2, one_mul]

section GramAll
open Matrix Polynomial

section Gram
variable {R : Type} [CommRing R]

lemma det_add_smul_single {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n R) (i j : n) (c : R) :
    (M + c • Matrix.single i j (1 : R)).det = M.det + c * M.adjugate j i := by
  have hM : M + c • Matrix.single i j (1 : R) = M.updateRow i (M i + c • Pi.single j 1) := by
    ext a b
    by_cases ha : a = i
    · subst ha
      by_cases hb : b = j
      · subst hb
        simp
      · simp [Matrix.single_apply, Pi.single_apply, hb, Ne.symm hb]
    · simp [Matrix.single_apply, Matrix.updateRow_ne ha, ha, Ne.symm ha]
  rw [hM, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.adjugate_apply]

lemma det_swap_blocks_alt {n : Type} [Fintype n] [DecidableEq n] :
    (fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R)).det =
      (-1) ^ Fintype.card n := by
  have h : (fromBlocks (0 : Matrix n n R) (1 : Matrix n n R) (1 : Matrix n n R) (0 : Matrix n n R)) =
      fromBlocks 1 1 0 1 * fromBlocks 1 0 (-1) 1 * fromBlocks 1 1 0 1 * fromBlocks (-1) 0 0 1 := by
    simp [fromBlocks_multiply]
  rw [h]
  simp [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₁₂, Matrix.det_neg]

lemma det_from_blocks_single_regular (r : ℕ) (W Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (l : Fin (r + 1))
    (t t' : R) (hreg : IsRegular W.det) :
    (fromBlocks W ((-t) • Matrix.single l l (1 : R)) ((-t') • Matrix.single l l (1 : R)) Z).det =
      W.det * Z.det - t * t' * W.adjugate l l * Z.adjugate l l := by
  set A := (-t) • Matrix.single l l (1 : R) with hA
  set D := (-t') • Matrix.single l l (1 : R) with hD
  set δ := W.det with hδ
  have h : fromBlocks W A D Z * fromBlocks W.adjugate (-(W.adjugate * A)) 0 (δ • 1) =
      fromBlocks (δ • 1) 0 (D * W.adjugate) (δ • Z - D * W.adjugate * A) := by
    rw [fromBlocks_multiply]
    congr 1
    · simp [mul_adjugate, hδ]
    · rw [Matrix.mul_neg, ← Matrix.mul_assoc, mul_adjugate]; simp [hδ]
    · simp
    · simp [Matrix.mul_assoc]; abel
  have hDA : D * W.adjugate * A = (t * t' * W.adjugate l l) • Matrix.single l l (1 : R) := by
    rw [hA, hD]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.single_mul_mul_single, smul_smul]
    ext a b
    simp [Matrix.single_apply]
  have h2 := congrArg det h
  rw [det_mul, det_fromBlocks_zero₂₁, det_fromBlocks_zero₁₂, hDA, sub_eq_add_neg, ← neg_smul,
    det_add_smul_single, det_adjugate, det_smul, det_smul, adjugate_smul] at h2
  simp only [Fintype.card_fin, add_tsub_cancel_right, det_one, mul_one, Matrix.smul_apply,
    smul_eq_mul] at h2
  apply (hreg.pow (2 * r + 1)).left
  simp only
  linear_combination h2

lemma det_from_blocks_single (r : ℕ) (W Z : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (l : Fin (r + 1))
    (t t' : R) :
    (fromBlocks W ((-t) • Matrix.single l l (1 : R)) ((-t') • Matrix.single l l (1 : R)) Z).det =
      W.det * Z.det - t * t' * W.adjugate l l * Z.adjugate l l := by
  let φ : R[X] →+* R := Polynomial.evalRingHom (0 : R)
  have hW : φ.mapMatrix (charmatrix (-W)) = W := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp [φ, charmatrix_apply]
    · simp [φ, charmatrix_apply, hab]
  have hZ : φ.mapMatrix (C.mapMatrix Z) = Z := by
    ext a b; simp [φ]
  have hs : ∀ c : R, φ.mapMatrix ((-(C c)) • Matrix.single l l (1 : R[X])) =
      (-c) • Matrix.single l l (1 : R) := by
    intro c; ext a b
    by_cases h : l = a ∧ l = b
    · obtain ⟨rfl, rfl⟩ := h; simp [φ]
    · simp [φ, Matrix.single_apply, h]
  have key := det_from_blocks_single_regular r (charmatrix (-W)) (C.mapMatrix Z) l (C t) (C t')
    (charpoly_monic (-W)).isRegular
  have key2 := congrArg φ key
  rw [RingHom.map_det, RingHom.mapMatrix_apply, fromBlocks_map] at key2
  simp only [← RingHom.mapMatrix_apply] at key2
  rw [hW, hZ, hs, hs] at key2
  rw [key2]
  have ha : ∀ M : Matrix (Fin (r + 1)) (Fin (r + 1)) R[X],
      φ (M.adjugate l l) = (φ.mapMatrix M).adjugate l l := by
    intro M; rw [← RingHom.map_adjugate]; rfl
  simp only [map_sub, map_mul, RingHom.map_det, ha, hW, hZ]
  simp [φ]

theorem gram_determinant_general : GramDetGen := by
  intro R _ r Z W t t'
  have hdiag : ∀ s : R, (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -s else 0) =
      (-s) • Matrix.single (Fin.last r) (Fin.last r) (1 : R) := by
    intro s
    ext i j
    by_cases hi : i = Fin.last r
    · subst hi
      by_cases hj : j = Fin.last r
      · subst hj
        simp
      · simp [Matrix.diagonal_apply, Matrix.single_apply, Ne.symm hj]
    · simp [Matrix.diagonal_apply, Matrix.single_apply, hi, Ne.symm hi]
  have hS : Matrix.fromBlocks (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -t else 0) W Z
      (Matrix.diagonal fun i : Fin (r + 1) => if i = Fin.last r then -t' else 0) *
      Matrix.fromBlocks 0 1 1 0 =
      Matrix.fromBlocks W ((-t) • Matrix.single (Fin.last r) (Fin.last r) (1 : R))
        ((-t') • Matrix.single (Fin.last r) (Fin.last r) (1 : R)) Z := by
    rw [hdiag t, hdiag t', Matrix.fromBlocks_multiply]
    simp
  have hdetS := det_swap_blocks_alt (R := R) (n := Fin (r + 1))
  have hB := det_from_blocks_single r W Z (Fin.last r) t t'
  have hcW := (cofactor_vector_formula R r W).2
  have hcZ := (cofactor_vector_formula R r Z).2
  have h1 := congrArg Matrix.det hS
  rw [Matrix.det_mul, hdetS, Fintype.card_fin, hB, hcW, hcZ] at h1
  have hsq : ((-1 : R) ^ (r + 1)) * ((-1) ^ (r + 1)) = 1 := by
    rw [← mul_pow]
    simp
  have key : ∀ x : R, x * (-1) ^ (r + 1) = W.det * Z.det - t * t' *
      (W.submatrix Fin.castSucc Fin.castSucc).det * (Z.submatrix Fin.castSucc Fin.castSucc).det →
      x = (-1) ^ (r + 1) * (Z.det * W.det - t * t' * (Z.submatrix Fin.castSucc Fin.castSucc).det *
        (W.submatrix Fin.castSucc Fin.castSucc).det) := by
    intro x hx
    linear_combination ((-1 : R) ^ (r + 1)) * hx - x * hsq
  exact key _ h1

theorem gram_determinant_formula : GramDet := by
  intro r Z T T'
  have h := gram_determinant_general ℂ r Z Z.conjTranspose (T : ℂ) (T' : ℂ)
  rw [h, ← Matrix.conjTranspose_submatrix, Matrix.det_conjTranspose, Matrix.det_conjTranspose]
  congr 1
  have hs : ∀ z : ℂ, z * star z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    first
      | exact Complex.mul_conj' z
      | (rw [Complex.star_def, Complex.mul_conj']; push_cast; ring)
      | (rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq])
  rw [mul_assoc ((T : ℂ) * (T' : ℂ)), hs, hs]
  push_cast <;> ring

end Gram

theorem gram_matrix_nondegenerate : GramNondeg := by
  intro K V ι _ _ _ _ _ σ B v hdet
  have right : ∀ c : ι → K, (∀ j, B (v j) (∑ i, c i • v i) = 0) → c = 0 := by
    intro c hc
    have h1 : (Matrix.of fun i j => B (v i) (v j)).mulVec (fun i => σ (c i)) = 0 := by
      funext j
      have hj := hc j
      rw [map_sum] at hj
      simp only [LinearMap.map_smulₛₗ, smul_eq_mul] at hj
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
      rw [← hj]
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
    have h2 := Matrix.eq_zero_of_mulVec_eq_zero hdet h1
    funext i
    have h3 := congrFun h2 i
    simp only [Pi.zero_apply] at h3
    exact (map_eq_zero σ).1 h3
  have left : ∀ c : ι → K, (∀ j, B (∑ i, c i • v i) (v j) = 0) → c = 0 := by
    intro c hc
    have h1 : Matrix.vecMul c (Matrix.of fun i j => B (v i) (v j)) = 0 := by
      funext j
      have hj := hc j
      rw [map_sum, LinearMap.sum_apply] at hj
      simp only [LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul] at hj
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      exact hj
    exact Matrix.eq_zero_of_vecMul_eq_zero hdet h1
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hg0 := right g (fun j => by rw [hg, map_zero])
    intro i
    exact congrFun hg0 i
  refine ⟨hli, finrank_span_eq_card hli, ?_, ?_⟩
  · intro x hx hB
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have hc := right c (fun j => hB (v j) (Submodule.subset_span ⟨j, rfl⟩))
    simp [hc]
  · intro x hx hB
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 hx
    have hc := left c (fun j => hB (v j) (Submodule.subset_span ⟨j, rfl⟩))
    simp [hc]

end GramAll

theorem denominator_norm_fraction : DenomNormFrac := by
  intro E _ _ α J hα hJ hint
  have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ α * J ≤ 1 := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    rw [FractionalIdeal.mem_spanSingleton] at hi
    obtain ⟨z, rfl⟩ := hi
    obtain ⟨w, hw⟩ := hint j hj
    rw [FractionalIdeal.mem_one_iff]
    refine ⟨z * w, ?_⟩
    rw [map_mul, Algebra.smul_def, mul_assoc]
    congr 1
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.1 hle
  have hne : FractionalIdeal.spanSingleton (𝓞 E)⁰ α * J ≠ 0 :=
    mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.2 hα) hJ
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    apply hne
    rw [← hI]
    simp
  have hn : FractionalIdeal.absNorm (FractionalIdeal.spanSingleton (𝓞 E)⁰ α) =
      |Algebra.norm ℚ α| := by
    first
      | exact FractionalIdeal.absNorm_span_singleton (𝓞 E) α
      | exact FractionalIdeal.absNorm_span_singleton α
      | simp [FractionalIdeal.absNorm_span_singleton]
  have hc : FractionalIdeal.absNorm ((I : FractionalIdeal (𝓞 E)⁰ E)) = (Ideal.absNorm I : ℚ) := by
    first
      | exact FractionalIdeal.coeIdeal_absNorm I
      | simp [FractionalIdeal.coeIdeal_absNorm]
      | simp
  have key : |Algebra.norm ℚ α| * FractionalIdeal.absNorm J = (Ideal.absNorm I : ℚ) := by
    rw [← hn, ← map_mul, ← hI, hc]
  rw [key]
  have h0 : Ideal.absNorm I ≠ 0 := by
    rwa [Ne, Ideal.absNorm_eq_zero_iff]
  exact_mod_cast Nat.one_le_iff_ne_zero.2 h0

lemma pow_two_div_sq_identity (g : ℝ) (e f : ℕ) : ((2 / g) ^ (e * f)) ^ 2 = 4 ^ (e * f) / g ^ (2 * f * e) := by
  rw [← pow_mul, div_pow, show e * f * 2 = 2 * f * e by ring]
  congr 1
  rw [show 2 * f * e = 2 * (e * f) by ring, pow_mul]
  norm_num

theorem L4_arithmetic_square : DetIndexProductInequalitySq := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ i₁ i₂ G0₁ G0₂ g e f hP₁ hP₂ hg hi₁ hi₂ hL₁ hL₂ hdet hG₁ hG₂ hgP
  have hq : 0 < g ^ (2 * f * e) := pow_pos hg _
  have hP : 0 < dPs₁ * dPs₂ := mul_pos hP₁ hP₂
  have hc : 0 ≤ (2 / g) ^ (e * f) := pow_nonneg (div_nonneg (by norm_num) hg.le) _
  have ha : 0 ≤ dLa₁ * i₁ ^ 2 := mul_nonneg hL₁ (sq_nonneg _)
  have hb : 0 ≤ dLa₂ * i₂ ^ 2 := mul_nonneg hL₂ (sq_nonneg _)
  have hab : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ G0₁ * G0₂ :=
    mul_le_mul hG₁ hG₂ hb (ha.trans hG₁)
  have hG : 0 ≤ G0₁ * G0₂ := (mul_nonneg ha hb).trans hab
  have hF : 1 ≤ 4 ^ (e * f) * (dPs₁ * dPs₂) / g ^ (2 * f * e) := by
    rw [← mul_assoc]
    first
      | exact (one_le_div hq).2 hgP
      | exact (one_le_div₀ hq).2 hgP
      | exact (le_div_iff₀ hq).2 (by rw [one_mul]; exact hgP)
  have e1 : (detM * i₁ * i₂) ^ 2 = (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / (dPs₁ * dPs₂) := by
    rw [show (detM * i₁ * i₂) ^ 2 = detM ^ 2 * i₁ ^ 2 * i₂ ^ 2 by ring, hdet]
    ring
  have hsq : (detM * i₁ * i₂) ^ 2 ≤ ((2 / g) ^ (e * f)) ^ 2 * (G0₁ * G0₂) := by
    rw [pow_two_div_sq_identity g e f, e1]
    have h4 : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤
        4 ^ (e * f) / g ^ (2 * f * e) * (G0₁ * G0₂) * (dPs₁ * dPs₂) :=
      calc (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤ G0₁ * G0₂ := hab
        _ ≤ (G0₁ * G0₂) * (4 ^ (e * f) * (dPs₁ * dPs₂) / g ^ (2 * f * e)) :=
          le_mul_of_one_le_right hG hF
        _ = 4 ^ (e * f) / g ^ (2 * f * e) * (G0₁ * G0₂) * (dPs₁ * dPs₂) := by ring
    first
      | exact (div_le_iff₀ hP).2 h4
      | exact (div_le_iff hP).2 h4
  by_cases h : detM ≤ 0
  · have h0 : detM * i₁ * i₂ ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_iff.2 (Or.inr ⟨h, mul_nonneg hi₁ hi₂⟩)
    exact h0.trans (mul_nonneg hc (Real.sqrt_nonneg _))
  · have hL : 0 ≤ detM * i₁ * i₂ := mul_nonneg (mul_nonneg (not_le.mp h).le hi₁) hi₂
    have hs : Real.sqrt ((detM * i₁ * i₂) ^ 2) ≤
        Real.sqrt (((2 / g) ^ (e * f)) ^ 2 * (G0₁ * G0₂)) := by
      first
        | exact Real.sqrt_le_sqrt hsq
        | gcongr
    rw [Real.sqrt_sq hL, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc] at hs
    exact hs

theorem L5_arithmetic_square : DetIndexProductPlacesInequalitySq := by
  intro detM dLa₁ dLa₂ dPs₁ dPs₂ P₁ P₂ dQ₁ dQ₂ i₁ i₂ G0₁ G0₂ g NT K₁ K₂ Nr₁ Nr₂ e f
    hP₁ hP₂ hQ₁ hQ₂ hg hi₁ hi₂ hL₁ hL₂ hNT hK₁ hK₂ hN₁ hN₂ hdet hd₁ hd₂ hG₁ hG₂ hT₁ hT₂ hgQ
  have hq : 0 < g ^ (2 * f * e) := pow_pos hg _
  have hc : 0 ≤ (2 / g) ^ (e * f) := pow_nonneg (div_nonneg (by norm_num) hg.le) _
  have ha : 0 ≤ dLa₁ * i₁ ^ 2 := mul_nonneg hL₁ (sq_nonneg _)
  have hb : 0 ≤ dLa₂ * i₂ ^ 2 := mul_nonneg hL₂ (sq_nonneg _)
  have hA : dLa₁ * i₁ ^ 2 * Nr₁ ≤ G0₁ := by
    have h := mul_le_mul_of_nonneg_right hG₁ hN₁.le
    rwa [div_mul_cancel₀ _ hN₁.ne'] at h
  have hB : dLa₂ * i₂ ^ 2 * Nr₂ ≤ G0₂ := by
    have h := mul_le_mul_of_nonneg_right hG₂ hN₂.le
    rwa [div_mul_cancel₀ _ hN₂.ne'] at h
  have hk₂ : 0 < Nr₂ * K₂ ^ 2 := mul_pos hN₂ (pow_pos hK₂ 2)
  have hk₁ : 0 < Nr₁ * K₁ ^ 2 := mul_pos hN₁ (pow_pos hK₁ 2)
  have hp1 : NT ≤ P₁ * (Nr₂ * K₂ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hT₁ hk₂.le
    rwa [div_mul_cancel₀ _ hk₂.ne'] at h
  have hp2 : NT ≤ P₂ * (Nr₁ * K₁ ^ 2) := by
    have h := mul_le_mul_of_nonneg_right hT₂ hk₁.le
    rwa [div_mul_cancel₀ _ hk₁.ne'] at h
  have hG1 : 0 ≤ G0₁ := le_trans (mul_nonneg ha hN₁.le) hA
  have hG2 : 0 ≤ G0₂ := le_trans (mul_nonneg hb hN₂.le) hB
  have hG : 0 ≤ G0₁ * G0₂ := mul_nonneg hG1 hG2
  have hPP : 0 < P₁ * P₂ := mul_pos hP₁ hP₂
  have hF : 1 ≤ 4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e) := by
    rw [← mul_assoc]
    first
      | exact (one_le_div hq).2 hgQ
      | exact (one_le_div₀ hq).2 hgQ
  have hNN : NT * NT ≤ (P₁ * (Nr₂ * K₂ ^ 2)) * (P₂ * (Nr₁ * K₁ ^ 2)) :=
    mul_le_mul hp1 hp2 hNT.le (le_trans hNT.le hp1)
  have key : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * (NT * NT) ≤
      (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e)) := by
    calc (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * (NT * NT)
        ≤ (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) * ((P₁ * (Nr₂ * K₂ ^ 2)) * (P₂ * (Nr₁ * K₁ ^ 2))) :=
          mul_le_mul_of_nonneg_left hNN (mul_nonneg ha hb)
      _ = ((dLa₁ * i₁ ^ 2 * Nr₁) * (dLa₂ * i₂ ^ 2 * Nr₂)) * ((K₁ * K₂) ^ 2 * (P₁ * P₂)) := by ring
      _ ≤ (G0₁ * G0₂) * ((K₁ * K₂) ^ 2 * (P₁ * P₂)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hA hB (mul_nonneg hb hN₂.le) hG1)
            (mul_nonneg (sq_nonneg _) hPP.le)
      _ = (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * 1 := by ring
      _ ≤ (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e)) :=
          mul_le_mul_of_nonneg_left hF (mul_nonneg (mul_nonneg hG (sq_nonneg _)) hPP.le)
  have hR : ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂) =
      ((G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e))
        / (NT * NT)) / ((P₁ * dQ₁) * (P₂ * dQ₂)) := by
    rw [show ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 =
      ((2 / g) ^ (e * f)) ^ 2 * (K₁ * K₂) ^ 2 / (NT * NT) by ring, pow_two_div_sq_identity]
    field_simp [hP₁.ne', hP₂.ne', hQ₁.ne', hQ₂.ne', hNT.ne', hq.ne'] <;> ring
  have hL2 : (detM * i₁ * i₂) ^ 2 =
      (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) / ((P₁ * dQ₁) * (P₂ * dQ₂)) := by
    rw [show (detM * i₁ * i₂) ^ 2 = detM ^ 2 * i₁ ^ 2 * i₂ ^ 2 by ring, hdet, hd₁, hd₂]
    ring
  have hPQ : 0 < (P₁ * dQ₁) * (P₂ * dQ₂) := mul_pos (mul_pos hP₁ hQ₁) (mul_pos hP₂ hQ₂)
  have hNT2 : 0 < NT * NT := mul_pos hNT hNT
  have hk : (dLa₁ * i₁ ^ 2) * (dLa₂ * i₂ ^ 2) ≤
      (G0₁ * G0₂) * (K₁ * K₂) ^ 2 * (P₁ * P₂) * (4 ^ (e * f) * (dQ₁ * dQ₂) / g ^ (2 * f * e))
        / (NT * NT) := (le_div_iff₀ hNT2).2 key
  have hsq : (detM * i₁ * i₂) ^ 2 ≤ ((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂) := by
    rw [hL2, hR]
    first
      | exact div_le_div_of_nonneg_right hk hPQ.le
      | exact (div_le_div_iff_of_pos_right hPQ).2 hk
      | exact div_le_div_of_le_right hk hPQ
  have hRc : 0 ≤ (2 / g) ^ (e * f) * K₁ * K₂ / NT :=
    div_nonneg (mul_nonneg (mul_nonneg hc hK₁.le) hK₂.le) hNT.le
  by_cases h : detM ≤ 0
  · have h0 : detM * i₁ * i₂ ≤ 0 := by
      rw [mul_assoc]
      exact mul_nonpos_iff.2 (Or.inr ⟨h, mul_nonneg hi₁ hi₂⟩)
    exact h0.trans (div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hc (Real.sqrt_nonneg _))
      hK₁.le) hK₂.le) hNT.le)
  · have hL : 0 ≤ detM * i₁ * i₂ := mul_nonneg (mul_nonneg (not_le.mp h).le hi₁) hi₂
    have hs : Real.sqrt ((detM * i₁ * i₂) ^ 2) ≤
        Real.sqrt (((2 / g) ^ (e * f) * K₁ * K₂ / NT) ^ 2 * (G0₁ * G0₂)) := by
      first
        | exact Real.sqrt_le_sqrt hsq
        | gcongr
    rw [Real.sqrt_sq hL, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hRc] at hs
    calc detM * i₁ * i₂ ≤ (2 / g) ^ (e * f) * K₁ * K₂ / NT * Real.sqrt (G0₁ * G0₂) := hs
      _ = (2 / g) ^ (e * f) * Real.sqrt (G0₁ * G0₂) * K₁ * K₂ / NT := by ring

section NF
variable {E : Type} [Field E] [NumberField E]

end NF

end Formalism.HermitianLatticeCounting.P
