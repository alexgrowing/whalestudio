import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Idem3
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicUnipotentRadicalsRationalCocompact

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipHaar GlobalTheory.Mem.UnipCocompact

noncomputable section

namespace GlobalTheory.UnipHaar.RadMem

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = -J i j) (u v : Fin n → E) : form σ J u v = -σ (form σ J v u) := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum, mul_neg, neg_mul, Finset.sum_neg_distrib, neg_neg]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_eq_dot {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → E) :
    (J *ᵥ fun i => σ (v i)) ⬝ᵥ u = form σ J u v := dotProduct_comm _ _

section Plane

variable {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}

theorem prX_mulVec_x_of_isAdapted (hA : H.IsAdapted σ B W W₁ i₀ i₁) : prX σ W.J H *ᵥ H.x = H.x := by
  rw [prX, vecMulVec_mulVec, op_smul_eq_smul, form_eq_dot, hA.xy, one_smul]

theorem prY_mulVec_x_eq_zero_of_isAdapted (hA : H.IsAdapted σ B W W₁ i₀ i₁) : prY σ W.J H *ᵥ H.x = 0 := by
  rw [prY, neg_mulVec, vecMulVec_mulVec, op_smul_eq_smul, form_eq_dot, hA.xx, zero_smul, neg_zero]

theorem dot_col (hA : H.IsAdapted σ B W W₁ i₀ i₁) (j : Fin n₁) :
    ((W.J *ᵥ fun i => σ (H.y i)) ᵥ* H.ι) j = 0 ∧ ((W.J *ᵥ fun i => σ (H.x i)) ᵥ* H.ι) j = 0 := by
  have h := hA.orth (Pi.single j 1)
  rw [mulVec_single_one] at h
  simp only [form, dotProduct] at h
  simp only [vecMul, dotProduct]
  constructor
  · rw [← h.2]; exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  · rw [← h.1]; exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]

theorem prX_mul_ι (hA : H.IsAdapted σ B W W₁ i₀ i₁) : prX σ W.J H * H.ι = 0 := by
  rw [prX, vecMulVec_mul]
  have : ((W.J *ᵥ fun i => σ (H.y i)) ᵥ* H.ι) = 0 := funext fun j => (dot_col hA j).1
  rw [this]; ext; simp [vecMulVec]

theorem prY_mul_ι (hA : H.IsAdapted σ B W W₁ i₀ i₁) : prY σ W.J H * H.ι = 0 := by
  rw [prY, Matrix.neg_mul, vecMulVec_mul]
  have : ((W.J *ᵥ fun i => σ (H.x i)) ᵥ* H.ι) = 0 := funext fun j => (dot_col hA j).2
  rw [this]; ext; simp [vecMulVec]

theorem prI_mul_ι (hA : H.IsAdapted σ B W W₁ i₀ i₁) : prI σ W.J H * H.ι = H.ι := by
  rw [prI, Matrix.sub_mul, Matrix.sub_mul, prX_mul_ι hA, prY_mul_ι hA, Matrix.one_mul, sub_zero, sub_zero]

theorem form_prI (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hA : H.IsAdapted σ B W W₁ i₀ i₁)
    (v : Fin n → E) : form σ W.J (prI σ W.J H *ᵥ v) H.x = 0 ∧ form σ W.J (prI σ W.J H *ᵥ v) H.y = 0 := by
  have hyx : form σ W.J H.y H.x = -1 := by rw [form_swap hσ hW, hA.xy, map_one]
  have lin : ∀ (a b : Fin n → E) (s t : E) (w : Fin n → E), form σ W.J (a - s • H.x + t • H.y) w =
      form σ W.J a w - s * form σ W.J H.x w + t * form σ W.J H.y w := fun a b s t w => by
    simp only [form, sub_dotProduct, add_dotProduct, smul_dotProduct, smul_eq_mul]
  have e : prI σ W.J H *ᵥ v = v - form σ W.J v H.y • H.x + form σ W.J v H.x • H.y := by
    rw [prI, sub_mulVec, sub_mulVec, one_mulVec, prX, prY, neg_mulVec, vecMulVec_mulVec, vecMulVec_mulVec,
      op_smul_eq_smul, op_smul_eq_smul, form_eq_dot, form_eq_dot, sub_neg_eq_add]
  rw [e, lin _ v, lin _ v, hA.xx, hA.yy, hA.xy, hyx]
  constructor <;> ring

end Plane

section Range

variable {σ : E →ₐ[F] E} {B : Base F E} {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {i₀ i₁ : ℕ}

theorem det_ne_zero_of_sig {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (r s : ℕ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  let e : Fin r ⊕ Fin s ≃ Fin m := finSumFinEquiv.trans (finCongr hrs)
  let A' : Matrix (Fin m) (Fin m) ℂ := A.submatrix id e.symm
  have h2 : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]; ext i j; simp [A', Matrix.mul_apply]
  have h3 : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [h2, det_submatrix_equiv_self, det_fromBlocks_zero₂₁]; simp [Matrix.det_neg]
  intro h0
  rw [det_mul, det_mul, h0, mul_zero, zero_mul] at h3
  exact h3 rfl

theorem det_ne_zero_of_skew {m r s : ℕ} {Y : Spc F E m} (hY : Y.IsSkew σ B r s) : Y.J.det ≠ 0 := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  intro h0
  apply det_ne_zero_of_sig _ _ _ (hY.sig w)
  rw [det_smul, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, mul_zero]

theorem ι_injective (hdet : W₁.J.det ≠ 0) (hA : H.IsAdapted σ B W W₁ i₀ i₁) : Function.Injective H.ι.mulVec := by
  intro a b hab
  rw [← sub_eq_zero]
  apply eq_zero_of_vecMul_eq_zero hdet
  have : H.ι *ᵥ (a - b) = 0 := by rw [mulVec_sub, hab, sub_self]
  rw [← hA.gram, ← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, this, zero_vecMul, zero_vecMul]

theorem form_comb (J : Matrix (Fin n) (Fin n) E) (a b : E) (u v w : Fin n → E) :
    form σ J (a • u + b • v) w = a * form σ J u w + b * form σ J v w := by
  simp [form, add_dotProduct, smul_dotProduct]

theorem prI_eq_mul (hσ : ∀ x, σ (σ x) = x) (hW : ∀ i j, σ (W.J j i) = -W.J i j) (hdet : W₁.J.det ≠ 0)
    (hA : H.IsAdapted σ B W W₁ i₀ i₁) : ∃ T : Matrix (Fin n₁) (Fin n) E, prI σ W.J H = H.ι * T := by
  classical
  have hyx : form σ W.J H.y H.x = -1 := by rw [form_swap hσ hW, hA.xy, map_one]
  let Ax : Matrix (Fin 2) (Fin n) E := Matrix.of ![W.J *ᵥ fun i => σ (H.x i), W.J *ᵥ fun i => σ (H.y i)]
  have hAx : ∀ v, Ax *ᵥ v = ![form σ W.J v H.x, form σ W.J v H.y] := by
    intro v; ext k; fin_cases k <;> exact form_eq_dot (σ := σ) _ _ _
  let K := LinearMap.ker Ax.mulVecLin
  have hsurj : LinearMap.range Ax.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro p
    refine ⟨(-p 0) • H.y + p 1 • H.x, ?_⟩
    rw [mulVecLin_apply, hAx, form_comb, form_comb, hyx, hA.xx, hA.yy, hA.xy]
    ext k; fin_cases k <;> simp
  have hK : Module.finrank E K = n₁ := by
    show Module.finrank E (LinearMap.ker Ax.mulVecLin) = n₁
    have := LinearMap.finrank_range_add_finrank_ker Ax.mulVecLin
    rw [hsurj, finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at this
    have := hA.rank
    omega
  have hR : Module.finrank E (LinearMap.range H.ι.mulVecLin) = n₁ := by
    rw [LinearMap.finrank_range_of_inj (ι_injective hdet hA), Module.finrank_fin_fun]
  have hle : LinearMap.range H.ι.mulVecLin ≤ K := by
    rintro _ ⟨t, rfl⟩
    rw [LinearMap.mem_ker, mulVecLin_apply, mulVecLin_apply, hAx, (hA.orth t).1, (hA.orth t).2]
    ext k; fin_cases k <;> rfl
  have heq := Submodule.eq_of_le_of_finrank_eq hle (by rw [hR, hK])
  have hcol : ∀ j : Fin n, ∃ t, H.ι *ᵥ t = fun i => prI σ W.J H i j := by
    intro j
    have hv : (fun i => prI σ W.J H i j) ∈ K := by
      rw [LinearMap.mem_ker, mulVecLin_apply, hAx]
      have h := form_prI hσ hW hA (Pi.single j 1)
      have e : prI σ W.J H *ᵥ Pi.single j 1 = fun i => prI σ W.J H i j := mulVec_single_one _ _
      rw [← e, h.1, h.2]; ext k; fin_cases k <;> rfl
    rw [← heq] at hv
    obtain ⟨t, ht⟩ := hv
    exact ⟨t, ht⟩
  choose t ht using hcol
  refine ⟨Matrix.of fun k j => t j k, ?_⟩
  ext i j
  have h : (H.ι *ᵥ t j) i = prI σ W.J H i j := congrFun (ht j) i
  rw [Matrix.mul_apply, ← h]; rfl

end Range

end GlobalTheory.UnipHaar.RadMem

namespace GlobalTheory.UnipHaar.RadMem

open Matrix

theorem mem_raise3 {S : Type} [Ring S] (ε : Fin 3 → S) (X : S) :
    X ∈ raise ε wt3 0 ↔ (ε 0 * X * ε 0 = 0 ∧ ε 1 * X * ε 0 = 0 ∧ ε 2 * X * ε 0 = 0 ∧ ε 1 * X * ε 1 = 0 ∧
      ε 2 * X * ε 1 = 0 ∧ ε 2 * X * ε 2 = 0) := by
  constructor
  · intro h
    exact ⟨h 0 0 (by decide), h 1 0 (by decide), h 2 0 (by decide), h 1 1 (by decide), h 2 1 (by decide), h 2 2 (by decide)⟩
  · rintro ⟨h00, h10, h20, h11, h21, h22⟩ a b hab
    fin_cases a <;> fin_cases b <;> first | assumption | (exfalso; revert hab; decide)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_incl (σ : E →ₐ[F] E) (e : E) : cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := by
  simp [cA, inclR, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

theorem incM_mul {l m k : ℕ} (A : Matrix (Fin l) (Fin m) E) (C : Matrix (Fin m) (Fin k) E) :
    incM F (A * C) = incM F A * incM F C := Matrix.map_mul

theorem incM_mulVec {l m : ℕ} (A : Matrix (Fin l) (Fin m) E) (v : Fin m → E) :
    incM F A *ᵥ incV F v = incV F (A *ᵥ v) := by
  funext i; exact (RingHom.map_mulVec _ _ _ _).symm

theorem incM_vecMulVec {m : ℕ} (a b : Fin m → E) : incM F (vecMulVec a b) = vecMulVec (incV F a) (incV F b) := by
  ext i j; simp [incM, incV, vecMulVec]

end GlobalTheory.UnipHaar.RadMem

namespace GlobalTheory.UnipHaar.RadMem

open Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_unip_iff_set (σ : E →ₐ[F] E) {n n₁ : ℕ} (W : Spc F E n) (H : Plane E n n₁) (u : UA σ W.J) :
    u ∈ unip σ W H ↔ (mat u *ᵥ incV F H.x = incV F H.x ∧
      ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ z + a • incV F H.x) := by
  constructor
  · intro hu
    induction hu using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one =>
      have e1 : mat (1 : UA σ W.J) = 1 := rfl
      exact ⟨by rw [e1, one_mulVec], fun z => ⟨0, by rw [e1, one_mulVec, zero_smul, add_zero]⟩⟩
    | mul a b _ _ ha hb =>
      have e : mat (a * b) = mat a * mat b := rfl
      refine ⟨by rw [e, ← mulVec_mulVec, hb.1, ha.1], fun z => ?_⟩
      obtain ⟨p, hp⟩ := hb.2 z
      obtain ⟨q, hq⟩ := ha.2 z
      refine ⟨q + p, ?_⟩
      rw [e, ← mulVec_mulVec, hp, mulVec_add, mulVec_smul, hq, ha.1, add_smul]; abel
    | inv a _ ha =>
      have e : mat a⁻¹ * mat a = 1 := Units.inv_mul a.1
      have hx : mat a⁻¹ *ᵥ incV F H.x = incV F H.x := by
        conv_lhs => rw [← ha.1]
        rw [mulVec_mulVec, e, one_mulVec]
      refine ⟨hx, fun z => ?_⟩
      obtain ⟨q, hq⟩ := ha.2 z
      refine ⟨-q, ?_⟩
      have : mat a⁻¹ *ᵥ (mat a *ᵥ (incM F H.ι *ᵥ z)) = mat a⁻¹ *ᵥ (incM F H.ι *ᵥ z + q • incV F H.x) := by rw [hq]
      rw [mulVec_mulVec _ (mat a⁻¹) (mat a), e, one_mulVec, mulVec_add, mulVec_smul, hx] at this
      rw [neg_smul, ← sub_eq_add_neg, eq_sub_iff_add_eq]
      exact this.symm
  · intro h; exact Subgroup.subset_closure h

theorem mem_unip_iff_raise (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s r₁ s₁ : ℕ)
    (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (hW₁ : W₁.IsSkew σ B r₁ s₁) (hA : H.IsAdapted σ B W W₁ i₀ i₁)
    (u : UA σ W.J) : u ∈ unip σ W H ↔ mat u - 1 ∈ raise (idem3 σ W.J H) wt3 0 := by
  have hσ : ∀ x, σ (σ x) = x := sigma_invol hB.cm
  obtain ⟨T, hT⟩ := prI_eq_mul hσ hW.skew (det_ne_zero_of_skew hW₁) hA
  have hu : (mat u)ᵀ * incM F W.J * (mat u).map (cA σ) = incM F W.J := u.2
  have hmap : ∀ A : Matrix (Fin n) (Fin n) E, incM F A = (inclR (F := F) (E := E) (AF F)).mapMatrix A := fun A => rfl
  rw [mem_unip_iff_set, mem_raise3]
  set x' := incV F H.x with hx'
  set y' := incV F H.y with hy'
  set ι' := incM F H.ι with hι'
  set cx := incV F (W.J *ᵥ fun i => σ (H.x i)) with hcx
  set cy := incV F (W.J *ᵥ fun i => σ (H.y i)) with hcy
  set M := mat u with hM
  set X := M - 1 with hX
  set ex := idem3 σ W.J H 0 with hex0
  set ei := idem3 σ W.J H 1 with hei0
  set ey := idem3 σ W.J H 2 with hey0
  have hsum : ex + ei + ey = 1 := by
    show incM F (prX σ W.J H) + incM F (prI σ W.J H) + incM F (prY σ W.J H) = 1
    rw [prI, hmap, hmap, hmap, map_sub, map_sub, map_one]; abel
  have hex : ex = vecMulVec x' cy := incM_vecMulVec _ _
  have hey : ey = -vecMulVec y' cx := by
    show incM F (prY σ W.J H) = _
    rw [prY, hmap, map_neg, ← hmap, incM_vecMulVec]
  have hexx : ex *ᵥ x' = x' := by
    show incM F (prX σ W.J H) *ᵥ incV F H.x = incV F H.x
    rw [incM_mulVec, prX_mulVec_x_of_isAdapted hA]
  have heyx : ey *ᵥ x' = 0 := by
    show incM F (prY σ W.J H) *ᵥ incV F H.x = 0
    rw [incM_mulVec, prY_mulVec_x_eq_zero_of_isAdapted hA]; funext i; simp [incV]
  have hei : ei = 1 - ex - ey := by rw [← hsum]; abel
  have heix : ei *ᵥ x' = 0 := by rw [hei, sub_mulVec, sub_mulVec, one_mulVec, hexx, heyx]; simp
  have heiι : ei * ι' = ι' := by
    show incM F (prI σ W.J H) * incM F H.ι = incM F H.ι
    rw [← incM_mul, prI_mul_ι hA]
  have hT' : ei = ι' * incM F T := by
    show incM F (prI σ W.J H) = _
    rw [hT, incM_mul]
  have hcx' : cx = incM F W.J *ᵥ fun i => cA σ (x' i) := by
    rw [hcx, ← incM_mulVec]; congr 1
    all_goals (funext i; simp only [incV, hx', cA_incl])
  constructor
  · rintro ⟨hx, hι⟩
    have hXx : X *ᵥ x' = 0 := by rw [hX, sub_mulVec, one_mulVec, hx, sub_self]
    have g0 : X * ex = 0 := by
      rw [hex, mul_vecMulVec, hXx]; ext i j; simp [vecMulVec]
    have hXz : ∀ z, ∃ a : AE F E, X *ᵥ (ι' *ᵥ z) = a • x' := by
      intro z
      obtain ⟨a, ha⟩ := hι z
      exact ⟨a, by rw [hX, sub_mulVec, one_mulVec, ha, add_sub_cancel_left]⟩
    have kill : ∀ P : Matrix (Fin n) (Fin n) (AE F E), P *ᵥ x' = 0 → P * X * ι' = 0 := by
      intro P hP; ext i j
      obtain ⟨a, ha⟩ := hXz (Pi.single j 1)
      have : (P *ᵥ (X *ᵥ (ι' *ᵥ Pi.single j 1))) i = (P *ᵥ (a • x')) i := by rw [ha]
      rw [mulVec_smul, hP, smul_zero, mulVec_mulVec _ P X, mulVec_mulVec _ (P * X) ι', mulVec_single_one] at this
      exact this
    have via : ∀ P : Matrix (Fin n) (Fin n) (AE F E), P *ᵥ x' = 0 → P * X * ei = 0 := by
      intro P hP
      calc P * X * ei = P * X * (ι' * incM F T) := by rw [← hT']
        _ = (P * X * ι') * incM F T := by rw [Matrix.mul_assoc (P * X)]
        _ = 0 := by rw [kill P hP, Matrix.zero_mul]
    have hxc : M.map (cA σ) *ᵥ (fun i => cA σ (x' i)) = fun i => cA σ (x' i) := by
      funext i
      have h1 := RingHom.map_mulVec (cA σ : AE F E →+* AE F E) M x' i
      rw [hx] at h1
      exact h1.symm
    have hw : Mᵀ *ᵥ (incM F W.J *ᵥ fun i => cA σ (x' i)) = incM F W.J *ᵥ fun i => cA σ (x' i) := by
      conv_lhs => rw [← hxc]
      rw [mulVec_mulVec, mulVec_mulVec, hu]
    have hkey : cx ⬝ᵥ (X *ᵥ y') = 0 := by
      rw [hX, sub_mulVec, one_mulVec, dotProduct_sub, sub_eq_zero, hcx', dotProduct_mulVec _ M y',
        ← mulVec_transpose, hw]
    have g3 : ey * X * ey = 0 := by
      rw [hey, Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, neg_neg, vecMulVec_mul, vecMulVec_mul_vecMulVec,
        ← dotProduct_mulVec, hkey, zero_smul]
      ext i j; simp [vecMulVec]
    refine ⟨by rw [Matrix.mul_assoc, g0, Matrix.mul_zero], by rw [Matrix.mul_assoc, g0, Matrix.mul_zero],
      by rw [Matrix.mul_assoc, g0, Matrix.mul_zero], via ei heix, via ey heyx, g3⟩
  · rintro ⟨c00, c10, c20, c11, c21, c22⟩
    have g0 : X * ex = 0 := by
      have : X * ex = (ex + ei + ey) * X * ex := by rw [hsum, Matrix.one_mul]
      rw [this, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, c00, c10, c20, add_zero, add_zero]
    have hx : M *ᵥ x' = x' := by
      have : X *ᵥ x' = 0 := by
        conv_lhs => rw [← hexx]
        rw [mulVec_mulVec, g0, zero_mulVec]
      rw [hX, sub_mulVec, one_mulVec, sub_eq_zero] at this
      exact this
    refine ⟨hx, fun z => ?_⟩
    have a1 : ei *ᵥ (ι' *ᵥ z) = ι' *ᵥ z := by rw [mulVec_mulVec, heiι]
    have a2 : X * ei = ex * X * ei := by
      have : X * ei = (ex + ei + ey) * X * ei := by rw [hsum, Matrix.one_mul]
      rw [this, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, Matrix.add_mul, c11, c21, add_zero, add_zero]
    have h1 : X *ᵥ (ι' *ᵥ z) = ex *ᵥ ((X * ei) *ᵥ (ι' *ᵥ z)) := by
      calc X *ᵥ (ι' *ᵥ z) = (X * ei) *ᵥ (ι' *ᵥ z) := by rw [← mulVec_mulVec, a1]
        _ = (ex * (X * ei)) *ᵥ (ι' *ᵥ z) := by rw [← Matrix.mul_assoc, ← a2]
        _ = ex *ᵥ ((X * ei) *ᵥ (ι' *ᵥ z)) := (mulVec_mulVec _ _ _).symm
    refine ⟨cy ⬝ᵥ ((X * ei) *ᵥ (ι' *ᵥ z)), ?_⟩
    have hM' : M *ᵥ (ι' *ᵥ z) = ι' *ᵥ z + X *ᵥ (ι' *ᵥ z) := by rw [hX, sub_mulVec, one_mulVec]; abel
    rw [hM', h1, hex, vecMulVec_mulVec, op_smul_eq_smul]

end GlobalTheory.UnipHaar.RadMem
