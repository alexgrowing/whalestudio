import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SupLeL2PrincipalTorus
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CardToMultisetEqDegree

open Complex ReciprocityTheory.ChartRestriction.G.I2

namespace GlobalTheory

namespace ThetaBound

section General

variable {ι : Type} [Fintype ι]

theorem l2NormSq_nonneg_gaussianTorus (Y : GT ι) (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ) : 0 ≤ Y.l2 q F := by
  unfold GT.l2
  rw [MeasureTheory.average_eq]
  refine MeasureTheory.integral_nonneg_of_ae ?_ |> smul_nonneg (by positivity)
  refine Filter.Eventually.of_forall fun v => ?_
  unfold GT.ptN2
  positivity

theorem le_firstMinimum_of_period_lower_bound (Y : GT ι) (hι : Fintype.card ι ≠ 0) {lam : ℝ}
    (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖) : lam ≤ Y.la1 := by
  refine le_csInf ⟨‖Y.b ⟨0, by omega⟩‖, Y.b ⟨0, by omega⟩,
    Submodule.subset_span ⟨_, rfl⟩, Y.b.ne_zero _, rfl⟩ ?_
  rintro t ⟨x, hx, hx0, rfl⟩
  exact hmin x hx hx0

theorem pointwiseNormSq_le_l2_of_firstMinimum (hsup : GSupStatement) (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ Y.Sec 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    (v : EuclideanSpace ℂ ι) :
    Y.ptN2 1 F v ≤ (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
      (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) ^ 2 * Y.l2 1 F := by
  refine (hsup ι Y 1 le_rfl F hF v).trans (mul_le_mul_of_nonneg_right ?_ (l2NormSq_nonneg_gaussianTorus Y 1 F))
  rw [mul_pow, Real.sq_sqrt (by norm_num), ← pow_mul, mul_comm (Fintype.card ι) 2]
  simp only [Nat.cast_one, one_pow, mul_one, one_mul]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  by_cases hι : Fintype.card ι = 0
  · simp [hι]
  have h1 := le_firstMinimum_of_period_lower_bound Y hι hmin
  have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have h2 : 0 < Y.la1 := hlam.trans_le h1
  gcongr

open Classical in

theorem norm_polyDeriv_le (q : ℕ) (F : EuclideanSpace ℂ ι → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ)
    (hS : ∀ v, ‖F v‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖v‖ ^ 2) ≤ S) (P : MvPolynomial ι ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) :
    ‖polyDeriv P (fun i => EuclideanSpace.single i 1) F 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  rcases Nat.eq_zero_or_pos q with rfl | hq
  swap
  · exact Jet.norm_polyDeriv_le q hq F hF S hS P a hP
  simp only [Nat.cast_zero, zero_mul, neg_zero, Real.exp_zero, mul_one] at hS
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · have h := Jet.norm_polyDeriv_le 1 le_rfl F hF S (fun v => ?_) P 0 hP
    · simpa using h
    · refine le_trans ?_ (hS v)
      refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.mpr ?_)
      have := Real.pi_pos
      have : 0 ≤ ((1 : ℕ) : ℝ) * Real.pi * ‖v‖ ^ 2 := by positivity
      linarith
  · have hb : Bornology.IsBounded (Set.range F) := by
      refine isBounded_iff_forall_norm_le.mpr ⟨Real.sqrt S, ?_⟩
      rintro _ ⟨v, rfl⟩
      exact Real.le_sqrt_of_sq_le (hS v)
    obtain ⟨c, hc⟩ := hF.exists_eq_const_of_bounded hb
    have h0 : polyDeriv P (fun i => EuclideanSpace.single i (1 : ℂ)) F 0 = 0 := by
      unfold polyDeriv
      refine Finset.sum_eq_zero fun m hm => ?_
      have hne : Multiset.card (Finsupp.toMultiset m) ≠ 0 := by
        rw [Jet.card_toMultiset_eq_degree, Jet.degree_eq_of_mem_support hP hm]
        omega
      rw [hc, show Function.const (EuclideanSpace ℂ ι) c = fun _ => c from rfl,
        iteratedFDeriv_const_of_ne hne]
      simp
    rw [h0, norm_zero]
    positivity

end General

section Columns

open TensorLat

variable {E : Type} [Field E] [NumberField E]

theorem norm_polyDeriv_U_le (X : PT E) (q : ℕ) {n : ℕ} (F : (Fin n → Vsp X.dim) → ℂ)
    (hF : Differentiable ℂ F) (S : ℝ) (hS : ∀ v, X.ptN2 q F v ≤ S)
    (P : MvPolynomial (Letter n X.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a)
    (b : Fin n → Vsp X.dim) :
    ‖polyDeriv P dir (X.U q b F) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * Real.sqrt S *
        (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) := by
  set G : EuclideanSpace ℂ (Fin n × Idx X.dim) → ℂ := F ∘ flat.symm with hG
  have hGd : Differentiable ℂ G := hF.comp (flat (n := n) (ι := Idx X.dim)).symm.differentiable
  have e : X.U q b F = (fun v => cexp (q * Real.pi * Hf v (flat b) -
      q * Real.pi * Hf (flat b) (flat b) / 2) * G (v - flat b)) ∘ flat := by
    funext v
    simp only [PT.U, Function.comp, hG, Hf_flat, ← map_sub,
      ContinuousLinearEquiv.symm_apply_apply]
  have h := norm_polyDeriv_le q _ (Jet.differentiable_translate q (flat b) hGd) S
    (fun v => by
      rw [Jet.norm_translate]
      have h1 := hS (flat.symm (v - flat b))
      rwa [PT.ptN2, HC_self_re, ContinuousLinearEquiv.apply_symm_apply] at h1) P a hP
  rw [e, Jet.polyDeriv_comp_equiv, map_zero]
  convert h using 3
  funext l
  rw [Function.comp_apply]
  convert flat_dir l

theorem col_mem_Sec (X : PT E) {q : ℕ} {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1) :
    (fun z => s fun _ => z) ∈ (gtOf X q).Sec q := by
  refine ⟨hs.1.comp (differentiable_pi.2 fun _ => differentiable_id), fun γ hγ v => ?_⟩
  have e : (fun _ : Fin 1 => v + γ) = (fun _ => v) + (fun _ => γ) := by funext j; simp
  simp only [e]
  rw [hs.2 (fun _ => γ) (fun _ => hγ) (fun _ => v)]
  simp [HC, gtOf]

theorem oneColumn_pointwiseNorm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) (x : Vsp X.dim) :
    (gtOf X q).ptN2 q (fun z => s fun _ => z) x = X.ptN2 q s fun _ => x := by
  simp [GT.ptN2, PT.ptN2, HC, jof_Hf_self_re]

theorem oneColumn_l2Norm_eq_torus (X : PT E) (q : ℕ) (s : (Fin 1 → Vsp X.dim) → ℂ) :
    (gtOf X q).l2 q (fun z => s fun _ => z) = X.l2 q s := by
  rw [l2_norm_fundamental_domain, GT.l2]
  simp only [oneColumn_pointwiseNorm_eq_torus]
  rfl

theorem l2_pos_of_mem_sec_of_ne_zero (X : PT E) {q : ℕ} (hq : 1 ≤ q) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec q 1)
    (hne : s ≠ 0) : 0 < X.l2 q s := by
  refine lt_of_le_of_ne ?_ fun h => hne (eq_zero_of_l2_eq_zero X packingCount hq hs h.symm)
  rw [← oneColumn_l2Norm_eq_torus]
  exact l2NormSq_nonneg_gaussianTorus _ _ _

theorem diagonal_pointwiseNormSq_le_l2 (X : PT E) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖) (x : Vsp X.dim) :
    X.ptN2 1 s (fun _ => x) ≤ (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx X.dim)) /
      (Real.sqrt Real.pi * lam)) ^ Fintype.card (Idx X.dim)) ^ 2 * X.l2 1 s := by
  rw [← oneColumn_pointwiseNorm_eq_torus, ← oneColumn_l2Norm_eq_torus]
  exact pointwiseNormSq_le_l2_of_firstMinimum sup_le_l2_principal_torus (gtOf X 1) (col_mem_Sec X hs) hlam hmin x

theorem differentiable_pullback_tensor (X : PT E) {n : ℕ} (π : Vsp X.dim →ₗ[ℂ] Vsp X.dim)
    {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : Differentiable ℂ s) :
    Differentiable ℂ (s0 X (n := n) π s) := by
  have hc : ContDiff ℂ (⊤ : ℕ∞) (s0 X (n := n) π s) := by
    refine contDiff_prod fun k _ => (contDiff_of_diff hs).comp (contDiff_pi.2 fun _ => ?_)
    exact (LinearMap.toContinuousLinearMap π).contDiff.comp (contDiff_apply ℂ (Vsp X.dim) k)
  exact hc.differentiable (by simp)

theorem pointwiseNormSq_pullback_tensor_eq_prod (X : PT E) {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim}
    (hπ : ∀ v w, Hf (π v) (π w) = q * Hf v w) (s : (Fin 1 → Vsp X.dim) → ℂ)
    (v : Fin n → Vsp X.dim) :
    X.ptN2 q (s0 X π s) v = ∏ k, X.ptN2 1 s fun _ => π (v k) := by
  unfold PT.ptN2 s0
  rw [norm_prod, ← Finset.prod_pow, Finset.prod_mul_distrib, ← Real.exp_sum]
  congr 2
  simp only [HC, Complex.re_sum, Fin.sum_univ_one, hπ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]
  push_cast
  ring

theorem norm_polyDeriv_pullback_tensor_le (X : PT E) {q n : ℕ} {π : Vsp X.dim →ₗ[ℂ] Vsp X.dim}
    (hπ : ∀ v w, Hf (π v) (π w) = q * Hf v w) {s : (Fin 1 → Vsp X.dim) → ℂ} (hs : s ∈ X.Sec 1 1)
    {lam : ℝ} (hlam : 0 < lam) (hmin : ∀ x ∈ X.L, x ≠ 0 → lam ≤ ‖x‖)
    (P : MvPolynomial (Letter n X.dim) ℂ) (a : ℕ) (hP : P.IsHomogeneous a)
    (b : Fin n → Vsp X.dim) :
    ‖polyDeriv P dir (X.U q b (s0 X π s)) 0‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx X.dim)) /
          (Real.sqrt Real.pi * lam)) ^ Fintype.card (Idx X.dim)) ^ n *
        Real.sqrt (X.l2 1 s) ^ n := by
  set C : ℝ := Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx X.dim)) /
    (Real.sqrt Real.pi * lam)) ^ Fintype.card (Idx X.dim) with hC
  have hC0 : 0 ≤ C := by positivity
  have hl : 0 ≤ X.l2 1 s := by rw [← oneColumn_l2Norm_eq_torus]; exact l2NormSq_nonneg_gaussianTorus _ _ _
  have h := norm_polyDeriv_U_le X q (s0 X π s) (differentiable_pullback_tensor X π hs.1)
    ((C ^ n * Real.sqrt (X.l2 1 s) ^ n) ^ 2) (fun v => by
      rw [pointwiseNormSq_pullback_tensor_eq_prod X hπ]
      calc ∏ k, X.ptN2 1 s (fun _ => π (v k)) ≤ ∏ _k : Fin n, C ^ 2 * X.l2 1 s :=
            Finset.prod_le_prod (fun k _ => by unfold PT.ptN2; positivity)
              fun k _ => diagonal_pointwiseNormSq_le_l2 X hs hlam hmin _
        _ = _ := by
            rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, ← pow_mul,
              mul_comm n 2, pow_mul, mul_pow C, Real.sq_sqrt hl]) P a hP b
  rw [Real.sqrt_sq (by positivity)] at h
  refine h.trans_eq ?_
  ring

end Columns

end ThetaBound

open Classical in

theorem theta_value_bound (hsup : GSupStatement) {ι : Type} [Fintype ι] (U : ℕ → EuclideanSpace ℂ ι → (EuclideanSpace ℂ ι → ℂ) → EuclideanSpace ℂ ι → ℂ)
    (hU : ∀ (q : ℕ) a F v, U q a F v = cexp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) * F (v - a))
    (Y : GT ι) (F : EuclideanSpace ℂ ι → ℂ) (hF : F ∈ Y.Sec 1) (lam : ℝ) (hlam : 0 < lam) (hmin : ∀ x ∈ lat Y.b, x ≠ 0 → lam ≤ ‖x‖)
    {κ : Type} (s : Finset κ) (c : κ → ℂ) (hc : ∀ j ∈ s, ‖c j‖ ≤ 1) (y : κ → EuclideanSpace ℂ ι)
    (P : MvPolynomial ι ℂ) (a : ℕ) (hP : P.IsHomogeneous a) :
    ‖∑ j ∈ s, c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
      s.card * (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) / (Real.sqrt Real.pi * lam)) ^ Fintype.card ι) * Real.sqrt (Y.l2 1 F) := by
  set C : ℝ := Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card ι) /
    (Real.sqrt Real.pi * lam)) ^ Fintype.card ι with hC
  have hC0 : 0 ≤ C := by positivity
  have key : ∀ j ∈ s,
      ‖c j * polyDeriv P (fun i => EuclideanSpace.single i 1) (U 1 (y j) F) 0‖ ≤
        (∑ m ∈ P.support, ‖P.coeff m‖) * (Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) * C *
          Real.sqrt (Y.l2 1 F) := by
    intro j hj
    have h := translate_jet_bound U hU 1 le_rfl F hF.1 (C ^ 2 * Y.l2 1 F)
      (ThetaBound.pointwiseNormSq_le_l2_of_firstMinimum hsup Y hF hlam hmin) P a hP (y j)
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hC0, Nat.cast_one, one_mul] at h
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (hc j hj)).trans (h.trans_eq ?_)
    ring
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ _ key).trans_eq ?_)
  rw [nsmul_eq_mul]
  ring

theorem norm_thAn_le {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {r : ℕ}
    {X : ReciprocityTheory.ChartRestriction.G.FD.Data E r} {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (A : TorusAt X x)
    (q n : ℕ) (π : Vsp A.T.dim →ₗ[ℂ] Vsp A.T.dim) (hπ : IsPi A.T q π)
    (b : Fin n → Vsp A.T.dim) (P : MvPolynomial (Letter n A.T.dim) ℂ) (a : ℕ)
    (hP : P.IsHomogeneous a) (lam : ℝ) (hlam : 0 < lam)
    (hmin : ∀ γ ∈ A.T.L, γ ≠ 0 → lam ≤ ‖γ‖) :
    ‖thAn A q n π b P‖ ≤
      (∑ m ∈ P.support, ‖P.coeff m‖) * (q * Real.pi * Real.exp 1 * a) ^ ((a : ℝ) / 2) *
        (Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * Fintype.card (Idx A.T.dim)) /
          (Real.sqrt Real.pi * lam)) ^ Fintype.card (Idx A.T.dim)) ^ n := by
  have hpos : 0 < Real.sqrt (A.T.l2 1 A.s) :=
    Real.sqrt_pos.mpr (ThetaBound.l2_pos_of_mem_sec_of_ne_zero A.T le_rfl A.s_mem A.s_ne)
  rw [thAn, norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hpos.le,
    div_le_iff₀ (pow_pos hpos n)]
  exact ThetaBound.norm_polyDeriv_pullback_tensor_le A.T hπ.2.2.1 A.s_mem hlam hmin P a hP b

end GlobalTheory
