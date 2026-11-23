import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGauss
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLogDerivQExpansionModPrimePowUnique
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLogDerivQExpansionModPrimePowOfTranslationStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

noncomputable section
namespace GlobalTheory.UlCusp

variable {Ω : Type} [Field Ω]

theorem eOm_spec [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) :
    ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
  obtain ⟨ζ, hζ⟩ := Api.exists_root_of_isAlgClosed ε x.den_pos
  have h : ∃ a, ε a = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := by
    refine ⟨ζ ^ x.num, ?_⟩
    rw [map_zpow₀, hζ, ← Complex.exp_int_mul]
    congr 1
    conv_rhs => rw [← Rat.num_div_den x]
    push_cast; ring
  exact Function.invFun_eq h

theorem eOm_add [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x y : ℚ) : eOm ε (x + y) = eOm ε x * eOm ε y := by
  apply Api.eOm_eq_of
  rw [map_mul, eOm_spec, eOm_spec, ← Complex.exp_add]; congr 1; push_cast; ring

theorem eOm_intCast [IsAlgClosed Ω] (ε : Ω →+* ℂ) (m : ℤ) : eOm ε (m : ℚ) = 1 := by
  apply Api.eOm_eq_of
  rw [map_one]
  have := Complex.exp_int_mul_two_pi_mul_I m
  rw [← this]; congr 1; push_cast; ring

theorem eOm_zero [IsAlgClosed Ω] (ε : Ω →+* ℂ) : eOm ε 0 = 1 := by
  simpa using eOm_intCast ε 0

theorem eOm_nsmul [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) (k : ℕ) : eOm ε (k * x) = eOm ε x ^ k := by
  induction k with
  | zero => simpa using eOm_zero ε
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, eOm_add, ih, pow_succ]

theorem eOm_pow_den [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) : eOm ε x ^ x.den = 1 := by
  rw [← eOm_nsmul]
  have : (x.den : ℚ) * x = (x.num : ℚ) := by
    have := Rat.mul_den_eq_num x; rw [mul_comm]; exact this
  rw [this, eOm_intCast]

theorem eOm_mem [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) : eOm ε x ∈ A := by
  rcases A.mem_or_inv_mem (eOm ε x) with h | h
  · exact h
  · have hd := eOm_pow_den ε x
    have h0 : eOm ε x ≠ 0 := by rintro h0; rw [h0, zero_pow x.den_pos.ne'] at hd; exact zero_ne_one hd
    have : eOm ε x = (eOm ε x)⁻¹ ^ (x.den - 1) := by
      rw [inv_pow]; exact eq_inv_of_mul_eq_one_left (by rw [← pow_succ', Nat.sub_add_cancel x.den_pos, hd])
    rw [this]; exact pow_mem h _

theorem eOm_inv_mem [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) : (eOm ε x)⁻¹ ∈ A := by
  have : (eOm ε x)⁻¹ = eOm ε (-x) := by
    exact inv_eq_of_mul_eq_one_right (by rw [← eOm_add, add_neg_cancel, eOm_zero])
  rw [this]; exact eOm_mem ε A _

theorem eOm_ne_zero [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) : eOm ε x ≠ 0 := by
  intro h; have := eOm_pow_den ε x; rw [h, zero_pow x.den_pos.ne'] at this; exact zero_ne_one this

theorem cm_mul_of_char {R : Type*} [CommRing R] (c : ℚ → R) (hc : ∀ x y, c (x + y) = c x * c y)
    (φ ψ : HahnSeries ℚ R) : cm c (φ * ψ) = cm c φ * cm c ψ := by
  ext r
  have h1 : (cm c φ).support ⊆ φ.support := fun s hs h => hs (by rw [Api.coeff_cm, h, mul_zero])
  have h2 : (cm c ψ).support ⊆ ψ.support := fun s hs h => hs (by rw [Api.coeff_cm, h, mul_zero])
  rw [Api.coeff_cm, HahnSeries.coeff_mul (x := φ), Finset.mul_sum, HahnSeries.coeff_mul_right' ψ.isPWO_support h2]
  rw [Finset.sum_subset (Finset.antidiagonal_mono_left (hs := φ.isPWO_support) h1)]
  · refine Finset.sum_congr rfl fun ij hij => ?_
    have := (Finset.mem_addAntidiagonal.1 hij).2.2
    rw [Api.coeff_cm, Api.coeff_cm, ← this, hc]; ring
  · intro ij hij hn
    have hm := Finset.mem_addAntidiagonal.1 hij
    have : (cm c φ).coeff ij.1 = 0 := by
      by_contra h0
      exact hn (Finset.mem_addAntidiagonal.2 ⟨h0, hm.2.1, hm.2.2⟩)
    rw [this, zero_mul]

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

theorem ent_piece (l j : ℕ) (hl : 0 < l) (i k : Fin 2) :
    ent (toGQ !![1, 0; 0, (l : ℤ)] * ofSL (ModularGroup.T ^ j)) i k = (!![1, (j : ℚ); 0, (l : ℚ)] : Matrix (Fin 2) (Fin 2) ℚ) i k := by
  have hdet : (0 : ℤ) < (!![1, 0; 0, (l : ℤ)] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; exact_mod_cast hl
  have hT : ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, (j : ℤ); 0, 1] := by
    have h := ModularGroup.coe_T_zpow (j : ℤ)
    rw [zpow_natCast] at h
    exact h
  have hS : (((ofSL (ModularGroup.T ^ j) : GQ) : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((ModularGroup.T ^ j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast) := rfl
  simp only [ent, toGQ, dif_pos hdet, Subgroup.coe_mul, Units.val_mul, hS, hT,
    Matrix.GeneralLinearGroup.mkOfDetNeZero]
  fin_cases i <;> fin_cases k <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

variable {Ω : Type} [Field Ω]

theorem coeff_S (ε : Ω →+* ℂ) (b : ℚ) {d : ℚ} (hd : 0 < d) (χ : HahnSeries ℚ Ω) (r : ℚ) :
    (sub ε 1 b d χ).coeff r = eOm ε (r * d * b / d) * χ.coeff (r * d) := by
  have h : (0 : ℚ) < 1 / d := by positivity
  rw [sub, Api.coeff_scale h, Api.coeff_cm, one_div, div_inv_eq_mul]

theorem S_mul [IsAlgClosed Ω] (ε : Ω →+* ℂ) (b d : ℚ) (χ ψ : HahnSeries ℚ Ω) :
    sub ε 1 b d (χ * ψ) = sub ε 1 b d χ * sub ε 1 b d ψ := by
  unfold sub
  rw [cm_mul_of_char _ (fun x y => by rw [← eOm_add]; congr 1; ring), Api.scale_mul]

theorem S_sub (ε : Ω →+* ℂ) (b : ℚ) {d : ℚ} (hd : 0 < d) (χ ψ : HahnSeries ℚ Ω) :
    sub ε 1 b d (χ - ψ) = sub ε 1 b d χ - sub ε 1 b d ψ := by
  ext r; rw [HahnSeries.coeff_sub, coeff_S ε b hd, coeff_S ε b hd, coeff_S ε b hd, HahnSeries.coeff_sub, mul_sub]

theorem S_smul (ε : Ω →+* ℂ) (b : ℚ) {d : ℚ} (hd : 0 < d) (c : Ω) (χ : HahnSeries ℚ Ω) :
    sub ε 1 b d (c • χ) = c • sub ε 1 b d χ := by
  ext r; rw [HahnSeries.coeff_smul, coeff_S ε b hd, coeff_S ε b hd, HahnSeries.coeff_smul, smul_eq_mul, smul_eq_mul]; ring

theorem S_int [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (b : ℚ) {d : ℚ} (hd : 0 < d)
    {χ : HahnSeries ℚ Ω} (h : ∀ r, χ.coeff r ∈ A) (r : ℚ) : (sub ε 1 b d χ).coeff r ∈ A := by
  rw [coeff_S ε b hd]; exact mul_mem (eOm_mem ε A _) (h _)

theorem S_prim [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (b : ℚ) {d : ℚ} (hd : 0 < d)
    {χ : HahnSeries ℚ Ω} (h : Prim A χ) : Prim A (sub ε 1 b d χ) := by
  obtain ⟨hi, r, hr, hu⟩ := h
  refine ⟨S_int ε A b hd hi, r / d, ?_, ?_⟩
  · rw [coeff_S ε b hd, div_mul_cancel₀ r hd.ne']
    exact mul_ne_zero (eOm_ne_zero ε _) hr
  · rw [coeff_S ε b hd, div_mul_cancel₀ r hd.ne', mul_inv]
    exact mul_mem (eOm_inv_mem ε A _) hu

theorem theta_S [Algebra ℚ Ω] (ε : Ω →+* ℂ) (b : ℚ) {d : ℚ} (hd : 0 < d) (χ : HahnSeries ℚ Ω) :
    theta 1 (sub ε 1 b d χ) = (algebraMap ℚ Ω d)⁻¹ • sub ε 1 b d (theta 1 χ) := by
  have hd' : algebraMap ℚ Ω d ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (algebraMap ℚ Ω).injective]; exact hd.ne'
  ext r
  rw [HahnSeries.coeff_smul, coeff_S ε b hd, smul_eq_mul]
  show algebraMap ℚ Ω (1 * r) * (sub ε 1 b d χ).coeff r = _
  rw [coeff_S ε b hd]
  show algebraMap ℚ Ω (1 * r) * (eOm ε (r * d * b / d) * χ.coeff (r * d)) =
    (algebraMap ℚ Ω d)⁻¹ * (eOm ε (r * d * b / d) * (algebraMap ℚ Ω (1 * (r * d)) * χ.coeff (r * d)))
  rw [show (1 : ℚ) * (r * d) = (1 * r) * d by ring, map_mul]
  field_simp
  rw [map_mul, map_one]; ring

theorem exp_piece [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l j : ℕ) (hl : 0 < l) (x : X.K) :
    X.exp (X.sl (ofSL (ModularGroup.T ^ j)) (X.sl (toGQ !![1, 0; 0, (l : ℤ)]) x)) = sub ε 1 (j : ℚ) (l : ℚ) (X.exp x) := by
  rw [← X.sl_mul, Api.exp_sl_upper X _ (by rw [ent_piece l j hl]; simp) x, ent_piece l j hl, ent_piece l j hl,
    ent_piece l j hl]
  simp

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

variable {Ω : Type} [Field Ω]

def Dv (A : ValuationSubring Ω) (l m : ℕ) (χ : HahnSeries ℚ Ω) : Prop := ∀ r, CgA A l m (χ.coeff r) 0

theorem dv_add {A : ValuationSubring Ω} {l m : ℕ} {χ ψ : HahnSeries ℚ Ω} (h1 : Dv A l m χ) (h2 : Dv A l m ψ) :
    Dv A l m (χ + ψ) := by
  intro r
  obtain ⟨z, hz, e⟩ := h1 r
  obtain ⟨w, hw, e'⟩ := h2 r
  refine ⟨z + w, add_mem hz hw, ?_⟩
  rw [sub_zero] at e e' ⊢
  rw [HahnSeries.coeff_add, e, e', mul_add]

theorem dv_neg {A : ValuationSubring Ω} {l m : ℕ} {χ : HahnSeries ℚ Ω} (h1 : Dv A l m χ) : Dv A l m (-χ) := by
  intro r
  obtain ⟨z, hz, e⟩ := h1 r
  refine ⟨-z, neg_mem hz, ?_⟩
  rw [sub_zero] at e ⊢
  rw [HahnSeries.coeff_neg, e, mul_neg]

theorem dv_mul {A : ValuationSubring Ω} {l m : ℕ} {χ G : HahnSeries ℚ Ω} (h1 : Dv A l m χ) (hG : ∀ r, G.coeff r ∈ A) :
    Dv A l m (χ * G) := GlobalTheory.Glue.DlUniq.cg_mul A l m χ G h1 hG

theorem dv_mul_left {A : ValuationSubring Ω} {l m : ℕ} {χ G : HahnSeries ℚ Ω} (hG : ∀ r, G.coeff r ∈ A) (h1 : Dv A l m χ) :
    Dv A l m (G * χ) := by rw [mul_comm]; exact dv_mul h1 hG

theorem dv_S [IsAlgClosed Ω] (ε : Ω →+* ℂ) {A : ValuationSubring Ω} {l m : ℕ} (b : ℚ) {d : ℚ} (hd : 0 < d)
    {χ : HahnSeries ℚ Ω} (h1 : Dv A l m χ) : Dv A l m (sub ε 1 b d χ) := by
  intro r
  obtain ⟨z, hz, e⟩ := h1 (r * d)
  refine ⟨eOm ε (r * d * b / d) * z, mul_mem (eOm_mem ε A _) hz, ?_⟩
  rw [sub_zero] at e ⊢
  rw [coeff_S ε b hd, e]; ring

theorem dv_inv [Algebra ℚ Ω] {A : ValuationSubring Ω} {l m : ℕ} (hl : 0 < l) {χ : HahnSeries ℚ Ω}
    (h1 : Dv A l (m + 1) χ) : Dv A l m (HahnSeries.C ((l : Ω)⁻¹) * χ) := by
  have hl' : (l : Ω) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ Ω) l]
    exact (map_ne_zero_iff _ (algebraMap ℚ Ω).injective).2 (by exact_mod_cast hl.ne')
  intro r
  obtain ⟨z, hz, e⟩ := h1 r
  refine ⟨z, hz, ?_⟩
  rw [sub_zero] at e ⊢
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, e, smul_eq_mul, pow_succ]
  field_simp

theorem dv_of_succ {A : ValuationSubring Ω} {l m : ℕ} {χ : HahnSeries ℚ Ω} (h1 : Dv A l (m + 1) χ) : Dv A l m χ := by
  intro r
  obtain ⟨z, hz, e⟩ := h1 r
  refine ⟨l * z, mul_mem (natCast_mem A l) hz, ?_⟩
  rw [e, pow_succ]; ring

theorem int_prod [Algebra ℚ Ω] {A : ValuationSubring Ω} (S : Finset ℕ) (F : ℕ → HahnSeries ℚ Ω) (h : ∀ j, ∀ r, (F j).coeff r ∈ A) :
    ∀ r, (∏ j ∈ S, F j).coeff r ∈ A := by
  induction S using Finset.induction_on with
  | empty => intro r; rw [Finset.prod_empty, HahnSeries.coeff_one]; split_ifs <;> simp
  | insert j S hj ih =>
    intro r; rw [Finset.prod_insert hj]; exact GlobalTheory.DlEx.intA_mul A (h j) ih r

def Br [Algebra ℚ Ω] (x y : HahnSeries ℚ Ω) : HahnSeries ℚ Ω := theta 1 x * y - x * theta 1 y

theorem Br_mul [Algebra ℚ Ω] (x X y Y : HahnSeries ℚ Ω) : Br (x * X) (y * Y) = Br x y * (X * Y) + (x * y) * Br X Y := by
  unfold Br
  rw [(GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (1 : ℚ) x X).1, (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (1 : ℚ) y Y).1]; ring

theorem Br_S [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (l : ℕ) (hl : 0 < l) (b : ℚ) (x y : HahnSeries ℚ Ω) :
    Br (sub ε 1 b l x) (sub ε 1 b l y) = HahnSeries.C ((l : Ω)⁻¹) * sub ε 1 b l (Br x y) := by
  have hd : (0 : ℚ) < l := by exact_mod_cast hl
  unfold Br
  rw [theta_S ε b hd, theta_S ε b hd, S_sub ε b hd, S_mul, S_mul, map_natCast, ← HahnSeries.C_mul_eq_smul,
    ← HahnSeries.C_mul_eq_smul]
  ring

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

variable {Ω : Type} [Field Ω]

theorem key_ind [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (l n : ℕ) (hl : 0 < l)
    (φ0 Ea Eb : HahnSeries ℚ Ω) (hEa : ∀ r, Ea.coeff r ∈ A) (hEb : ∀ r, Eb.coeff r ∈ A)
    (hD : Dv A l (n + 1) (φ0 * Ea * Eb - Br Ea Eb)) (S : Finset ℕ) :
    Dv A l n (Br (∏ j ∈ S, sub ε 1 (j : ℚ) (l : ℚ) Ea) (∏ j ∈ S, sub ε 1 (j : ℚ) (l : ℚ) Eb) -
      (∑ j ∈ S, HahnSeries.C ((l : Ω)⁻¹) * sub ε 1 (j : ℚ) (l : ℚ) φ0) *
        ∏ j ∈ S, (sub ε 1 (j : ℚ) (l : ℚ) Ea * sub ε 1 (j : ℚ) (l : ℚ) Eb)) := by
  have hd : (0 : ℚ) < l := by exact_mod_cast hl
  induction S using Finset.induction_on with
  | empty =>
    intro r
    refine ⟨0, zero_mem A, ?_⟩
    simp [Br]
  | insert j S hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj, Finset.prod_insert hj]
    set Δ := φ0 * Ea * Eb - Br Ea Eb with hΔ
    set x := sub ε 1 (j : ℚ) (l : ℚ) Ea
    set y := sub ε 1 (j : ℚ) (l : ℚ) Eb
    set X := ∏ j ∈ S, sub ε 1 (j : ℚ) (l : ℚ) Ea
    set Y := ∏ j ∈ S, sub ε 1 (j : ℚ) (l : ℚ) Eb
    set Q := ∏ j ∈ S, (sub ε 1 (j : ℚ) (l : ℚ) Ea * sub ε 1 (j : ℚ) (l : ℚ) Eb)
    set Sg := ∑ j ∈ S, HahnSeries.C ((l : Ω)⁻¹) * sub ε 1 (j : ℚ) (l : ℚ) φ0
    have hXY : X * Y = Q := (Finset.prod_mul_distrib).symm
    have hB : Br Ea Eb = φ0 * Ea * Eb - Δ := by rw [hΔ]; ring
    have e : Br (x * X) (y * Y) - (HahnSeries.C ((l : Ω)⁻¹) * sub ε 1 (j : ℚ) (l : ℚ) φ0 + Sg) * (x * y * Q) =
        -(HahnSeries.C ((l : Ω)⁻¹) * sub ε 1 (j : ℚ) (l : ℚ) Δ) * Q + (x * y) * (Br X Y - Sg * Q) := by
      rw [Br_mul, hXY, Br_S ε l hl, hB, S_sub ε _ hd, S_mul, S_mul]
      ring
    rw [e]
    have hQ : ∀ r, Q.coeff r ∈ A := int_prod S _ (fun i => GlobalTheory.DlEx.intA_mul A (S_int ε A _ hd hEa) (S_int ε A _ hd hEb))
    have hxy : ∀ r, (x * y).coeff r ∈ A := GlobalTheory.DlEx.intA_mul A (S_int ε A _ hd hEa) (S_int ε A _ hd hEb)
    exact dv_add (dv_mul (dv_neg (dv_inv hl (dv_S ε _ hd hD))) hQ) (dv_mul_left hxy ih)

end GlobalTheory.UlCusp

noncomputable section
namespace GlobalTheory.UlCusp

variable {Ω : Type} [Field Ω]

theorem prim_one (A : ValuationSubring Ω) : Prim A (1 : HahnSeries ℚ Ω) := by
  refine ⟨fun r => ?_, 0, ?_, ?_⟩
  · rw [HahnSeries.coeff_one]; split_ifs <;> simp
  · simp
  · simp

theorem prim_prod (A : ValuationSubring Ω) (S : Finset ℕ) (F : ℕ → HahnSeries ℚ Ω) (h : ∀ j, Prim A (F j)) :
    Prim A (∏ j ∈ S, F j) := by
  induction S using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact prim_one A
  | insert j S hj ih => rw [Finset.prod_insert hj]; exact GlobalTheory.Glue.Prim.mul A _ _ (h j) ih

theorem isAlgClosure_of_tower [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) : IsAlgClosure ℚ Ω := by
  refine ⟨inferInstance, ⟨fun c => ?_⟩⟩
  obtain ⟨D, hD, hk⟩ := X.bdd (algebraMap Ω X.K c)
  obtain ⟨k, hint⟩ := hk 0
  have hc : (X.exp (algebraMap Ω X.K c)).coeff 0 = c := by
    rw [X.exp.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply, HahnSeries.ofPowerSeries_C]
    simp [HahnSeries.C_apply, HahnSeries.coeff_single, Pi.single_apply]
  rw [hc] at hint
  have h1 : IsIntegral ℚ ((D : Ω) ^ k * c) := hint.tower_top
  have h2 : IsIntegral ℚ (algebraMap ℚ Ω (((D : ℚ) ^ k)⁻¹)) := isIntegral_algebraMap
  have hD' : (D : Ω) ^ k ≠ 0 := pow_ne_zero _ (by
    rw [← map_natCast (algebraMap ℚ Ω) D]
    exact (map_ne_zero_iff _ (algebraMap ℚ Ω).injective).2 (by exact_mod_cast hD.ne'))
  have : c = algebraMap ℚ Ω (((D : ℚ) ^ k)⁻¹) * ((D : Ω) ^ k * c) := by
    rw [map_inv₀, map_pow, map_natCast, ← mul_assoc, inv_mul_cancel₀ hD', one_mul]
  rw [this]
  exact (h2.mul h1).isAlgebraic

end GlobalTheory.UlCusp

namespace GlobalTheory.UlCusp

theorem dl_norm_uq : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ), (l : Ω) ∈ A.nonunits →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), X.sl (ofSL ModularGroup.T) f = f → IsDl X A l (n + 1) 1 f φ →
    IsDl X A l n 1 (nrmT X l (X.sl (toGQ !![1, 0; 0, (l : ℤ)]) f)) (uq l φ) := by
  intro Ω _ _ _ ε X A l _ n hl f φ hT hφ
  haveI : IsAlgClosure ℚ Ω := isAlgClosure_of_tower X
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  have hd : (0 : ℚ) < l := by exact_mod_cast hl0
  have Hj : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨g, h1, h2⟩ := X.j_hol; exact ⟨g, h2, h1⟩

  have hf0 : f ≠ 0 := by
    obtain ⟨-, a, b, κ, hκ, hfb, hPa, -, -⟩ := hφ
    rintro rfl
    rw [zero_mul, eq_comm, mul_eq_zero] at hfb
    rcases hfb with h | h
    · exact hκ ((map_eq_zero_iff _ (algebraMap Ω X.K).injective).1 h)
    · obtain ⟨-, r, hr, -⟩ := hPa
      exact hr (by rw [h, map_zero, HahnSeries.coeff_zero])
  have hKT : f ∈ KT X 1 := by
    show (X.sl (ofSL (ModularGroup.T ^ 1))) f = f
    rw [pow_one]; exact hT
  obtain ⟨φ0, hφ0, hsp⟩ := GlobalTheory.T.exists_logDerivQExpansion_modPrimePow_of_translationInvariant ε X Hj l A hl (n + 1) 1 f one_pos hf0 hKT
  rw [Nat.cast_one] at hφ0
  have huniq := GlobalTheory.Glue.isDl_unique ε X Hj l A hl (n + 1) 1 f φ φ0 hφ hφ0
  obtain ⟨hφ0A, a, b, κ, hκ, hfb, hPa, hPb, hc0⟩ := hφ0
  have hφA := hφ.1
  set D : GQ := toGQ !![1, 0; 0, (l : ℤ)]

  have hE : ∀ x : X.K, X.exp (nrmT X l (X.sl D x)) = ∏ j ∈ Finset.range l, sub ε 1 (j : ℚ) (l : ℚ) (X.exp x) := by
    intro x
    rw [nrmT, map_prod]
    exact Finset.prod_congr rfl fun j _ => exp_piece X l j hl0 x
  have hEq : nrmT X l (X.sl D f) * nrmT X l (X.sl D b) = algebraMap Ω X.K (κ ^ l) * nrmT X l (X.sl D a) := by
    unfold nrmT
    rw [← Finset.prod_mul_distrib]
    have : ∀ j ∈ Finset.range l, X.sl (ofSL (ModularGroup.T ^ j)) (X.sl D f) * X.sl (ofSL (ModularGroup.T ^ j)) (X.sl D b) =
        algebraMap Ω X.K κ * X.sl (ofSL (ModularGroup.T ^ j)) (X.sl D a) := by
      intro j _
      rw [← map_mul, ← map_mul, hfb, map_mul, map_mul, AlgEquiv.commutes, AlgEquiv.commutes]
    rw [Finset.prod_congr rfl this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, map_pow]
  have hEa : ∀ r, (X.exp a).coeff r ∈ A := hPa.1
  have hEb : ∀ r, (X.exp b).coeff r ∈ A := hPb.1
  have hD : Dv A l (n + 1) (φ0 * X.exp a * X.exp b - Br (X.exp a) (X.exp b)) := by
    intro r
    obtain ⟨z, hz, e⟩ := hc0 r
    exact ⟨z, hz, by unfold Br; rw [sub_zero, HahnSeries.coeff_sub, e]⟩
  have hkey := key_ind ε A l n hl0 φ0 (X.exp a) (X.exp b) hEa hEb hD (Finset.range l)
  have hsum : (∑ j ∈ Finset.range l, HahnSeries.C ((l : Ω)⁻¹) * sub ε 1 (j : ℚ) (l : ℚ) φ0) = uq l φ0 := by
    rw [← Api.hq_eq_uq_of_isAlgClosed (ε := ε) hl0 (fun r hr => by simpa using hsp r hr), hq, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [HahnSeries.C_mul_eq_smul]
  rw [hsum, Finset.prod_mul_distrib] at hkey
  have hdiff : Dv A l n (uq l φ - uq l φ0) := by
    intro r
    rw [HahnSeries.coeff_sub, Api.coeff_uq hl0, Api.coeff_uq hl0]
    split_ifs
    · obtain ⟨z, hz, e⟩ := huniq (l * r)
      refine ⟨l * z, mul_mem (natCast_mem A l) hz, ?_⟩
      rw [sub_zero, e, pow_succ]; ring
    · exact ⟨0, zero_mem A, by simp⟩
  have hQ : ∀ r, ((∏ j ∈ Finset.range l, sub ε 1 (j : ℚ) (l : ℚ) (X.exp a)) *
      (∏ j ∈ Finset.range l, sub ε 1 (j : ℚ) (l : ℚ) (X.exp b))).coeff r ∈ A :=
    GlobalTheory.DlEx.intA_mul A (int_prod _ _ fun j => S_int ε A _ hd hEa) (int_prod _ _ fun j => S_int ε A _ hd hEb)
  have hfin := dv_add (dv_mul hdiff hQ) (dv_neg hkey)
  refine ⟨fun r => ?_, nrmT X l (X.sl D a), nrmT X l (X.sl D b), κ ^ l, pow_ne_zero _ hκ, hEq, ?_, ?_, fun r => ?_⟩
  · rw [Api.coeff_uq hl0]; split_ifs
    · exact hφA _
    · exact zero_mem A
  · rw [hE]; exact prim_prod A _ _ fun j => S_prim ε A _ hd hPa
  · rw [hE]; exact prim_prod A _ _ fun j => S_prim ε A _ hd hPb
  · obtain ⟨z, hz, e⟩ := hfin r
    refine ⟨z, hz, ?_⟩
    rw [sub_zero] at e
    rw [← e, hE, hE, ← HahnSeries.coeff_sub]
    congr 1
    unfold Br
    ring

end GlobalTheory.UlCusp

example : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime] (n : ℕ), (l : Ω) ∈ A.nonunits →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), X.sl (ofSL ModularGroup.T) f = f → IsDl X A l (n + 1) 1 f φ →
    IsDl X A l n 1 (nrmT X l (X.sl (toGQ !![1, 0; 0, (l : ℤ)]) f)) (uq l φ) := GlobalTheory.UlCusp.dl_norm_uq
