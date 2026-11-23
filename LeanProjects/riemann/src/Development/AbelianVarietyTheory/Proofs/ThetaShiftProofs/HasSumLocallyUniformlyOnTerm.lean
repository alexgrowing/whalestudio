import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.DegeneratingToriPeriodMapEqBaseOfYEqZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SummableExpNegSumAbs

noncomputable section

open Filter Topology

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm eTwoPi)

theorem summable_exp_neg_sum_abs_int {ι : Type} [Fintype ι] :
    Summable fun m : ι → ℤ => Real.exp (-∑ i, |(m i : ℝ)|) := by
  first
  | exact @_root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs
  | exact _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs
  | (apply _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs <;> assumption)
  | (intros; apply _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SummableExpNegAbsSum.summable_exp_neg_sum_abs ..)

namespace AnArc

theorem norm_e (x : ℂ) : ‖eTwoPi x‖ = Real.exp (-(2 * Real.pi * x.im)) := by
  rw [eTwoPi, Complex.norm_exp]; congr 1; simp

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

def size (μ : A.X) : ℝ := ∑ i, |((Module.Free.chooseBasis ℤ A.X).repr μ i : ℝ)|

theorem size_nonneg (μ : A.X) : 0 ≤ A.size μ := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem summable_exp_neg_size : Summable fun μ => Real.exp (-A.size μ) :=
  summable_exp_neg_sum_abs_int.comp_injective (Module.Free.chooseBasis ℤ A.X).equivFun.injective

theorem norm_le_mul_size {E : Type*} [SeminormedAddCommGroup E] (f : A.X →+ E) {C : ℝ}
    (hC : ∀ i, ‖f (Module.Free.chooseBasis ℤ A.X i)‖ ≤ C) (μ : A.X) : ‖f μ‖ ≤ C * A.size μ := by
  conv_lhs => rw [← (Module.Free.chooseBasis ℤ A.X).sum_repr μ, map_sum]
  rw [size, Finset.mul_sum]
  refine norm_sum_le_of_le _ fun i _ => ?_
  rw [map_zsmul]
  refine (norm_zsmul_le _ _).trans ?_
  rw [mul_comm, Int.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC i) (abs_nonneg _)

theorem exists_norm_le_mul_size {E : Type*} [SeminormedAddCommGroup E] (f : A.X →+ E) :
    ∃ C, 0 ≤ C ∧ ∀ μ, ‖f μ‖ ≤ C * A.size μ :=
  ⟨∑ i, ‖f (Module.Free.chooseBasis ℤ A.X i)‖, Finset.sum_nonneg fun _ _ => norm_nonneg _,
    A.norm_le_mul_size f fun i => Finset.single_le_sum
      (f := fun i => ‖f (Module.Free.chooseBasis ℤ A.X i)‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i)⟩

theorem norm_apply_le_size (l : A.X →+ ℂ) (μ : A.X) : ‖l μ‖ ≤ ‖l‖ * A.size μ :=
  A.norm_le_mul_size l (fun i => norm_le_pi_norm (A.coord l) i) μ

theorem be_sq_le (x y : A.X) : A.be x y ^ 2 ≤ A.be x x * A.be y y :=
  A.be.apply_sq_le_of_symm A.be_self_nonneg ⟨A.be_symm⟩ x y

theorem exists_sq_le_be (n : A.X →ₗ[ℤ] ℤ) : ∃ C : ℤ, 0 ≤ C ∧ ∀ μ, n μ ^ 2 ≤ C * A.be μ μ := by
  have hinj : Function.Injective A.be := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra h
    have := A.be_pos x h
    simp [hx] at this
  have h0 : Module.finrank ℤ ((A.X →ₗ[ℤ] ℤ) ⧸ LinearMap.range A.be) = 0 := by
    have h1 := (LinearMap.range A.be).finrank_quotient_add_finrank
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_linearMap, Module.finrank_self, mul_one] at h1
    omega
  obtain ⟨a, ha, h⟩ := Module.finrank_eq_zero_iff.1 h0 (Submodule.Quotient.mk n)
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h
  obtain ⟨y, hy⟩ := h
  refine ⟨A.be y y, A.be_self_nonneg y, fun μ => ?_⟩
  have h2 := A.be_sq_le y μ
  rw [hy] at h2 ⊢
  have h3 : 1 ≤ a ^ 2 := by have := sq_pos_of_ne_zero ha; omega
  have h4 : ((a • n) μ) ^ 2 = a ^ 2 * n μ ^ 2 := by simp [mul_pow]
  nlinarith [sq_nonneg (n μ)]

theorem exists_size_sq_le : ∃ C : ℝ, 0 < C ∧ ∀ μ, A.size μ ^ 2 ≤ C * A.be μ μ := by
  choose c hc0 hc using fun i => A.exists_sq_le_be ((Module.Free.chooseBasis ℤ A.X).coord i)
  have h0 : 0 ≤ (Fintype.card (Module.Free.ChooseBasisIndex ℤ A.X) : ℝ) * ∑ i, (c i : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => by exact_mod_cast hc0 i)
  refine ⟨(Fintype.card (Module.Free.ChooseBasisIndex ℤ A.X) : ℝ) * ∑ i, (c i : ℝ) + 1, by linarith, fun μ => ?_⟩
  have hb : (0 : ℝ) ≤ A.be μ μ := by exact_mod_cast A.be_self_nonneg μ
  refine sq_sum_le_card_mul_sum_sq.trans ?_
  rw [add_mul, mul_assoc, Finset.sum_mul, Finset.card_univ]
  refine le_add_of_le_of_nonneg (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (Nat.cast_nonneg _))
    (by linarith)
  rw [sq_abs]
  exact_mod_cast hc i μ

theorem summable_exp_neg_be {δ : ℝ} (hδ : 0 < δ) (D : ℝ) :
    Summable fun μ => Real.exp (-(δ * A.be μ μ) + D * A.size μ) := by
  obtain ⟨C, hC, h⟩ := A.exists_size_sq_le
  refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun μ => ?_)
    (A.summable_exp_neg_size.mul_left (Real.exp (C * (D + 1) ^ 2 / (4 * δ))))
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : (D + 1) * A.size μ - δ * A.be μ μ ≤ C * (D + 1) ^ 2 / (4 * δ) := by
    rw [le_div_iff₀ (by positivity), ← mul_le_mul_iff_right₀ hC]
    nlinarith [sq_nonneg (C * (D + 1) - 2 * δ * A.size μ), mul_le_mul_of_nonneg_left (h μ) (sq_nonneg (2 * δ))]
  linarith

theorem exists_norm_H_le : ∃ C, 0 ≤ C ∧ ∀ z w, ‖A.H z w‖ ≤ C * ‖z‖ * ‖w‖ := by
  refine ⟨∑ i, ∑ k, ‖A.Hm i k‖, by positivity, fun z w => ?_⟩
  simp only [H, hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  refine norm_sum_le_of_le _ fun i _ => norm_sum_le_of_le _ fun k _ => ?_
  simp only [norm_mul, Pi.star_apply, norm_star]
  have h1 := norm_le_pi_norm z i
  have h2 := norm_le_pi_norm w k
  calc ‖z i‖ * (‖A.Hm i k‖ * ‖w k‖) ≤ ‖z‖ * (‖A.Hm i k‖ * ‖w‖) := by gcongr
    _ = _ := by ring

theorem continuous_H : Continuous fun p : (Fin A.gB → ℂ) × (Fin A.gB → ℂ) => A.H p.1 p.2 := by
  simp only [H, hermForm, dotProduct, Matrix.mulVec]
  fun_prop

theorem H_re_symm (z w : Fin A.gB → ℂ) : (A.H z w).re = (A.H w z).re := by
  rw [← A.H_conj z w, Complex.conj_re]

theorem H_add_self_re (z w : Fin A.gB → ℂ) :
    (A.H (z + w) (z + w)).re = (A.H z z).re + 2 * (A.H z w).re + (A.H w w).re := by
  simp only [H_add_left, H_add_right, Complex.add_re, A.H_re_symm w z]; ring

theorem psi_sq (μ : A.X) : (A.psi μ : ℂ) ^ 2 = eTwoPi (A.T μ μ) := by
  have h := A.psi_add μ (-μ)
  rw [add_neg_cancel, psi_zero, A.psi_neg, map_neg, Units.val_one] at h
  have h2 := e_add (A.T μ μ) (-A.T μ μ)
  rw [add_neg_cancel, e_zero] at h2
  exact mul_right_cancel₀ (e_ne_zero (-A.T μ μ)) (by rw [← h2, h]; ring)

theorem norm_psi (μ : A.X) : ‖(A.psi μ : ℂ)‖ = Real.exp (-(Real.pi * (A.T μ μ).im)) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.exp_pos _).le, ← norm_pow, psi_sq, norm_e, sq, ← Real.exp_add]
  congr 1; ring

theorem norm_ah (l : A.abelian₂) (z : Fin A.gB → ℂ) :
    ‖A.ah l z‖ = Real.exp (Real.pi * (A.H z l).re + Real.pi / 2 * (A.H l l).re) := by
  rw [ah, norm_mul, A.chi_norm, one_mul, Complex.norm_exp]
  congr 1
  rw [show (Real.pi / 2 : ℂ) = ((Real.pi / 2 : ℝ) : ℂ) by simp, Complex.add_re, Complex.re_ofReal_mul,
    Complex.re_ofReal_mul]

theorem exists_norm_theta_le {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ} (h : th ∈ A.Theta j α) :
    ∃ M, 0 ≤ M ∧ ∀ z, ‖th z‖ ≤
      M * Real.exp (j * (Real.pi / 2 * (A.H z z).re) + Real.pi * (A.H (A.ct α) z).re) := by
  set g : (Fin A.gB → ℂ) → ℝ := fun z => j * (Real.pi / 2 * (A.H z z).re) + Real.pi * (A.H (A.ct α) z).re with hg
  have c1 : Continuous fun z => A.H z z := A.continuous_H.comp (continuous_id.prodMk continuous_id)
  have c2 : Continuous fun z => A.H (A.ct α) z := A.continuous_H.comp (continuous_const.prodMk continuous_id)
  have c3 := h.1.continuous
  have hK := IsZLattice.isCompact_range_of_periodic A.abelian₂ (fun z => ‖th z‖ * Real.exp (-g z))
    (by rw [hg]; fun_prop) fun z l hl => by
      have h2 := h.2 ⟨l, hl⟩ z
      simp only at h2
      rw [h2, norm_mul, norm_mul, norm_pow, norm_ah, Complex.norm_exp, ← Real.exp_nat_mul, ← Real.exp_add,
        mul_comm _ ‖th z‖, mul_assoc, ← Real.exp_add]
      congr 2
      simp only [hg, H_add_self_re, A.H_add_right (A.ct α), Complex.add_re, Complex.re_ofReal_mul]
      ring
  obtain ⟨M, hM⟩ := hK.bddAbove
  refine ⟨M, le_trans (by positivity) (hM ⟨0, rfl⟩), fun z => ?_⟩
  have : ‖th z‖ * Real.exp (-g z) ≤ M := hM ⟨z, rfl⟩
  rwa [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)] at this

def IsConvLine (T₀ : ℝ) : Prop :=
  ∀ μ : A.X, (A.H (A.ct μ) (A.ct μ)).re / 2 - (A.T μ μ).im ≤ T₀ * A.be μ μ

variable {A} in

theorem IsConvLine.mono {T₀ T₁ : ℝ} (h : A.IsConvLine T₀) (hT : T₀ ≤ T₁) : A.IsConvLine T₁ := fun μ =>
  (h μ).trans (mul_le_mul_of_nonneg_right hT (by exact_mod_cast A.be_self_nonneg μ))

theorem exists_isConvLine : ∃ T₀, A.IsConvLine T₀ := by
  obtain ⟨C, hC, h⟩ := A.exists_size_sq_le
  obtain ⟨CH, hCH, hH⟩ := A.exists_norm_H_le
  obtain ⟨Cc, hCc, hc⟩ := A.exists_norm_le_mul_size A.ct
  obtain ⟨CT, hCT, hT⟩ := A.exists_norm_le_mul_size A.T
  refine ⟨(CH * Cc ^ 2 / 2 + CT) * C, fun μ => ?_⟩
  have hs := A.size_nonneg μ
  have h1 : (A.H (A.ct μ) (A.ct μ)).re ≤ CH * Cc ^ 2 * A.size μ ^ 2 :=
    calc _ ≤ CH * ‖A.ct μ‖ * ‖A.ct μ‖ := (Complex.re_le_norm _).trans (hH _ _)
      _ ≤ CH * (Cc * A.size μ) * (Cc * A.size μ) := by gcongr <;> exact hc μ
      _ = _ := by ring
  have h2 : -(A.T μ μ).im ≤ CT * A.size μ ^ 2 :=
    calc _ ≤ ‖A.T μ‖ * A.size μ :=
          (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (A.norm_apply_le_size _ μ))
      _ ≤ CT * A.size μ * A.size μ := by gcongr; exact hT μ
      _ = _ := by ring
  have h3 : (CH * Cc ^ 2 / 2 + CT) * A.size μ ^ 2 ≤ (CH * Cc ^ 2 / 2 + CT) * (C * A.be μ μ) :=
    mul_le_mul_of_nonneg_left (h μ) (by positivity)
  linarith

theorem tate_isConvLine_iff (τ₀ : ℂ) (T₀ : ℝ) : (tate τ₀).IsConvLine T₀ ↔ -τ₀.im / 2 ≤ T₀ := by
  have key : ∀ μ : ℤ, (((tate τ₀).H ((tate τ₀).ct μ) ((tate τ₀).ct μ)).re / 2 - ((tate τ₀).T μ μ).im ≤
      T₀ * (tate τ₀).be μ μ) ↔ -(τ₀.im * μ * μ) ≤ T₀ * (2 * μ * μ) := fun μ => by
    change (hermForm (0 : Matrix (Fin 0) (Fin 0) ℂ) 0 0).re / 2 - (TInt τ₀ μ μ).im ≤ T₀ * (beInt μ μ : ℤ) ↔ _
    simp [hermForm]
  constructor
  · intro h
    have := (key 1).1 (h (1 : ℤ))
    simp only [Int.cast_one, mul_one] at this
    linarith
  · intro h μ
    refine (key μ).2 ?_
    nlinarith [mul_self_nonneg ((show ℤ from μ) : ℝ)]

section Conv

variable {A} {T₀ : ℝ} (hT : A.IsConvLine T₀) {j : ℕ} {α : A.X} {th : (Fin A.gB → ℂ) → ℂ}
include hT

theorem exists_norm_term_le (hj : j ≠ 0) (h : th ∈ A.Theta j α) {T₁ : ℝ} (h₁ : T₀ ≤ T₁) (R : ℝ) :
    ∃ K D : ℝ, ∀ μ (w : ℂ) (v : A.V), T₁ ≤ w.im → |w.im| ≤ R → ‖v‖ ≤ R →
      ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖ ≤
        K * Real.exp (-(Real.pi * (T₁ - T₀) * A.be μ μ) + D * A.size μ) := by
  obtain ⟨M, hM, hth⟩ := A.exists_norm_theta_le h
  obtain ⟨CH, hCH, hH⟩ := A.exists_norm_H_le
  obtain ⟨Cc, hCc, hc⟩ := A.exists_norm_le_mul_size A.ct
  obtain ⟨Cb, hCb, hb⟩ := A.exists_norm_le_mul_size (A.be α).toAddMonoidHom
  refine ⟨M * Real.exp (Real.pi * (2 * (R * A.size α) + j * (CH * R * R) / 2 + CH * ‖A.ct α‖ * R)),
    Real.pi * (2 * ‖A.T α‖ + 2 * (j * R) + j * (CH * R * Cc) + CH * ‖A.ct α‖ * Cc + 2 * (R * Cb)),
    fun μ w v hw hwR hv => ?_⟩
  obtain ⟨l, z⟩ := v
  have hl : ‖l‖ ≤ R := (norm_fst_le (l, z)).trans hv
  have hz : ‖z‖ ≤ R := (norm_snd_le (l, z)).trans hv
  have hR : 0 ≤ R := (norm_nonneg _).trans hz
  have hs := A.size_nonneg μ
  have hsα := A.size_nonneg α
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  have hB : (0 : ℝ) ≤ A.be μ μ := by exact_mod_cast A.be_self_nonneg μ
  have im_le : ∀ (f : A.X →+ ℂ) (x : A.X), -(f x).im ≤ ‖f‖ * A.size x := fun f x =>
    (neg_le_abs _).trans ((Complex.abs_im_le_norm _).trans (A.norm_apply_le_size f x))
  have re_le : ∀ a b, (A.H a b).re ≤ CH * ‖a‖ * ‖b‖ := fun a b => (Complex.re_le_norm _).trans (hH a b)
  have e1 : -(A.T μ α).im ≤ ‖A.T α‖ * A.size μ := by rw [A.T_symm]; exact im_le _ _
  have e2 : -(l α).im ≤ R * A.size α := (im_le l α).trans (by gcongr)
  have e3 : j * -(l μ).im ≤ j * (R * A.size μ) :=
    mul_le_mul_of_nonneg_left ((im_le l μ).trans (by gcongr)) hj0
  have e4 : j * (A.H z z).re ≤ j * (CH * R * R) :=
    mul_le_mul_of_nonneg_left ((re_le z z).trans (by gcongr)) hj0
  have e5 : j * (A.H z (A.ct μ)).re ≤ j * (CH * R * (Cc * A.size μ)) :=
    mul_le_mul_of_nonneg_left ((re_le _ _).trans (by gcongr; exact hc μ)) hj0
  have e6 : (A.H (A.ct α) z).re ≤ CH * ‖A.ct α‖ * R := (re_le _ _).trans (by gcongr)
  have e7 : (A.H (A.ct α) (A.ct μ)).re ≤ CH * ‖A.ct α‖ * (Cc * A.size μ) :=
    (re_le _ _).trans (by gcongr; exact hc μ)
  have e8 : -(w.im * A.be μ α) ≤ R * (Cb * A.size μ) := by
    refine (neg_le_abs _).trans ?_
    rw [abs_mul, A.be_symm]
    have := hb μ
    rw [Int.norm_eq_abs] at this
    exact mul_le_mul hwR this (abs_nonneg _) hR
  have e9 : j * ((A.H (A.ct μ) (A.ct μ)).re / 2 - (A.T μ μ).im - w.im * A.be μ μ) ≤ -((T₁ - T₀) * A.be μ μ) := by
    have a1 : (A.H (A.ct μ) (A.ct μ)).re / 2 - (A.T μ μ).im - w.im * A.be μ μ ≤ -((T₁ - T₀) * A.be μ μ) := by
      have := hT μ
      have := mul_le_mul_of_nonneg_right hw hB
      linarith
    have a2 : 0 ≤ (T₁ - T₀) * A.be μ μ := mul_nonneg (sub_nonneg.2 h₁) hB
    nlinarith [mul_le_mul_of_nonneg_left a1 hj0]
  have hex : (A.exponent j α μ : ℝ) = j * A.be μ μ / 2 + A.be μ α := by
    have : (2 : ℝ) * A.exponent j α μ = j * A.be μ μ + 2 * A.be μ α := by exact_mod_cast A.two_mul_exponent j α μ
    linarith
  have i1 : (l (α + j • μ)).im = (l α).im + j * (l μ).im := by simp
  have i2 : (w * A.exponent j α μ).im = w.im * (j * A.be μ μ / 2 + A.be μ α) := by simp [hex]
  rw [term, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_psi, norm_e, norm_e, norm_e, i1, i2,
    ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, mul_right_comm, ← Real.exp_add]
  refine (mul_le_mul_of_nonneg_left (hth _) (Real.exp_pos _).le).trans ?_
  rw [mul_left_comm, ← Real.exp_add, mul_assoc M, ← Real.exp_add]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM
  rw [H_add_self_re, H_add_right, Complex.add_re]
  have key := mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add e1 e1)
    (add_le_add e2 e2)) (add_le_add (add_le_add e3 e3) (div_le_div_of_nonneg_right e4 zero_le_two)))
    (add_le_add (add_le_add e5 e6) (add_le_add e7 (add_le_add e8 e8)))) e9) Real.pi_pos.le
  linarith

theorem exists_summable_bound (hj : j ≠ 0) (h : th ∈ A.Theta j α) {T₁ : ℝ} (h₁ : T₀ < T₁) (T₂ R : ℝ) :
    ∃ u : A.X → ℝ, Summable u ∧ ∀ μ (w : ℂ) (v : A.V), T₁ ≤ w.im → w.im ≤ T₂ → ‖v‖ ≤ R →
      ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖ ≤ u μ := by
  obtain ⟨K, D, hK⟩ := exists_norm_term_le hT hj h h₁.le (max R (max |T₁| |T₂|))
  refine ⟨_, (A.summable_exp_neg_be (mul_pos Real.pi_pos (sub_pos.2 h₁)) D).mul_left K, fun μ w v a b c =>
    hK μ w v a ((abs_le_max_abs_abs a b).trans (le_max_right _ _)) (c.trans (le_max_left _ _))⟩

theorem locally_normal (hj : j ≠ 0) (h : th ∈ A.Theta j α) (p : ℂ × A.V) (hp : T₀ < p.1.im) :
    ∃ t ∈ 𝓝 p, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ q ∈ t,
      ‖A.term j α th μ q.2 * eTwoPi (q.1 * A.exponent j α μ)‖ ≤ u μ := by
  obtain ⟨u, hu, hb⟩ := exists_summable_bound hT hj h (T₁ := (T₀ + p.1.im) / 2) (by linarith) (p.1.im + 1) (‖p.2‖ + 1)
  have c1 : Continuous fun q : ℂ × A.V => q.1.im := by fun_prop
  have c2 : Continuous fun q : ℂ × A.V => ‖q.2‖ := by fun_prop
  refine ⟨{q | (T₀ + p.1.im) / 2 ≤ q.1.im} ∩ ({q | q.1.im ≤ p.1.im + 1} ∩ {q | ‖q.2‖ ≤ ‖p.2‖ + 1}), ?_, u, hu,
    fun μ q hq => hb μ q.1 q.2 hq.1 hq.2.1 hq.2.2⟩
  exact inter_mem (c1.continuousAt.eventually (eventually_ge_nhds (by simp only; linarith)))
    (inter_mem (c1.continuousAt.eventually (eventually_le_nhds (by simp)))
      (c2.continuousAt.eventually (eventually_le_nhds (by simp))))

theorem summable_norm_term (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v : A.V) :
    Summable fun μ => ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖ := by
  obtain ⟨t, ht, u, hu, hb⟩ := locally_normal hT hj h (w, v) hw
  exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun μ => hb μ (w, v) (mem_of_mem_nhds ht)) hu

theorem summable_term (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v : A.V) :
    Summable fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ) :=
  (summable_norm_term hT hj h hw v).of_norm

theorem hasSum_term (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v : A.V) :
    HasSum (fun μ => A.term j α th μ v * eTwoPi (w * A.exponent j α μ)) (A.Sum j α th w v) :=
  (summable_term hT hj h hw v).hasSum

theorem hasSumLocallyUniformlyOn_term (hj : j ≠ 0) (h : th ∈ A.Theta j α) :
    HasSumLocallyUniformlyOn (fun μ (p : ℂ × A.V) => A.term j α th μ p.2 * eTwoPi (p.1 * A.exponent j α μ))
      (fun p => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} :=
  SCV.hasSumLocallyUniformlyOn_of_locally_normal (locally_normal hT hj h)

omit hT in

theorem isOpen_above (T : ℝ) : IsOpen {p : ℂ × A.V | T < p.1.im} := isOpen_lt continuous_const (by fun_prop)

omit hT in

theorem differentiable_term_mul (h : Differentiable ℂ th) (μ : A.X) :
    Differentiable ℂ fun p : ℂ × A.V => A.term j α th μ p.2 * eTwoPi (p.1 * A.exponent j α μ) := by
  have := A.differentiable_term j α h μ
  unfold eTwoPi
  fun_prop

theorem differentiableOn_Sum (hj : j ≠ 0) (h : th ∈ A.Theta j α) :
    DifferentiableOn ℂ (fun p : ℂ × A.V => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} :=
  SCV.differentiableOn_of_hasSumLocallyUniformlyOn (isOpen_above T₀) (hasSumLocallyUniformlyOn_term hT hj h)
    fun μ => (differentiable_term_mul h.1 μ).differentiableOn

theorem differentiable_Sum (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) :
    Differentiable ℂ (A.Sum j α th w) := fun v =>
  ((differentiableOn_Sum hT hj h).differentiableAt ((isOpen_above T₀).mem_nhds (x := (w, v)) hw)).comp v
    (f := fun v => (w, v)) (by fun_prop)

theorem locally_normal_right (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v : A.V) :
    ∃ t ∈ 𝓝 v, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ v' ∈ t,
      ‖A.term j α th μ v' * eTwoPi (w * A.exponent j α μ)‖ ≤ u μ := by
  obtain ⟨t, ht, u, hu, hb⟩ := locally_normal hT hj h (w, v) hw
  exact ⟨_, (Continuous.prodMk_right w).continuousAt ht, u, hu, fun μ v' hv' => hb μ (w, v') hv'⟩

theorem hasSum_fderiv_term (hj : j ≠ 0) (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v v₀ : A.V) :
    HasSum (fun μ => fderiv ℂ (A.term j α th μ) v v₀ * eTwoPi (w * A.exponent j α μ))
      (fderiv ℂ (A.Sum j α th w) v v₀) := by
  have h1 := SCV.hasSum_fderiv_of_locally_normal isOpen_univ
    (F := fun μ v => A.term j α th μ v * eTwoPi (w * A.exponent j α μ))
    (fun μ => ((A.differentiable_term j α h.1 μ).mul_const _).differentiableOn)
    (fun v _ => locally_normal_right hT hj h hw v) (Set.mem_univ v)
  refine ((ContinuousLinearMap.apply ℂ ℂ v₀).hasSum h1).congr_fun fun μ => ?_
  rw [fderiv_mul_const (A.differentiable_term j α h.1 μ v)]
  simp [mul_comm]

variable [NeZero j]

omit hT in

theorem hasSum_level {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] {f : A.X → E} {a : E} (hf : HasSum f a) :
    HasSum (fun n : ℤ => ∑ μ ∈ A.level j α n, f μ) a := by
  convert hf.tsum_fiberwise (A.exponent j α) using 2 with n
  have : A.exponent j α ⁻¹' {n} = (A.level j α n : Set A.X) := by ext; simp
  rw [this, Finset.tsum_subtype']

omit hT in

theorem coeff_FSum_mul (w : ℂ) (v : A.V) (n : ℤ) : (A.FSum j α th v).coeff n * eTwoPi w ^ n =
    ∑ μ ∈ A.level j α n, A.term j α th μ v * eTwoPi (w * A.exponent j α μ) := by
  rw [coeff_FSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [e_mul_intCast, A.mem_level.1 hμ]

omit hT in

theorem differentiable_coeff_FSum (h : Differentiable ℂ th) (n : ℤ) :
    Differentiable ℂ fun v => (A.FSum j α th v).coeff n :=
  Differentiable.fun_sum fun μ _ => A.differentiable_term j α h μ

omit hT in

theorem fderiv_coeff_FSum (h : Differentiable ℂ th) (n : ℤ) (v v₀ : A.V) :
    fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v v₀ = ∑ μ ∈ A.level j α n, fderiv ℂ (A.term j α th μ) v v₀ := by
  simp only [coeff_FSum]
  rw [fderiv_fun_sum fun μ _ => A.differentiable_term j α h μ v, sum_apply]

omit hT in

theorem fderiv_coeff_FSum_eq_zero {n : ℤ} (hn : n < -A.be α α) (v : A.V) :
    fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v = 0 := by
  simp only [A.coeff_FSum_eq_zero j α th _ hn, fderiv_fun_const, Pi.zero_apply]

theorem hasSum_coeff_FSum (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v : A.V) :
    HasSum (fun n : ℤ => (A.FSum j α th v).coeff n * eTwoPi w ^ n) (A.Sum j α th w v) := by
  simp only [coeff_FSum_mul]
  exact hasSum_level (hasSum_term hT (NeZero.ne j) h hw v)

theorem hasSum_fderiv_coeff_FSum (h : th ∈ A.Theta j α) {w : ℂ} (hw : T₀ < w.im) (v v₀ : A.V) :
    HasSum (fun n : ℤ => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v v₀ * eTwoPi w ^ n)
      (fderiv ℂ (A.Sum j α th w) v v₀) := by
  refine (hasSum_level (j := j) (α := α) (hasSum_fderiv_term hT (NeZero.ne j) h hw v v₀)).congr_fun fun n => ?_
  rw [fderiv_coeff_FSum h.1, Finset.sum_mul]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  rw [e_mul_intCast, A.mem_level.1 hμ]

end Conv

theorem exists_convergence : ∃ T₀ : ℝ, ∀ (j : ℕ) [NeZero j] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ), th ∈ A.Theta j α →
    (∀ p : ℂ × A.V, T₀ < p.1.im → ∃ t ∈ 𝓝 p, ∃ u : A.X → ℝ, Summable u ∧ ∀ μ, ∀ q ∈ t,
      ‖A.term j α th μ q.2 * eTwoPi (q.1 * A.exponent j α μ)‖ ≤ u μ) ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v, Summable fun μ => ‖A.term j α th μ v * eTwoPi (w * A.exponent j α μ)‖) ∧
    HasSumLocallyUniformlyOn (fun μ (p : ℂ × A.V) => A.term j α th μ p.2 * eTwoPi (p.1 * A.exponent j α μ))
      (fun p => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} ∧
    DifferentiableOn ℂ (fun p : ℂ × A.V => A.Sum j α th p.1 p.2) {p | T₀ < p.1.im} ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v,
      HasSum (fun n : ℤ => (A.FSum j α th v).coeff n * eTwoPi w ^ n) (A.Sum j α th w v)) ∧
    (∀ n : ℤ, Differentiable ℂ fun v => (A.FSum j α th v).coeff n) ∧
    (∀ w : ℂ, T₀ < w.im → ∀ v v₀,
      HasSum (fun n : ℤ => fderiv ℂ (fun v => (A.FSum j α th v).coeff n) v v₀ * eTwoPi w ^ n)
        (fderiv ℂ (A.Sum j α th w) v v₀)) := by
  obtain ⟨T₀, hT⟩ := A.exists_isConvLine
  exact ⟨T₀, fun j _ α th h => ⟨locally_normal hT (NeZero.ne j) h,
    fun _ hw => summable_norm_term hT (NeZero.ne j) h hw, hasSumLocallyUniformlyOn_term hT (NeZero.ne j) h,
    differentiableOn_Sum hT (NeZero.ne j) h, fun _ hw => hasSum_coeff_FSum hT h hw,
    differentiable_coeff_FSum h.1, fun _ hw => hasSum_fderiv_coeff_FSum hT h hw⟩⟩

end AnArc

end GlobalTheory
