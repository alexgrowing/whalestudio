import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ColTorusD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.L2NormFundamentalDomain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ContinuousPointNormSqQuotient

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem ct_28 (P : Par X DF) {c : ℕ} (hc : c ≤ DF) : 28 * (c : ℝ) ≤ t0 (E := E) P.q P.R0 := by
  have h5 := P.C5
  have hq : (1 : ℝ) ≤ P.q := by exact_mod_cast P.hq
  have hDF : (1 : ℝ) ≤ DF := by exact_mod_cast P.hDF
  have hlog : 0 ≤ Real.log ((P.q : ℝ) * DF) := Real.log_nonneg (by nlinarith)
  have hcDF : (c : ℝ) ≤ DF := by exact_mod_cast hc
  have hd : (0:ℝ) ≤ dstar (E := E) P.m := Nat.cast_nonneg _
  have hm : 0 ≤ 4 * (DF : ℝ) * Real.log ((P.q : ℝ) * DF) := mul_nonneg (by linarith) hlog
  nlinarith

theorem ct_tail (hI : IsSplit P I) (hP : Ext.PackingCount) (hGT : Ext.GaussianTailBound)
    {β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ} (hβ : β ∈ (Col.YB hI hP P.q).Sec P.q)
    {B : ℝ} (hB0 : 0 ≤ B) (hBβ : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤ B ^ 2)
    (c : ℕ) (hc : c ≤ DF) (x0 u : Vsp X.dim) (hu : u = Col.uc (IR I) x0)
    (hc6 : ∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ u uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2)
    (r : ℝ) (hr0 : 0 ≤ r) (hr : r * (2 * Real.pi * ‖u‖ + 5 * Real.sqrt (P.q * (c + 1))) ≤ c)
    (v : Vsp X.dim) (hv : ‖v‖ ≤ r) :
    ‖(ctC I P.q (ctA x0 P.q))⁻¹ * (Complex.exp (P.q * Real.pi * Hf v (ctA x0 P.q) -
        P.q * Real.pi * Hf (ctA x0 P.q) (ctA x0 P.q) / 2) *
        (Col.sP X I P.q β (v - ctA x0 P.q) - Col.F0 I P.q β (v - ctA x0 P.q)))‖ ≤
      B * Real.exp (1.07 * c) * (2 * 3 ^ Col.dK (IR I) * Real.exp (-(1.33 * t0 (E := E) P.q P.R0))) := by
  set a := ctA x0 P.q with ha
  set q := P.q with hqdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast P.hq
  have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast (by have := P.hq; omega : q ≠ 0)
  set K := (ctC I q a)⁻¹ * Complex.exp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) with hK

  have hsum := Col.summable_Tc hI hP hGT hB0 hBβ (v - a)
  have hsplit := hsum.sum_add_tsum_compl (s := ({0} : Finset (Col.Qc X I)))
  rw [Finset.sum_singleton, translate_zero_zeroModeLift hI hP q hβ] at hsplit
  have hR : Col.sP X I q β (v - a) - Col.F0 I q β (v - a) =
      ∑' x : ((({0} : Finset (Col.Qc X I)) : Set (Col.Qc X I))ᶜ : Set _), Col.Tc X I q β x (v - a) := by
    rw [Col.sP, ← hsplit]; ring
  rw [show (ctC I q a)⁻¹ * (Complex.exp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2) *
      (Col.sP X I q β (v - a) - Col.F0 I q β (v - a))) = K * (Col.sP X I q β (v - a) -
        Col.F0 I q β (v - a)) by rw [hK]; ring, hR, ← tsum_mul_left]

  obtain ⟨hgs, hgb⟩ := Col.tailQ hI hP hGT 1.33 (by norm_num) (Col.cond_tail hI 1.33 (by norm_num))
  set g : ((({0} : Finset (Col.Qc X I)) : Set (Col.Qc X I))ᶜ : Set _) → ℝ :=
    fun x => Real.exp (-(1.33 * q) * ‖Col.uQ X I x‖ ^ 2) with hg
  have hgs' : Summable g := hgs
  have hpt : ∀ x : ((({0} : Finset (Col.Qc X I)) : Set (Col.Qc X I))ᶜ : Set _),
      ‖K * Col.Tc X I q β x (v - a)‖ ≤ B * Real.exp (1.07 * c) * g x := by
    intro x
    have hx0 : (x : Col.Qc X I) ≠ 0 := by
      have := x.2; simpa using this
    have hT := Col.norm_Tc_le hI hB0 hBβ (x : Col.Qc X I) (v - a)
    set ua := Col.uc (IR I) a with hua
    set y := Col.uQ X I (x : Col.Qc X I) with hy
    set w := Col.uc (IR I) v with hw
    have hKn : ‖K‖ = Real.exp (q * Real.pi * ‖ua‖ ^ 2) *
        Real.exp (q * Real.pi * (Hf v a).re - q * Real.pi * ‖a‖ ^ 2 / 2) := by
      rw [hK, norm_mul, norm_inv, ct_norm_C hI, Complex.norm_exp, Real.exp_neg, inv_inv]
      congr 2
      rw [Col.Hf_self a]
      simp [Complex.mul_re, Complex.sub_re]
      left; norm_cast
    have hn : ‖v - a‖ ^ 2 = ‖v‖ ^ 2 - 2 * (Hf v a).re + ‖a‖ ^ 2 := by
      rw [← Col.Hf_self_re, ← Col.Hf_self_re, ← Col.Hf_self_re, Col.Hf_sub_l, Col.Hf_sub_r,
        Col.Hf_sub_r, Col.Hf_swap v a]
      simp; ring
    have huc : Col.uc (IR I) (v - a) = w - ua := Col.uc_sub (I := I) v a
    rw [huc] at hT

    have hua' : (q : ℝ) • ua = u := by
      rw [hua, ha, ct_uc_A, smul_smul, mul_one_div_cancel hq0.ne', one_smul, hu]
    have hnua : (q : ℝ) * ‖ua‖ = ‖u‖ := by
      rw [← hua', norm_smul, Real.norm_eq_abs, abs_of_pos hq0]
    have hc6' : |2 * inner ℝ ((q : ℝ) • ua) y| ≤ M1 (E := E) P.m * ‖y‖ ^ 2 := by
      rw [hua']
      refine hc6 _ (Quotient.out (x : Col.Qc X I) : X.L).2 y ?_
      rw [hy, Col.uQ_out]; exact Col.isU_uc _
    have hwr : ‖w‖ ≤ r := (Col.norm_uc_le hI.iso v).trans hv
    have hv1 := ct_expo_vec w ua y hq0 hwr hc6'
    have hsep := Col.uQ_sep hI hx0
    have h28 := ct_28 P hc
    have ht : 28 * (c : ℝ) ≤ q * ‖y‖ ^ 2 := by
      have : t0 (E := E) P.q P.R0 = q * b0 (E := E) P.q P.R0 := rfl
      nlinarith
    have hv2 := ct_expo_num q c P.hq (U := ‖u‖) (y := ‖y‖) (norm_nonneg _) (norm_nonneg _) P.C3 hr0 hr ht
    have hvv : q * Real.pi * ‖v‖ ^ 2 / 2 ≤ q * Real.pi * r ^ 2 / 2 := by
      have : ‖v‖ ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ q * Real.pi)
      linarith
    have hsub : w - (ua + y) = w - ua - y := by abel
    rw [hsub] at hv1
    have hexp : q * Real.pi * ‖ua‖ ^ 2 + (q * Real.pi * (Hf v a).re - q * Real.pi * ‖a‖ ^ 2 / 2) +
        (q * Real.pi * ‖v - a‖ ^ 2 / 2 + -(q * Real.pi) * ‖w - ua - y‖ ^ 2) ≤
        1.07 * c + -(1.33 * q) * ‖y‖ ^ 2 := by
      rw [hn]
      have e1 : 2 * Real.pi * r * (q * ‖ua‖ + q * ‖y‖) = 2 * Real.pi * r * (‖u‖ + q * ‖y‖) := by
        rw [hnua]
      nlinarith
    calc ‖K * Col.Tc X I q β (x : Col.Qc X I) (v - a)‖
        = ‖K‖ * ‖Col.Tc X I q β (x : Col.Qc X I) (v - a)‖ := norm_mul _ _
      _ ≤ ‖K‖ * (B * Real.exp (q * Real.pi * ‖v - a‖ ^ 2 / 2) *
            Real.exp (-(q * Real.pi) * ‖w - ua - y‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left hT (norm_nonneg _)
      _ = B * Real.exp (q * Real.pi * ‖ua‖ ^ 2 + (q * Real.pi * (Hf v a).re - q * Real.pi * ‖a‖ ^ 2 / 2) +
            (q * Real.pi * ‖v - a‖ ^ 2 / 2 + -(q * Real.pi) * ‖w - ua - y‖ ^ 2)) := by
          rw [hKn, Real.exp_add, Real.exp_add, Real.exp_add]; ring
      _ ≤ B * Real.exp (1.07 * c + -(1.33 * q) * ‖y‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hB0
      _ = B * Real.exp (1.07 * c) * g x := by rw [hg, Real.exp_add]; ring
  have hns : Summable (fun x : ((({0} : Finset (Col.Qc X I)) : Set (Col.Qc X I))ᶜ : Set _) =>
      ‖K * Col.Tc X I q β x (v - a)‖) :=
    Summable.of_nonneg_of_le (fun x => norm_nonneg _) hpt (hgs'.mul_left _)
  refine (norm_tsum_le_tsum_norm hns).trans ?_
  refine (hns.tsum_le_tsum hpt (hgs'.mul_left _)).trans ?_
  rw [tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have : ∑' x, g x ≤ 2 * 3 ^ Col.dK (IR I) * Real.exp (-(1.33 * q * b0 (E := E) P.q P.R0)) := hgb
  refine this.trans (le_of_eq ?_)
  congr 2
  simp only [t0]; ring

end

end ReciprocityTheory.ChartRestriction.G.I2

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField MeasureTheory

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {X : PT E} {DF : ℕ} {P : Par X DF}
  {I : Submodule ℤ (Vsp X.dim)}

theorem ct_dK_le (hI : IsSplit P I) : Col.dK (IR I) ≤ dstar (E := E) P.m := by
  obtain ⟨ρ, hρ, hr⟩ := hI.rank
  have h1 : Col.dK (IR I) = 2 * PT.f E * ρ := hr
  rw [h1, dstar]
  exact Nat.mul_le_mul_left _ hρ

set_option maxHeartbeats 1000000 in

theorem ct_deriv (hP : Ext.PackingCount) (hGT : Ext.GaussianTailBound) (hI : IsSplit P I)
    (c : ℕ) (hc : c ≤ DF) (σ : E →+* ℂ) (x0 u : Vsp X.dim) (hu : u = Col.uc (IR I) x0)
    (n : ℝ) (hn : 1 ≤ n) (hun : 2 * Real.pi * ‖u‖ ≤ 1.5 * n)
    (hc6 : ∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ u uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2)
    (βt : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ) (hβtd : Differentiable ℂ βt) (hb0 : βt 0 = 1)
    (hbj : ∀ j, 1 ≤ j → j ≤ c → iteratedFDeriv ℂ j βt 0 = 0)
    {β : EuclideanSpace ℂ (Fin (Col.gB (IR I))) → ℂ} (hβ : β ∈ (Col.YB hI hP P.q).Sec P.q)
    (hββ : ctU P.q (Col.wmap (IR I) (ctA x0 P.q)) β = βt)
    (hBβ : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(P.q * Real.pi) * ‖t‖ ^ 2) ≤
      Real.sqrt (12 * (5.12 : ℝ) ^ Col.gB (IR I)) ^ 2)
    (xs : Fin c → Vsp X.dim) (hxs : ∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) :
    ‖d1 (ctS X I P.q β (ctA x0 P.q)) c xs - (-Complex.I) ^ c * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) u‖ ≤
      P.eps1 * n ^ c := by
  have hK := Col.hK_of hI
  set q := P.q with hqdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast P.hq
  have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast (by have := P.hq; omega : q ≠ 0)
  set a := ctA x0 q with ha
  set C := ctC I q a with hC
  have hC0 : C ≠ 0 := Complex.exp_ne_zero _
  set Bsq : ℝ := 12 * (5.12 : ℝ) ^ Col.gB (IR I) with hBsq
  have hBsq0 : 0 ≤ Bsq := by positivity
  set B := Real.sqrt Bsq with hBdef
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  set E0 : Vsp X.dim → ℂ := fun v => Complex.exp (q * Real.pi * Hf v a - q * Real.pi * Hf a a / 2)
    with hE0
  set gfun : Vsp X.dim → ℂ := fun v => C⁻¹ * (E0 v * Col.sP X I q β (v - a)) with hgfun
  set mainf : Vsp X.dim → ℂ := fun v =>
    Complex.exp (-(2 * Real.pi * q : ℂ) * Complex.I * Hf v (Col.uc (IR I) a)) * Col.F0 I q βt v
    with hmainf
  set tailf : Vsp X.dim → ℂ := fun v =>
    C⁻¹ * (E0 v * (Col.sP X I q β (v - a) - Col.F0 I q β (v - a))) with htailf
  have hE0d : Differentiable ℂ E0 :=
    (((Col.diff_Hf a).const_mul ((q : ℂ) * Real.pi)).sub_const _).cexp
  have hsPd : Differentiable ℂ (Col.sP X I q β) := Col.diff_sP hI hP hGT hB0 hBβ hβ.1
  have hF0d : Differentiable ℂ (Col.F0 I q β) := differentiable_zeroModeLift I q β hβ.1
  have hsh : Differentiable ℂ (fun v : Vsp X.dim => v - a) := differentiable_id.sub_const a
  have htaild : Differentiable ℂ tailf :=
    (hE0d.mul ((hsPd.comp hsh).sub (hF0d.comp hsh))).const_mul _
  have hmaind : Differentiable ℂ mainf :=
    (((Col.diff_Hf _).const_mul _).cexp).mul (differentiable_zeroModeLift I q βt hβtd)
  have hgd : Differentiable ℂ gfun := (hE0d.mul (hsPd.comp hsh)).const_mul _
  have hgsplit : gfun = mainf + tailf := by
    funext v
    have h := translate_zeroModeLift_formula hK q β a v
    rw [hββ] at h
    show C⁻¹ * (E0 v * Col.sP X I q β (v - a)) = mainf v + C⁻¹ * (E0 v * (Col.sP X I q β (v - a) -
      Col.F0 I q β (v - a)))
    have h1 : E0 v * Col.F0 I q β (v - a) =
        C * (Complex.exp (-(2 * Real.pi * q : ℂ) * Complex.I * Hf v (Col.uc (IR I) a)) *
          Col.F0 I q βt v) := by
      simp only [hE0, Col.F0]; rw [h, hC]; unfold ctC; ring
    have h2 : mainf v = C⁻¹ * (E0 v * Col.F0 I q β (v - a)) := by
      rw [h1, hmainf, ← mul_assoc, inv_mul_cancel₀ hC0, one_mul]
    rw [h2]; ring
  have hd1 : d1 (ctS X I q β a) c xs = iteratedFDeriv ℂ c gfun 0 xs := by
    have hfun : ctS X I q β a = fun w => gfun (w 0) := ct_fun q β a
    unfold d1; rw [hfun]
    exact iteratedFDeriv_single_column (contDiff_of_differentiable_fd hgd c) xs
  have hadd : iteratedFDeriv ℂ c gfun 0 xs =
      iteratedFDeriv ℂ c mainf 0 xs + iteratedFDeriv ℂ c tailf 0 xs := by
    rw [hgsplit, iteratedFDeriv_add_apply (contDiff_of_differentiable_fd hmaind c).contDiffAt
      (contDiff_of_differentiable_fd htaild c).contDiffAt]
    rfl
  have hmain := ct_main hI σ q c βt hβtd hb0 hbj (Col.uc (IR I) a) xs (fun k => (hxs k).1)
  have hua : Col.uc (IR I) a = (1 / (q : ℝ)) • u := by rw [ha, ct_uc_A, hu]
  have hprod : ∏ k, (-(2 * Real.pi * q : ℂ) * Complex.I * Hf (xs k) (Col.uc (IR I) a)) =
      (-Complex.I) ^ c * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) u := by
    have hk : ∀ k, (-(2 * Real.pi * q : ℂ) * Complex.I * Hf (xs k) (Col.uc (IR I) a)) =
        (-Complex.I) * (2 * Real.pi) * Hf (xs k) u := by
      intro k
      rw [hua, Col.Hf_rsmul_r]
      push_cast
      field_simp
    rw [Finset.prod_congr rfl (fun k _ => hk k), Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hd1, hadd, hmain, hprod, add_sub_cancel_left]

  set D := 2 * Real.pi * ‖u‖ + 5 * Real.sqrt (q * (c + 1)) with hD
  have hs0 : 0 < Real.sqrt (q * (c + 1)) := Real.sqrt_pos.mpr (by positivity)
  have hD0 : 0 < D := by positivity
  set M := B * Real.exp (1.07 * c) *
    (2 * 3 ^ Col.dK (IR I) * Real.exp (-(1.33 * t0 (E := E) P.q P.R0))) with hM
  have hcr : (c : ℝ) * (1 / D) * D ≤ c := by field_simp; rfl
  have hcau := ct_iter_cauchy tailf (fun m => contDiff_of_differentiable_fd htaild m) (1 / D) M
    (by positivity) c xs 0 (fun k => (hxs k).2.le) (fun y hy =>
      ct_tail hI hP hGT hβ hB0 hBβ c hc x0 u hu hc6 (c * (1 / D)) (by positivity) hcr y
        (by simpa using hy))
  refine hcau.trans ?_
  have hC5 : 4 * (c : ℝ) * (7 + Real.log (q * c)) ≤ t0 (E := E) P.q P.R0 := by
    have := threshold_ge_log_bound P hc
    have : (0 : ℝ) ≤ dstar (E := E) P.m := Nat.cast_nonneg _
    linarith
  have hBn := ct_B_num X.gA (Col.gB (IR I)) (Col.dK (IR I)) (dstar (E := E) P.m) hBsq0 le_rfl
    (cab_gB_le (IR I)) (ct_dK_le hI) (threshold_ge_rank_log_two P)
  have hfin := jet_product_le q c (Col.dK (IR I)) X.gA (dstar (E := E) P.m) P.hq hn (norm_nonneg u) hun
    hC5 hBn
  have heq : M / (1 / D) ^ c = D ^ c * (Real.sqrt Bsq * Real.exp (1.07 * c) *
      (2 * 3 ^ Col.dK (IR I) * Real.exp (-(1.33 * t0 (E := E) P.q P.R0)))) := by
    rw [hM, one_div, inv_pow, div_inv_eq_mul]; ring
  rw [heq]
  refine hfin.trans (le_of_eq ?_)
  simp only [Par.eps1]

theorem ct_core (hP : Ext.PackingCount) (hGT : Ext.GaussianTailBound) (hA : PropAStatement)
    (hS : GSupStatement) (hI : IsSplit P I) (c : ℕ) (hc : c ≤ DF) (σ : E →+* ℂ)
    (x0 u : Vsp X.dim) (hx0 : x0 ∈ X.L) (hu : IsU I x0 u) (n : ℝ) (hn : 1 ≤ n)
    (hun : 2 * Real.pi * ‖u‖ ≤ 1.5 * n)
    (hc6 : ∀ y ∈ X.L, ∀ uy, IsU I y uy → |2 * inner ℝ u uy| ≤ M1 (E := E) P.m * ‖uy‖ ^ 2) :
    ∃ s' ∈ X.Sec P.q 1, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      (∀ xs : Fin c → Vsp X.dim, (∀ k, InPart σ (xs k) ∧ ‖xs k‖ = 1) →
        ‖d1 s' c xs - ζ * (2 * Real.pi) ^ c * ∏ k, Hf (xs k) u‖ ≤ P.eps1 * n ^ c) ∧
      P.K6⁻¹ * Real.exp (-(2 * Real.pi * ‖u‖ ^ 2 / P.q)) * X.l2 P.q s' ≤ n ^ (2 * c) := by
  have hu' : u = Col.uc (IR I) x0 := hu.unique (Col.isU_uc x0)
  set q := P.q with hqdef
  have hq0 : (0 : ℝ) < q := by exact_mod_cast P.hq
  have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast (by have := P.hq; omega : q ≠ 0)
  set w := Col.wmap (IR I) x0 with hw
  obtain ⟨βt, hβt, hb0, hbj, hl2t, hsupt⟩ := ct_beta hA hS hI hP w c hc
  set b : EuclideanSpace ℂ (Fin (Col.gB (IR I))) := -((1 / (q : ℂ)) • w) with hb
  set β := ctU q b βt with hβdef
  have hβ : β ∈ (Col.YB hI hP q).Sec q := ctU_mem (Col.YB hI hP q) w P.hq hβt
  set a := ctA x0 q with ha
  have hwa : Col.wmap (IR I) a = (1 / (q : ℂ)) • w := by rw [ha, ctA, map_smul]
  have hββ : ctU q (Col.wmap (IR I) a) β = βt := by
    rw [hwa, hβdef, hb]; exact ctU_cancel q _ βt
  set Bsq : ℝ := 12 * (5.12 : ℝ) ^ Col.gB (IR I) with hBsq
  have hBsq0 : 0 ≤ Bsq := by positivity
  have hBβ : ∀ t, ‖β t‖ ^ 2 * Real.exp (-(q * Real.pi) * ‖t‖ ^ 2) ≤ Real.sqrt Bsq ^ 2 := by
    intro t
    rw [Real.sq_sqrt hBsq0]
    have h1 := pointNormSq_translate (Col.YB hI hP q) q b βt t
    have h2 := hsupt (t - b)
    unfold GT.ptN2 at h1 h2
    rw [← hβdef] at h1
    rw [h1]; exact h2
  have hB0 : 0 ≤ Real.sqrt Bsq := Real.sqrt_nonneg _
  have hcol := Col.colS_mem hI hP hGT hB0 hBβ hβ
  have hamem : ∀ k : Fin 1, (q : ℂ) • (fun _ : Fin 1 => a) k ∈ X.L := by
    intro k
    show (q : ℂ) • ctA x0 q ∈ X.L
    rw [ctA, smul_smul, mul_one_div_cancel hq0', one_smul]; exact hx0
  have hUmem := nA_U_mem X hcol hamem
  refine ⟨ctS X I q β a, (X.Sec q 1).smul_mem _ hUmem, (-Complex.I) ^ c, by simp, ?_, ?_⟩
  · intro xs hxs
    exact ct_deriv hP hGT hI c hc σ x0 u hu' n hn hun hc6 βt hβt.1 hb0 hbj hβ hββ hBβ xs hxs
  · have hl2 : X.l2 q (ctS X I q β a) = ‖(ctC I q a)⁻¹‖ ^ 2 * X.l2 q (Col.colS X I q β) := by
      unfold ctS
      rw [l2_smul X q, l2_U_eq_l2 hcol]
    have hCn : ‖(ctC I q a)⁻¹‖ ^ 2 = Real.exp (2 * Real.pi * ‖u‖ ^ 2 / q) := by
      rw [norm_inv, ct_norm_C hI, Real.exp_neg, inv_inv, ← Real.exp_nat_mul]
      congr 1
      have hua : Col.uc (IR I) a = (1 / (q : ℝ)) • u := by rw [ha, ct_uc_A, hu']
      rw [hua, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
      push_cast; ring
    have h4 := Col.l2_colS_le_four_mul hI hP hGT hβ hB0 hBβ
    rw [l2_ctU_eq_l2_ctY (Col.YB hI hP q) w hβt] at h4
    have hK6 := twentyfour_le_constant P
    have hK6p : 0 < P.K6 := by linarith
    have hl20 : 0 ≤ X.l2 q (Col.colS X I q β) := by
      unfold PT.l2
      rw [MeasureTheory.setAverage_eq]
      exact smul_nonneg (inv_nonneg.2 MeasureTheory.measureReal_nonneg)
        (MeasureTheory.integral_nonneg fun v => by unfold PT.ptN2; positivity)
    have hn1 : (1 : ℝ) ≤ n ^ (2 * c) := one_le_pow₀ hn
    rw [hl2, hCn, ← mul_assoc, mul_assoc P.K6⁻¹, ← Real.exp_add,
      show -(2 * Real.pi * ‖u‖ ^ 2 / q) + 2 * Real.pi * ‖u‖ ^ 2 / q = 0 by ring, Real.exp_zero,
      mul_one]
    rw [inv_mul_le_iff₀ hK6p]
    nlinarith

end

end ReciprocityTheory.ChartRestriction.G.I2
