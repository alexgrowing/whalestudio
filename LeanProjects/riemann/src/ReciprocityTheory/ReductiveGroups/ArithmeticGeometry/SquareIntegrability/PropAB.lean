import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropAA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.PropABSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.PaThContinuous
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.FourierProjections.ExpNEllMem

namespace ReciprocityTheory.ChartRestriction.G.I2

open MeasureTheory Complex

noncomputable section

variable {ι : Type} [Fintype ι]

open Classical

def paT : EuclideanSpace ℂ (Fin (Fintype.card ι)) ≃ₗᵢ[ℂ] EuclideanSpace ℂ ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin ι).symm

theorem paT_apply (z : EuclideanSpace ℂ (Fin (Fintype.card ι))) (i : ι) :
    paT z i = z (Fintype.equivFin ι i) := by
  first
  | rfl
  | simp [paT, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply]

theorem Hf_eq_inner (v w : EuclideanSpace ℂ ι) : Hf v w = inner ℂ w v := by
  exact FPw.Hf_eq_inner v w

theorem paMono_smul_paT (α : ι →₀ ℕ) (t : ℝ) (z : EuclideanSpace ℂ (Fin (Fintype.card ι))) :
    paMono α (t • paT z) = (t : ℂ) ^ α.degree *
      paMono (Finsupp.equivMapDomain (Fintype.equivFin ι) α) z := by
  simp only [paMono, paPF, MvPolynomial.eval_monomial, one_mul, Finsupp.prod_equivMapDomain,
    PiLp.smul_apply, paT_apply, Complex.real_smul, mul_pow]
  rw [Finsupp.prod, Finsupp.prod, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

theorem comp_smul_paT_mem_paPoly {c : ℕ} (t : ℝ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    (fun z => F (t • paT z)) ∈ paPoly (ι := Fin (Fintype.card ι)) c := by
  induction hF using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨α, hα, rfl⟩ := hx
    have hfun : (fun z => paMono α (t • paT z)) = ((t : ℂ) ^ α.degree) •
        paMono (ι := Fin (Fintype.card ι)) (Finsupp.equivMapDomain (Fintype.equivFin ι) α) :=
      funext fun z => by rw [Pi.smul_apply, smul_eq_mul, paMono_smul_paT]
    rw [hfun]
    refine (paPoly _).smul_mem _ ?_
    have hd : (Finsupp.equivMapDomain (Fintype.equivFin ι) α).sum (fun _ e => e) ≤ c := by
      rw [Finsupp.sum_equivMapDomain]
      exact (Finset.mem_filter.1 (Finset.mem_coe.1 hα)).2
    refine paPF_mem_paPoly (p := MvPolynomial.monomial _ 1) ?_
    rw [MvPolynomial.totalDegree_monomial _ one_ne_zero]
    exact hd
  | zero => exact (paPoly _).zero_mem
  | add x y _ _ hx hy => exact (paPoly _).add_mem hx hy
  | smul a x _ hx => exact (paPoly _).smul_mem a hx

theorem paIsPoly {c : ℕ} (t : ℝ) {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    IsPolyLE c (fun z => F (t • paT z)) := by
  obtain ⟨p, hp, hpe⟩ := paPoly_exists (comp_smul_paT_mem_paPoly t hF)
  exact ⟨p, hp, fun z => congrFun hpe z⟩

def paTR : EuclideanSpace ℂ (Fin (Fintype.card ι)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ ι :=
  { toLinearEquiv := (paT (ι := ι)).toLinearEquiv.restrictScalars ℝ
    norm_map' := (paT (ι := ι)).norm_map }

theorem paTR_apply (z : EuclideanSpace ℂ (Fin (Fintype.card ι))) : paTR z = paT z := rfl

theorem paFock_cv {q : ℕ} (hq : 1 ≤ q) (H K : EuclideanSpace ℂ ι → ℂ) :
    fockIP (fun z => H ((Real.sqrt (q * Real.pi))⁻¹ • paT z))
      (fun z => K ((Real.sqrt (q * Real.pi))⁻¹ • paT z)) = (q : ℂ) ^ Fintype.card ι * paIP q H K := by
  set s : ℝ := Real.sqrt (q * Real.pi) with hs
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt (by positivity)
  let g : EuclideanSpace ℂ ι → ℂ := fun w =>
    H (s⁻¹ • w) * (starRingEnd ℂ) (K (s⁻¹ • w)) * (Real.exp (-‖w‖ ^ 2) : ℂ)

  have h1 : (∫ z : EuclideanSpace ℂ (Fin (Fintype.card ι)), H (s⁻¹ • paT z) *
      (starRingEnd ℂ) (K (s⁻¹ • paT z)) * (Real.exp (-‖z‖ ^ 2) : ℂ)) = ∫ w, g w := by
    rw [← (paTR (ι := ι)).measurePreserving.integral_comp
      (paTR (ι := ι)).toHomeomorph.measurableEmbedding g]
    congr 1
    ext z
    simp only [g, paTR_apply, LinearIsometryEquiv.norm_map]

  have hd : Module.finrank ℝ (EuclideanSpace ℂ ι) = 2 * Fintype.card ι := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace]
  have h2 : ∫ w, g w = (s ^ (2 * Fintype.card ι) : ℝ) • paIP q H K := by
    have h3 := MeasureTheory.Measure.integral_comp_smul
      (volume : Measure (EuclideanSpace ℂ ι)) g s
    rw [hd] at h3
    have hg : (fun x => g (s • x)) = fun v => H v * (starRingEnd ℂ) (K v) * (paW q v : ℂ) := by
      ext v
      simp only [g, paW]
      rw [smul_smul, inv_mul_cancel₀ hs0.ne', one_smul, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs0, mul_pow, hs2]
      simp only [neg_mul]
    rw [hg, abs_of_pos (by positivity)] at h3
    unfold paIP
    rw [h3, smul_smul, mul_inv_cancel₀ (by positivity), one_smul]
  unfold fockIP
  rw [h1, h2, pow_mul, hs2, Complex.real_smul]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  rw [mul_pow]
  field_simp

theorem polynomial_translate_innerProduct_bound {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    ‖paIP q (paU q a F) G‖ ≤ 2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
      Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) * paN q F * paN q G := by
  set s : ℝ := Real.sqrt (q * Real.pi) with hs
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = q * Real.pi := Real.sq_sqrt (by positivity)
  have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs0.ne'
  have hqpi : (q : ℂ) * (Real.pi : ℂ) = (s : ℂ) ^ 2 := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul, ← hs2]
    push_cast
    ring

  set a' : EuclideanSpace ℂ (Fin (Fintype.card ι)) := s • (paT (ι := ι)).symm a with ha'
  have hna : ‖a'‖ = s * ‖a‖ := by
    rw [ha', norm_smul, Real.norm_eq_abs, abs_of_pos hs0, LinearIsometryEquiv.norm_map]
  have hT : paT (s • (paT (ι := ι)).symm a) = s • a := by
    rw [← paTR_apply, map_smul, paTR_apply, LinearIsometryEquiv.apply_symm_apply]
  have hU : (fun z => paU q a F (s⁻¹ • paT z)) = fockU a' (fun z => F (s⁻¹ • paT z)) := by
    ext z
    unfold paU fockU
    congr 1
    · congr 1
      rw [hna, show (∑ i, z i * (starRingEnd ℂ) (a' i)) = Hf z a' from rfl, Hf_eq_inner, Hf_eq_inner,
        Hf_eq_inner, ← Complex.coe_smul s⁻¹ (paT z), inner_smul_right, ha',
        ← Complex.coe_smul s, inner_smul_left, inner_self_eq_norm_sq_to_K,
        ← (paT (ι := ι)).inner_map_map, LinearIsometryEquiv.apply_symm_apply, hqpi]
      simp only [Complex.conj_ofReal]
      push_cast
      field_simp
      first
      | rfl
      | ring
    · congr 1
      rw [map_sub, hT, smul_sub, smul_smul, inv_mul_cancel₀ hs0.ne', one_smul]
  have hF' := paIsPoly s⁻¹ hF
  have hG' := paIsPoly s⁻¹ hG
  have hB := fockU_coeff_le a' _ _ hF' hG'
  rw [← hU, paFock_cv hq, paFock_cv hq, paFock_cv hq] at hB
  have hqn : (0 : ℝ) < (q : ℝ) ^ Fintype.card ι := by positivity
  have hre : ∀ H : EuclideanSpace ℂ ι → ℂ,
      Real.sqrt ((q : ℂ) ^ Fintype.card ι * paIP q H H).re =
        Real.sqrt ((q : ℝ) ^ Fintype.card ι) * paN q H := by
    intro H
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
      Real.sqrt_mul hqn.le]
    rfl
  rw [hre, hre, norm_mul, norm_pow, Complex.norm_natCast, hna] at hB
  have hsq : Real.sqrt ((q : ℝ) ^ Fintype.card ι) * Real.sqrt ((q : ℝ) ^ Fintype.card ι) =
      (q : ℝ) ^ Fintype.card ι := Real.mul_self_sqrt hqn.le
  have hexp : Real.exp (-(s * ‖a‖) ^ 2 / 16) = Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) := by
    rw [mul_pow, hs2]
    ring_nf
  rw [hexp] at hB
  have hB' : (q : ℝ) ^ Fintype.card ι * ‖paIP q (paU q a F) G‖ ≤ (q : ℝ) ^ Fintype.card ι *
      (2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
        Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) * paN q F * paN q G) := by
    calc _ ≤ _ := hB
      _ = _ := by
        linear_combination (2 ^ (1 + 3 * ((Fintype.card ι : ℝ) + c) / 2) *
          Real.exp (-(q * Real.pi) * ‖a‖ ^ 2 / 16) * paN q F * paN q G) * hsq
  exact le_of_mul_le_mul_left hB' hqn

theorem paTail (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2) :
    Summable (fun γ : lat Y.b => if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) ∧
    ∑' γ : lat Y.b, (if (γ : EuclideanSpace ℂ ι) = 0 then 0 else
      Real.exp (-(q * Real.pi) * ‖(γ : EuclideanSpace ℂ ι)‖ ^ 2 / 16)) ≤
      2 * 9 ^ Fintype.card ι * Real.exp (-R0 ^ 2 / 16) := by
  exact FPw.paTail hP hA Y hq hR0 hlat hR

theorem paHf_contDiff (a : EuclideanSpace ℂ ι) :
    ContDiff ℂ (⊤ : ℕ∞) (fun v : EuclideanSpace ℂ ι => Hf v a) := by
  show ContDiff ℂ (⊤ : ℕ∞) (fun v : EuclideanSpace ℂ ι => ∑ i, v i * (starRingEnd ℂ) (a i))
  exact ContDiff.sum fun i _ =>
    (EuclideanSpace.proj i : EuclideanSpace ℂ ι →L[ℂ] ℂ).contDiff.mul contDiff_const

theorem paU_contDiff {q c : ℕ} (a : EuclideanSpace ℂ ι) {F : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) : ContDiff ℂ (⊤ : ℕ∞) (paU q a F) := by
  obtain ⟨p, -, rfl⟩ := paPoly_exists hF
  unfold paU
  refine ContDiff.mul ?_ ((paPF_contDiff p).comp (contDiff_id.sub contDiff_const))
  exact Complex.contDiff_exp.comp ((contDiff_const.mul (paHf_contDiff a)).sub contDiff_const)

theorem paD_add (α : ι →₀ ℕ) {H1 H2 : EuclideanSpace ℂ ι → ℂ} (h1 : ContDiff ℂ (⊤ : ℕ∞) H1)
    (h2 : ContDiff ℂ (⊤ : ℕ∞) H2) : paD α (H1 + H2) = paD α H1 + paD α H2 := by
  exact FPw.paD_add α h1 h2

theorem paD_smul (α : ι →₀ ℕ) (a : ℂ) {H : EuclideanSpace ℂ ι → ℂ}
    (h : ContDiff ℂ (⊤ : ℕ∞) H) : paD α (a • H) = a * paD α H := by
  exact FPw.paD_smul α a h

theorem gaussianInner_jet {q c : ℕ} (hq : 1 ≤ q) (a : EuclideanSpace ℂ ι) {F G : EuclideanSpace ℂ ι → ℂ}
    (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    paIP q (paU q a F) G = paIP q (paJet c (paU q a F)) G := by
  exact FPw.gaussianInner_jet' hq a hF hG

theorem paUnfold (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hC : ∀ γ ∈ lat Y.b, ∀ γ' ∈ lat Y.b,
      Y.ka (γ + γ') = Y.ka γ * Y.ka γ' * cexp (-(Real.pi * q * (Hf γ γ').im) * I))
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) :
    Y.l2 q (paTh Y q F) = (paIP q (paTh Y q F) F).re := by
  exact FPw.paUnfold_w hP hA Y hq hR0 hC hlat hR hF

theorem paTh_IP (hP : Ext.PackingCount) (hA : Ext.GaussianTailBound) (Y : GT ι) {q c : ℕ} {R0 : ℝ}
    (hq : 1 ≤ q) (hR0 : 0 < R0)
    (hlat : ∀ γ ∈ lat Y.b, γ ≠ 0 → R0 ≤ Real.sqrt (q * Real.pi) * ‖γ‖)
    (hR : 16 * (2 * (Fintype.card ι : ℝ) + 1) ≤ R0 ^ 2)
    {F G : EuclideanSpace ℂ ι → ℂ} (hF : F ∈ paPoly c) (hG : G ∈ paPoly c) :
    HasSum (fun γ : lat Y.b => Y.ka γ * paIP q (paU q γ F) G) (paIP q (paTh Y q F) G) := by
  exact FPw.gaussianInner_theta' hP hA Y hq hR0 hlat hR hF hG

theorem paMono_contDiff (β : ι →₀ ℕ) : ContDiff ℂ (⊤ : ℕ∞) (paMono (ι := ι) β) :=
  paPF_contDiff _

theorem pa_cd_sum (s : Finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (∑ β ∈ s, f β • paMono (ι := ι) β) := by
  have h := ContDiff.sum (𝕜 := ℂ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (s := s)
    (f := fun β v => f β * paMono (ι := ι) β v) fun β _ => contDiff_const.mul (paMono_contDiff β)
  convert h using 1
  ext v
  simp [Finset.sum_apply]

theorem pa_cd_smul (a : ℂ) (β : ι →₀ ℕ) : ContDiff ℂ (⊤ : ℕ∞) (a • paMono (ι := ι) β) :=
  (paMono_contDiff β).const_smul a

private theorem paD_sum_smul_paMono (α : ι →₀ ℕ) (s : Finset (ι →₀ ℕ)) (f : (ι →₀ ℕ) → ℂ) :
    paD α (∑ β ∈ s, f β • paMono (ι := ι) β) = ∑ β ∈ s, f β * paD α (paMono β) := by
  refine Finset.induction_on s (by simp [FPw.paD_zero]) ?_
  intro b s hb ih
  rw [Finset.sum_insert hb, FPw.paD_add α (pa_cd_smul _ _) (pa_cd_sum _ _),
    FPw.paD_smul α _ (paMono_contDiff _), ih, Finset.sum_insert hb]

theorem paD_jet (c : ℕ) (H : EuclideanSpace ℂ ι → ℂ) {α : ι →₀ ℕ} (hα : α ∈ paS c) :
    paD α (paJet c H) = paD α H := by
  show paD α (∑ β ∈ paS c, (paD β H / paFact β) • paMono β) = _
  rw [paD_sum_smul_paMono, Finset.sum_eq_single α]
  · have hf : (paFact α : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun i _ => Nat.factorial_ne_zero _)
    rw [paD_mono, if_pos rfl, div_mul_cancel₀ _ hf]
  · intro β _ hβ
    rw [paD_mono, if_neg (Ne.symm hβ), mul_zero]
  · intro h
    exact absurd hα h

private theorem paIP_sum_smul_paMono_left {q c : ℕ} (hq : 1 ≤ q) {G : EuclideanSpace ℂ ι → ℂ}
    (hG : G ∈ paPoly c) (f : (ι →₀ ℕ) → ℂ) (s : Finset (ι →₀ ℕ)) (hs : s ⊆ paS c) :
    paIP q (∑ β ∈ s, f β • paMono β) G = ∑ β ∈ s, f β * paIP q (paMono β) G := by
  induction s using Finset.induction_on with
  | empty => simp [paIP]
  | insert b s hb ih =>
    obtain ⟨hb', hs'⟩ := Finset.insert_subset_iff.1 hs
    have hm : ∀ β ∈ paS c, paMono (ι := ι) β ∈ paPoly c := fun β h =>
      Submodule.subset_span ⟨β, Finset.mem_coe.2 h, rfl⟩
    rw [Finset.sum_insert hb, gaussianInner_add_left hq ((paPoly c).smul_mem _ (hm b hb'))
      (Submodule.sum_mem _ fun β h => (paPoly c).smul_mem _ (hm β (hs' h))) hG,
      gaussianInner_smul_left, ih hs', Finset.sum_insert hb]

theorem gaussianInner_jet_eq_sum {q c : ℕ} (hq : 1 ≤ q) (H : EuclideanSpace ℂ ι → ℂ) {G : EuclideanSpace ℂ ι → ℂ}
    (hG : G ∈ paPoly c) :
    paIP q (paJet c H) G = ∑ α ∈ paS c, (paD α H / paFact α) * paIP q (paMono α) G := by
  exact paIP_sum_smul_paMono_left hq hG _ _ subset_rfl

theorem paNum (g : ℕ) (c R0 : ℝ) (hc : 0 ≤ c) (h270 : 270 ≤ R0 ^ 2)
    (h90 : 90 * ((g : ℝ) + c) ≤ R0 ^ 2) :
    2 ^ (1 + 3 * ((g : ℝ) + c) / 2) * (2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)) ≤ 1 / 2 := by
  have hl2 : Real.log 2 < 0.7 := lt_trans Real.log_two_lt_d9 (by norm_num)
  have hy : 0 ≤ 1 + 3 * ((g : ℝ) + c) / 2 := by positivity
  have e1 : (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) =
      Real.exp (Real.log 2 * (1 + 3 * ((g : ℝ) + c) / 2)) := Real.rpow_def_of_pos (by norm_num) _
  have e9 : (9 : ℝ) ^ g ≤ Real.exp (2.3 * g) := by
    rw [mul_comm, Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by norm_num) ?_ g
    have h1 := Real.exp_one_gt_d9
    have h2 := Real.add_one_le_exp (0.3 : ℝ)
    have h3 : Real.exp 2.3 = Real.exp 1 * Real.exp 1 * Real.exp 0.3 := by
      rw [← Real.exp_add, ← Real.exp_add]
      norm_num
    rw [h3]
    nlinarith
  have e2 : (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
  have key : (2 : ℝ) ^ (1 + 3 * ((g : ℝ) + c) / 2) * (2 * 9 ^ g * Real.exp (-R0 ^ 2 / 16)) ≤
      Real.exp (Real.log 2 * (1 + 3 * ((g : ℝ) + c) / 2) + (Real.log 2 + (2.3 * g + -R0 ^ 2 / 16))) := by
    rw [Real.exp_add, Real.exp_add, Real.exp_add, e1, ← mul_assoc (Real.exp (Real.log 2))]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    exact mul_le_mul (le_of_eq e2) e9 (by positivity) (Real.exp_pos _).le
  refine key.trans ?_
  have hhalf : Real.exp (-Real.log 2) = 1 / 2 := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  rw [← hhalf]
  apply Real.exp_le_exp.2
  have hm : Real.log 2 * (1 + 3 * ((g : ℝ) + c) / 2) ≤ 0.7 * (1 + 3 * ((g : ℝ) + c) / 2) :=
    mul_le_mul_of_nonneg_right hl2.le hy
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  nlinarith

end

end ReciprocityTheory.ChartRestriction.G.I2
