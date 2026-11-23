import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
import ReciprocityTheory.Chebotarev.EulerSum
open NumberField Complex Filter Topology
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section
namespace GlobalTheory.ZetaPole

theorem tendsto_pow_mul (F : Type) [Field F] [NumberField F] (C C' : ClassGroup (𝓞 F)) (Z Z' : ℂ → ℂ)
    (hZ' : IsPartialZeta C' Z')
    (hfe : ∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
      (dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
        (dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) :
    ∃ L : ℂ, Tendsto (fun s => (s - 1) ^ Module.finrank ℚ F * Z s) (𝓝[≠] 1) (𝓝 L) := by
  set f := Module.finrank ℚ F
  set d : ℂ := (dF F : ℂ)
  have hd0 : d ≠ 0 := by
    simp only [d, dF, ne_eq, ofReal_eq_zero, abs_eq_zero, Int.cast_eq_zero]
    exact discr_ne_zero F
  have hev : ∀ᶠ s in 𝓝[≠] (1 : ℂ), (s - 1) ^ f * Z s =
      (d ^ ((1 - s) / 2) / d ^ (s / 2)) * ((Complex.Gammaℝ s)⁻¹) ^ f *
        (-((1 - s) * Complex.Gammaℝ (1 - s))) ^ f * Z' (1 - s) := by
    have hb : Metric.ball (1 : ℂ) 1 ∈ 𝓝[≠] (1 : ℂ) :=
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [hb, self_mem_nhdsWithin] with s hs hs1
    have hs1' : s ≠ 1 := hs1
    rw [Metric.mem_ball, dist_eq] at hs
    have hre : 0 < s.re := by
      have := abs_re_le_norm (s - 1)
      rw [sub_re, one_re] at this
      linarith [abs_le.mp (this.trans hs.le) |>.1, neg_abs_le (s.re - 1)]
    have hΓ : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hre
    have h1 : ∀ n : ℕ, s ≠ -2 * n := by
      intro n h
      have := congrArg Complex.re h
      simp at this
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have h2 : ∀ n : ℕ, 1 - s ≠ -2 * n := by
      intro n h
      have hs' : s - 1 = 2 * n := by linear_combination -h
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact hs1' (by simpa [sub_eq_zero] using hs')
      · rw [hs'] at hs
        have : ‖(2 * n : ℂ)‖ = 2 * n := by
          rw [show (2 * n : ℂ) = ((2 * n : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by positivity)]
        rw [this] at hs
        have : (1:ℝ) ≤ n := by exact_mod_cast hn
        linarith
    have e := hfe s h1 h2
    have hds : d ^ (s / 2) ≠ 0 := by
      rw [Ne, cpow_eq_zero_iff]; tauto
    have hZs : Z s = d ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ f * Z' (1 - s) /
        (d ^ (s / 2) * Complex.Gammaℝ s ^ f) := by
      rw [eq_div_iff (mul_ne_zero hds (pow_ne_zero _ hΓ)), ← e]; ring
    rw [hZs, show -((1 - s) * Complex.Gammaℝ (1 - s)) = (s - 1) * Complex.Gammaℝ (1 - s) by ring, mul_pow,
      inv_pow, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  refine ⟨(d ^ (((1:ℂ) - 1) / 2) / d ^ ((1:ℂ) / 2)) * ((Complex.Gammaℝ 1)⁻¹) ^ f * (-2) ^ f * Z' ((1:ℂ) - 1), ?_⟩
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hc1 : ContinuousAt (fun s : ℂ => d ^ ((1 - s) / 2) / d ^ (s / 2)) 1 := by
    refine ContinuousAt.div ?_ ?_ ?_
    · exact (continuousAt_const_cpow hd0).comp (by fun_prop)
    · exact (continuousAt_const_cpow hd0).comp (by fun_prop)
    · rw [Ne, cpow_eq_zero_iff]; tauto
  have hc2 : ContinuousAt (fun s : ℂ => ((Complex.Gammaℝ s)⁻¹) ^ f) 1 :=
    (Complex.differentiable_Gammaℝ_inv.continuous.pow f).continuousAt
  have hZ'0 : ContinuousAt (fun s : ℂ => Z' (1 - s)) 1 := by
    have : DifferentiableAt ℂ Z' (1 - 1) := by
      refine hZ'.1.differentiableAt (isOpen_compl_singleton.mem_nhds ?_)
      simp
    exact this.continuousAt.comp (by fun_prop)
  have hres : Tendsto (fun s : ℂ => -((1 - s) * Complex.Gammaℝ (1 - s))) (𝓝[≠] 1) (𝓝 (-2)) := by
    have hm : Tendsto (fun s : ℂ => 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, ?_⟩
      · have : Tendsto (fun s : ℂ => 1 - s) (𝓝 1) (𝓝 (1 - 1)) := (continuous_const.sub continuous_id).tendsto 1
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff, sub_eq_zero] at hs ⊢
        exact fun h => hs h.symm
    exact (Complex.Gammaℝ_residue_zero.comp hm).neg
  exact ((hc1.tendsto.mono_left nhdsWithin_le_nhds).mul (hc2.tendsto.mono_left nhdsWithin_le_nhds) |>.mul
    (hres.pow f)).mul (hZ'0.tendsto.mono_left nhdsWithin_le_nhds)

end GlobalTheory.ZetaPole

noncomputable section
namespace GlobalTheory.ZetaPole

theorem norm_le_idealZetaR (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) {x : ℝ} (hx : 1 < x) : ‖Z x‖ ≤ ReciprocityTheory.Cheb.idealZetaR F x := by
  have hs := hZ.2 x (by simpa using hx)
  set r : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} → ℝ :=
    fun J => ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℝ) ^ (-x) with hr
  have hterm : (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} =>
      ((Ideal.absNorm (J.1 : Ideal (𝓞 F)) : ℕ) : ℂ) ^ (-(x : ℂ))) = fun J => ((r J : ℝ) : ℂ) := by
    funext J
    rw [hr, Complex.ofReal_cpow (Nat.cast_nonneg _), Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [hterm] at hs
  have hre := (Complex.hasSum_re hs)
  have him := (Complex.hasSum_im hs)
  simp only [Complex.ofReal_re, Complex.ofReal_im] at hre him
  have him0 : (Z x).im = 0 := (hasSum_zero.unique him).symm
  have hnn : 0 ≤ (Z x).re := hre.nonneg fun J => by positivity
  have hZx : Z x = ((Z x).re : ℂ) := Complex.ext (by simp) (by simp [him0])
  rw [hZx, norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
  refine hasSum_le_of_sum_le hre fun T => ?_
  classical
  have hinj : Function.Injective (fun J : {J : (Ideal (𝓞 F))⁰ // ClassGroup.mk0 J = C} => (J.1 : Ideal (𝓞 F))) := by
    intro a b h
    exact Subtype.ext (Subtype.ext h)
  have := ReciprocityTheory.Cheb.sum_le_idealZetaR F hx (T.image fun J => (J.1 : Ideal (𝓞 F)))
  rw [Finset.sum_image fun a _ b _ h => hinj h] at this
  exact this

theorem bdd_right (F : Type) [Field F] [NumberField F] (C : ClassGroup (𝓞 F)) (Z : ℂ → ℂ)
    (hZ : IsPartialZeta C Z) : ∃ B : ℝ, ∀ᶠ x : ℝ in 𝓝[>] 1, ‖((x : ℂ) - 1) * Z x‖ ≤ B := by
  refine ⟨dedekindZeta_residue F + 1, ?_⟩
  have ht := (tendsto_sub_one_mul_dedekindZeta_nhdsGT F).norm
  have hlt : ‖(dedekindZeta_residue F : ℂ)‖ < dedekindZeta_residue F + 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (dedekindZeta_residue_pos F)]; linarith
  filter_upwards [ht.eventually (eventually_lt_nhds hlt), self_mem_nhdsWithin] with x hx hx1
  have hx1' : 1 < x := hx1
  rw [ReciprocityTheory.Cheb.dedekindZeta_eq_idealZetaR F hx1'] at hx
  have h0 : 0 ≤ x - 1 := by linarith
  calc ‖((x : ℂ) - 1) * Z x‖ = (x - 1) * ‖Z x‖ := by
        rw [norm_mul, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
          Real.norm_eq_abs, abs_of_nonneg h0]
    _ ≤ (x - 1) * ReciprocityTheory.Cheb.idealZetaR F x := mul_le_mul_of_nonneg_left (norm_le_idealZetaR F C Z hZ hx1') h0
    _ ≤ ‖((x : ℂ) - 1) * ((ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ)‖ := by
        rw [show ((x : ℂ) - 1) * ((ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ) =
          (((x - 1) * ReciprocityTheory.Cheb.idealZetaR F x : ℝ) : ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs]
        exact le_abs_self _
    _ ≤ dedekindZeta_residue F + 1 := hx.le

end GlobalTheory.ZetaPole

noncomputable section
namespace GlobalTheory.ZetaPole

theorem zeta_simple_pole : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F]
    (C C' : ClassGroup (NumberField.RingOfIntegers F)) (Z Z' : ℂ → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C Z → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta C' Z' →
    (∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) → (∀ n : ℕ, 1 - s ≠ -2 * n) →
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * Z s =
        (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) * Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * Z' (1 - s)) →
    ∃ R : ℂ → ℂ, Differentiable ℂ R ∧ ∀ s : ℂ, s ≠ 1 → Z s = R s / (s - 1) := by
  intro F _ _ _ C C' Z Z' hZ hZ' hfe
  set f := Module.finrank ℚ F
  have hdiff : ∀ s : ℂ, s ≠ 1 → DifferentiableAt ℂ Z s := fun s hs =>
    hZ.1.differentiableAt (isOpen_compl_singleton.mem_nhds hs)

  obtain ⟨L, hL⟩ := tendsto_pow_mul F C C' Z Z' hZ' hfe
  set h : ℂ → ℂ := fun s => (s - 1) ^ f * Z s
  have hHd : DifferentiableOn ℂ (Function.update h 1 (limUnder (𝓝[≠] 1) h)) Set.univ := by
    refine differentiableOn_update_limUnder_of_isLittleO Filter.univ_mem ?_ ?_
    · intro s hs
      have hs1 : s ≠ 1 := hs.2
      exact (((differentiableAt_id.sub_const 1).pow f).mul (hdiff s hs1)).differentiableWithinAt
    · exact ((hL.sub_const (h 1)).norm.isBoundedUnder_le).isLittleO_sub_self_inv
  set H := Function.update h 1 (limUnder (𝓝[≠] 1) h)
  have hHdf : Differentiable ℂ H := fun s => hHd.differentiableAt Filter.univ_mem
  have hHa : AnalyticAt ℂ H 1 := hHdf.analyticAt 1
  have hHh : ∀ s, s ≠ 1 → H s = (s - 1) ^ f * Z s := fun s hs => Function.update_of_ne hs _ _

  set g : ℂ → ℂ := fun s => (s - 1) * Z s
  have hpunct : ∀ {P : ℂ → Prop}, (∀ᶠ z in 𝓝 (1:ℂ), P z) → ∀ᶠ z in 𝓝[≠] (1:ℂ), P z ∧ z ≠ 1 := fun hP =>
    (eventually_nhdsWithin_of_eventually_nhds hP).and self_mem_nhdsWithin
  have hg : ∃ M, Tendsto g (𝓝[≠] 1) (𝓝 M) := by
    by_cases hz : ∀ᶠ z in 𝓝 (1:ℂ), H z = 0
    · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
      filter_upwards [hpunct hz] with z ⟨hz0, hz1⟩
      have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
      rw [hHh z hz1] at hz0
      have : Z z = 0 := (mul_eq_zero.mp hz0).resolve_left (pow_ne_zero _ hne)
      simp [g, this]
    · obtain ⟨n, G, hGa, hG1, hev⟩ := hHa.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
      rcases le_or_gt f (n + 1) with hfn | hfn
      · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hfn
        refine ⟨(1 - 1 : ℂ) ^ m * G 1, ?_⟩
        have hc : ContinuousAt (fun s : ℂ => (s - 1) ^ m * G s) 1 :=
          ((continuous_id.sub continuous_const).pow m).continuousAt.mul hGa.continuousAt
        refine (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
        filter_upwards [hpunct hev] with z ⟨hz0, hz1⟩
        have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
        rw [hHh z hz1, smul_eq_mul] at hz0
        apply mul_left_cancel₀ (pow_ne_zero f hne)
        simp only [g]
        calc (z - 1) ^ f * ((z - 1) ^ m * G z) = (z - 1) ^ (n + 1) * G z := by rw [hm]; ring
          _ = (z - 1) * ((z - 1) ^ f * Z z) := by rw [hz0]; ring
          _ = (z - 1) ^ f * ((z - 1) * Z z) := by ring
      · exfalso
        obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hfn

        have hev2 : ∀ᶠ z in 𝓝[≠] (1:ℂ), G z = (z - 1) ^ (k + 1) * g z := by
          filter_upwards [hpunct hev] with z ⟨hz0, hz1⟩
          have hne : (z - 1) ≠ 0 := sub_ne_zero.mpr hz1
          rw [hHh z hz1, smul_eq_mul] at hz0
          apply mul_left_cancel₀ (pow_ne_zero n hne)
          simp only [g]
          calc (z - 1) ^ n * G z = (z - 1) ^ f * Z z := hz0.symm
            _ = (z - 1) ^ n * ((z - 1) ^ (k + 1) * ((z - 1) * Z z)) := by rw [hk]; ring
        have hreal : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 1) (𝓝[≠] (1:ℂ)) := by
          rw [tendsto_nhdsWithin_iff]
          refine ⟨?_, ?_⟩
          · have := (Complex.continuous_ofReal.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (1:ℝ)))
            simpa using this
          · filter_upwards [self_mem_nhdsWithin] with x hx
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            intro h
            have : x = 1 := by exact_mod_cast h
            exact (ne_of_gt (show (1:ℝ) < x from hx)) this
        have hG : Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 (G 1)) :=
          (hGa.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).comp hreal
        obtain ⟨B, hB⟩ := bdd_right F C Z hZ
        have h0 : Tendsto (fun x : ℝ => G x) (𝓝[>] 1) (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          have hlim : Tendsto (fun x : ℝ => |x - 1| ^ (k + 1) * B) (𝓝[>] 1) (𝓝 0) := by
            have : Tendsto (fun x : ℝ => |x - 1| ^ (k + 1) * B) (𝓝 1) (𝓝 (|1 - 1| ^ (k + 1) * B)) :=
              (((continuous_id.sub continuous_const).abs.pow (k + 1)).mul continuous_const).tendsto 1
            simpa using this.mono_left nhdsWithin_le_nhds
          refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
          filter_upwards [hB, hreal.eventually hev2] with x hx hx2
          rw [hx2, norm_mul, norm_pow, show ((x : ℂ) - 1) = ((x - 1 : ℝ) : ℂ) by push_cast; ring, norm_real,
            Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (by simpa [g] using hx) (by positivity)
        exact hG1 (tendsto_nhds_unique hG h0)

  obtain ⟨M, hM⟩ := hg
  refine ⟨Function.update g 1 (limUnder (𝓝[≠] 1) g), ?_, ?_⟩
  · have hRd : DifferentiableOn ℂ (Function.update g 1 (limUnder (𝓝[≠] 1) g)) Set.univ := by
      refine differentiableOn_update_limUnder_of_isLittleO Filter.univ_mem ?_ ?_
      · intro s hs
        have hs1 : s ≠ 1 := hs.2
        exact ((differentiableAt_id.sub_const 1).mul (hdiff s hs1)).differentiableWithinAt
      · exact ((hM.sub_const (g 1)).norm.isBoundedUnder_le).isLittleO_sub_self_inv
    exact fun s => hRd.differentiableAt Filter.univ_mem
  · intro s hs
    rw [Function.update_of_ne hs]
    simp only [g]
    field_simp [sub_ne_zero.mpr hs]

end GlobalTheory.ZetaPole
