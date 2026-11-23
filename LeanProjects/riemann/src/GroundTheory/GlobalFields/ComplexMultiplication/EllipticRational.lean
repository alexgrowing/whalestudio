import Mathlib
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticFunctions
import GroundTheory.GlobalFields.ComplexMultiplication.EllipticConstant

open Complex Filter Topology Set Polynomial
open scoped PeriodPair

noncomputable section

namespace GroundTheory.Global
namespace Elliptic

variable {L : PeriodPair}

lemma meromorphicAt_eval {g : ℂ → ℂ} {x : ℂ} (hg : MeromorphicAt g x) (P : ℂ[X]) :
    MeromorphicAt (fun z ↦ P.eval (g z)) x := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simp only [eval_add]; fun_prop
  | monomial n a => simp only [eval_monomial]; fun_prop

lemma analyticAt_eval {g : ℂ → ℂ} {x : ℂ} (hg : AnalyticAt ℂ g x) (P : ℂ[X]) :
    AnalyticAt ℂ (fun z ↦ P.eval (g z)) x := by
  simpa using hg.aeval_polynomial P

lemma isPeriodic_weierstrassP : IsPeriodic L ℘[L] := fun z l hl ↦
  L.weierstrassP_add_coe z ⟨l, hl⟩

lemma isPeriodic_derivWeierstrassP : IsPeriodic L ℘'[L] := fun z l hl ↦
  L.derivWeierstrassP_add_coe z ⟨l, hl⟩

lemma isEllipticFunction_weierstrassP : IsEllipticFunction L ℘[L] :=
  ⟨L.meromorphic_weierstrassP, isPeriodic_weierstrassP⟩

lemma weierstrassP_eq_zpow_mul {z : ℂ} (hz : z ≠ 0) :
    ℘[L] z = z ^ (-2 : ℤ) * (z ^ 2 * L.weierstrassPExcept 0 z + 1) := by
  have h := L.ite_eq_one_sub_sq_mul_weierstrassP 0 L.lattice.zero_mem z
  rw [if_neg hz] at h
  have h' : z ^ 2 * ℘[L] z = z ^ 2 * L.weierstrassPExcept 0 z + 1 := by
    simpa using h
  have h2 : z ^ (-2 : ℤ) * z ^ 2 = 1 := by
    rw [zpow_neg, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero 2 hz)]
  rw [← h', ← mul_assoc, h2, one_mul]

lemma analyticAt_weierstrassP_laurent :
    AnalyticAt ℂ (fun z ↦ z ^ 2 * L.weierstrassPExcept 0 z + 1) 0 := by
  have := L.analyticAt_weierstrassPExcept 0
  fun_prop

lemma lt_meromorphicOrderAt_of_eventuallyEq {f w : ℂ → ℂ} {x : ℂ} {n : ℤ}
    (hw : AnalyticAt ℂ w x) (hw0 : w x = 0)
    (h : f =ᶠ[𝓝[≠] x] fun z ↦ (z - x) ^ n * w z) :
    (n : WithTop ℤ) < meromorphicOrderAt f x := by
  have e : (fun z ↦ (z - x) ^ n * w z) = (fun z ↦ z - x) ^ n * w := rfl
  have hm : MeromorphicAt ((fun z ↦ z - x) ^ n) x :=
    ((analyticAt_id.sub analyticAt_const).meromorphicAt (x := x)).zpow n
  rw [meromorphicOrderAt_congr h, e, meromorphicOrderAt_mul hm hw.meromorphicAt,
    meromorphicOrderAt_zpow_id_sub_const]
  have hpos : (1 : WithTop ℤ) ≤ meromorphicOrderAt w x := by
    rw [hw.meromorphicOrderAt_eq]
    have h1 : analyticOrderAt w x ≠ 0 := by
      rw [Ne, hw.analyticOrderAt_eq_zero]
      simpa using hw0
    cases h : analyticOrderAt w x with
    | top => simp
    | coe m =>
      rw [h] at h1
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (by exact_mod_cast h1)
      simp only [ENat.map_natCast]
      exact_mod_cast this
  cases ho : meromorphicOrderAt w x with
  | top => simp
  | coe m =>
    rw [ho] at hpos
    have : (1 : ℤ) ≤ m := by exact_mod_cast hpos
    exact_mod_cast (by omega : n < n + m)

private lemma coe_add_one_le_of_lt {o : ℤ} {x : WithTop ℤ} (h : (o : WithTop ℤ) < x) :
    ((o + 1 : ℤ) : WithTop ℤ) ≤ x := by
  cases x with
  | top => exact le_top
  | coe m =>
    have : o < m := by exact_mod_cast h
    exact_mod_cast (by omega : o + 1 ≤ m)

lemma even_of_meromorphicOrderAt_eq {f : ℂ → ℂ} (hf : MeromorphicAt f 0)
    (he : ∀ z, f (-z) = f z) {n : ℤ} (hn : meromorphicOrderAt f 0 = n) : Even n := by
  obtain ⟨u, hu, hu0, e⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  have hneg : Tendsto (fun z : ℂ ↦ -z) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · simpa using ((continuous_neg.tendsto (0 : ℂ)).mono_left nhdsWithin_le_nhds)
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simpa using hz
  have e' := hneg.eventually e
  have key : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (-1 : ℂ) ^ n * u (-z) = u z := by
    filter_upwards [e, e', self_mem_nhdsWithin] with z h1 h2 hz
    have hz' : z ≠ 0 := hz
    rw [he z, h1] at h2
    simp only [sub_zero, smul_eq_mul] at h2
    have h3 : z ^ n * u z = z ^ n * ((-1 : ℂ) ^ n * u (-z)) := by
      rw [h2, show -z = (-1 : ℂ) * z by ring, mul_zpow]
      ring
    exact (mul_left_cancel₀ (zpow_ne_zero n hz') h3).symm
  have hc : ContinuousAt (fun z ↦ (-1 : ℂ) ^ n * u (-z)) 0 := by
    have : ContinuousAt u (-0) := by simpa using hu.continuousAt
    exact continuousAt_const.mul (this.comp continuous_neg.continuousAt)
  have t1 : Tendsto u (𝓝[≠] 0) (𝓝 (u 0)) := hu.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 := (hc.tendsto.mono_left nhdsWithin_le_nhds).congr' key
  have heq : (-1 : ℂ) ^ n * u (-0) = u 0 := tendsto_nhds_unique t2 t1
  rw [neg_zero] at heq
  rcases Int.even_or_odd n with h | h
  · exact h
  · exfalso
    rw [h.neg_one_zpow] at heq
    apply hu0
    linear_combination -heq / 2

lemma exists_eventuallyEq_const_of_analyticAt_off_lattice {g : ℂ → ℂ} (hg : Meromorphic g)
    (hp : IsPeriodic L g) (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (h0 : 0 ≤ meromorphicOrderAt g 0) : ∃ c : ℂ, g =ᶠ[codiscrete ℂ] fun _ ↦ c := by
  refine exists_eventuallyEq_const_of_meromorphicOrderAt_nonneg L hg hp fun z ↦ ?_
  by_cases hz : z ∈ L.lattice
  · have := hp.meromorphicOrderAt_add hz 0
    rw [zero_add] at this
    rwa [this]
  · exact (han z hz).meromorphicOrderAt_nonneg

theorem exists_polynomial_of_even_of_analyticAt_off_lattice (n : ℕ) {g : ℂ → ℂ}
    (hg : Meromorphic g) (hp : IsPeriodic L g) (he : ∀ z, g (-z) = g z)
    (han : ∀ z ∉ L.lattice, AnalyticAt ℂ g z)
    (hn : ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt g 0) :
    ∃ P : ℂ[X], g =ᶠ[codiscrete ℂ] fun z ↦ P.eval (℘[L] z) := by
  induction n using Nat.strong_induction_on generalizing g with
  | _ n ih =>
  by_cases h0 : 0 ≤ meromorphicOrderAt g 0
  · obtain ⟨c, hc⟩ := exists_eventuallyEq_const_of_analyticAt_off_lattice hg hp han h0
    exact ⟨C c, by simpa using hc⟩
  push Not at h0
  obtain ⟨o, ho⟩ : ∃ o : ℤ, meromorphicOrderAt g 0 = o := by
    cases h : meromorphicOrderAt g 0 with
    | top => rw [h] at h0; exact absurd h0 (not_lt.2 le_top)
    | coe o => exact ⟨o, rfl⟩
  rw [ho] at h0 hn
  have ho0 : o < 0 := by exact_mod_cast h0
  have hno : -(n : ℤ) ≤ o := by exact_mod_cast hn
  obtain ⟨r, hr⟩ := even_of_meromorphicOrderAt_eq (hg 0) he ho
  obtain ⟨k, hk⟩ : ∃ k : ℕ, o = -2 * k := ⟨(-r).toNat, by omega⟩
  have hk1 : 1 ≤ k := by omega
  obtain ⟨u, hu, hu0, hgu⟩ := (meromorphicOrderAt_eq_int_iff (hg 0)).1 ho
  have hv := analyticAt_weierstrassP_laurent (L := L)
  have hdiff : (fun z ↦ g z - u 0 * ℘[L] z ^ k) =ᶠ[𝓝[≠] 0] fun z ↦ (z - 0) ^ o *
      (u z - u 0 * (z ^ 2 * L.weierstrassPExcept 0 z + 1) ^ k) := by
    filter_upwards [hgu, self_mem_nhdsWithin] with z h1 h2
    have h2' : z ≠ 0 := h2
    rw [h1, weierstrassP_eq_zpow_mul h2', mul_pow, ← zpow_natCast (z ^ (-2 : ℤ)), ← zpow_mul,
      hk, sub_zero, smul_eq_mul]
    ring
  have hlt := lt_meromorphicOrderAt_of_eventuallyEq
    (hu.sub (analyticAt_const.mul (hv.pow k))) (by simp) hdiff
  obtain ⟨P, hP⟩ := ih (2 * k - 1) (by omega) (g := fun z ↦ g z - u 0 * ℘[L] z ^ k)
    (fun z ↦ by have := hg z; have := L.meromorphic_weierstrassP z; fun_prop)
    (fun z l hl ↦ by simp only [hp z l hl, isPeriodic_weierstrassP z l hl])
    (fun z ↦ by simp only [he, L.weierstrassP_neg])
    (fun z hz ↦ by
      have := han z hz
      have := L.analyticOnNhd_weierstrassP z hz
      fun_prop)
    (by
      have e : ((-((2 * k - 1 : ℕ) : ℤ) : ℤ) : WithTop ℤ) = ((o + 1 : ℤ) : WithTop ℤ) := by
        congr 1; omega
      rw [e]
      exact coe_add_one_le_of_lt hlt)
  refine ⟨P + C (u 0) * X ^ k, ?_⟩
  filter_upwards [hP] with z hz
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  rw [← hz]
  ring

theorem exists_polynomial_mul_analyticAt_off_lattice {f : ℂ → ℂ} (hf : Meromorphic f)
    (hp : IsPeriodic L f) :
    ∃ Q : ℂ[X], Q ≠ 0 ∧ ∀ z ∉ L.lattice, AnalyticAt ℂ (fun w ↦ Q.eval (℘[L] w) * f w) z := by
  classical
  have hT := finite_image_singularSet L hf hp
  let rep : Torus L → ℂ := Function.surjInv (Torus.mk_surjective L)
  have hrep : ∀ t, Torus.mk L (rep t) = t := Function.surjInv_eq _
  let n : Torus L → ℕ := fun t ↦ (hf (rep t)).choose
  have hn : ∀ t, AnalyticAt ℂ (fun z ↦ (z - rep t) ^ n t • f z) (rep t) := fun t ↦
    (hf (rep t)).choose_spec
  let N := hT.toFinset.sup n
  refine ⟨∏ t ∈ hT.toFinset, (X - C (℘[L] (rep t))) ^ N, ?_, fun z hz ↦ ?_⟩
  · exact Finset.prod_ne_zero_iff.2 fun t _ ↦ pow_ne_zero _ (X_sub_C_ne_zero _)
  have h℘ : AnalyticAt ℂ ℘[L] z := L.analyticOnNhd_weierstrassP z hz
  by_cases hfz : AnalyticAt ℂ f z
  · exact (analyticAt_eval h℘ _).mul hfz
  have ht : Torus.mk L z ∈ hT.toFinset := hT.mem_toFinset.2 ⟨z, hfz, rfl⟩
  have hza : z - rep (Torus.mk L z) ∈ L.lattice := (Torus.mk_eq_mk_iff L).1 (hrep _).symm
  have h℘a : ℘[L] (rep (Torus.mk L z)) = ℘[L] z :=
    isPeriodic_weierstrassP.eq_of_mk_eq (hrep _)
  have hφ : AnalyticAt ℂ (fun w ↦ ℘[L] w - ℘[L] z) z := h℘.sub analyticAt_const
  have hdφ : AnalyticAt ℂ (dslope (fun w ↦ ℘[L] w - ℘[L] z) z) z := by
    obtain ⟨p, hp'⟩ := hφ
    exact ⟨_, hp'.has_fpower_series_dslope_fslope⟩
  have hφeq : ∀ w, ℘[L] w - ℘[L] z = (w - z) * dslope (fun w ↦ ℘[L] w - ℘[L] z) z w := by
    intro w
    have := sub_smul_dslope_of_zero (f := fun w ↦ ℘[L] w - ℘[L] z) (sub_self _) w
    simp only [smul_eq_mul] at this
    exact this.symm
  have hnN : n (Torus.mk L z) ≤ N := Finset.le_sup ht
  have h1 : AnalyticAt ℂ (fun w ↦ (w - z) ^ n (Torus.mk L z) * f w) z := by
    set a := rep (Torus.mk L z)
    have hF : AnalyticAt ℂ (fun u ↦ (u - a) ^ n (Torus.mk L z) • f u) (z - (z - a)) := by
      rw [sub_sub_cancel]; exact hn _
    have := hF.comp (f := fun w ↦ w - (z - a)) (by fun_prop)
    refine this.congr (Eventually.of_forall fun w ↦ ?_)
    simp only [Function.comp_apply, smul_eq_mul]
    rw [show w - (z - a) - a = w - z by ring, hp.sub w hza]
  have hfN : AnalyticAt ℂ (fun w ↦ (w - z) ^ N * f w) z := by
    have e : (fun w ↦ (w - z) ^ N * f w) =
        fun w ↦ (w - z) ^ (N - n (Torus.mk L z)) * ((w - z) ^ n (Torus.mk L z) * f w) := by
      funext w; rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnN]
    rw [e]
    fun_prop
  generalize dslope (fun w ↦ ℘[L] w - ℘[L] z) z = D at hdφ hφeq
  refine (((hdφ.pow N).mul (analyticAt_eval h℘
    (∏ s ∈ hT.toFinset.erase (Torus.mk L z), (X - C (℘[L] (rep s))) ^ N))).mul hfN).congr
    (Eventually.of_forall fun w ↦ ?_)
  simp only [Pi.mul_apply, Pi.pow_apply]
  rw [← Finset.mul_prod_erase hT.toFinset (fun s ↦ (X - C (℘[L] (rep s))) ^ N) ht]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, h℘a]
  rw [hφeq w, mul_pow]
  ring

lemma eventually_nhdsNE_zero_eval_weierstrassP_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), Q.eval (℘[L] z) ≠ 0 := by
  have hcob : Tendsto ℘[L] (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
    apply tendsto_cobounded_of_meromorphicOrderAt_neg
    rw [L.order_weierstrassP 0 L.lattice.zero_mem]
    decide
  have hb : Bornology.IsBounded {w : ℂ | Q.IsRoot w} :=
    (Polynomial.finite_setOfPred_isRoot hQ).isBounded
  filter_upwards [hcob.eventually hb] with z hz
  exact hz

lemma eventually_codiscrete_ne_zero_of_nhdsNE {F : ℂ → ℂ} (hF : Meromorphic F)
    (h : ∀ᶠ z in 𝓝[≠] (0 : ℂ), F z ≠ 0) : ∀ᶠ z in codiscrete ℂ, F z ≠ 0 := by
  have h0 : meromorphicOrderAt F 0 ≠ ⊤ :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hF 0)).2 h
  have hall : ∀ u ∈ (univ : Set ℂ), meromorphicOrderAt F u ≠ ⊤ := fun u _ ↦
    (hF.meromorphicOn (s := univ)).meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (mem_univ 0) (mem_univ u) h0
  exact MeromorphicAt.MeromorphicOn.codiscreteWithin_setOfPred_ne_zero
    (hF.meromorphicOn (s := univ)) hall

lemma eventually_codiscrete_eval_weierstrassP_ne_zero {Q : ℂ[X]} (hQ : Q ≠ 0) :
    ∀ᶠ z in codiscrete ℂ, Q.eval (℘[L] z) ≠ 0 :=
  eventually_codiscrete_ne_zero_of_nhdsNE (fun z ↦ meromorphicAt_eval
    (L.meromorphic_weierstrassP z) Q) (eventually_nhdsNE_zero_eval_weierstrassP_ne_zero hQ)

lemma eventually_codiscrete_derivWeierstrassP_ne_zero :
    ∀ᶠ z in codiscrete ℂ, ℘'[L] z ≠ 0 := by
  apply eventually_codiscrete_ne_zero_of_nhdsNE L.meromorphic_derivWeierstrassP
  have hR : (C 4 * X ^ 3 - C L.g₂ * X - C L.g₃ : ℂ[X]) ≠ 0 := by
    intro h
    have := congrArg (fun p : ℂ[X] ↦ p.coeff 3) h
    norm_num [coeff_X, coeff_C] at this
  filter_upwards [eventually_nhdsNE_zero_eval_weierstrassP_ne_zero hR,
    mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds 0),
    self_mem_nhdsWithin] with z hz hzl hz0
  intro h
  have hzL : z ∉ L.lattice := fun hm ↦ hzl ⟨hm, hz0⟩
  have := L.derivWeierstrassP_sq z hzL
  rw [h] at this
  apply hz
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X]
  linear_combination -this

theorem exists_polynomial_div_of_even {f : ℂ → ℂ} (hf : IsEllipticFunction L f)
    (he : ∀ z, f (-z) = f z) :
    ∃ P Q : ℂ[X], Q ≠ 0 ∧ f =ᶠ[codiscrete ℂ] fun z ↦ P.eval (℘[L] z) / Q.eval (℘[L] z) := by
  obtain ⟨Q, hQ, hQa⟩ := exists_polynomial_mul_analyticAt_off_lattice hf.1 hf.2
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ((-(n : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun w ↦ Q.eval (℘[L] w) * f w) 0 := by
    cases h : meromorphicOrderAt (fun w ↦ Q.eval (℘[L] w) * f w) 0 with
    | top => exact ⟨0, le_top⟩
    | coe o => exact ⟨o.natAbs, by exact_mod_cast (by omega : -(o.natAbs : ℤ) ≤ o)⟩
  obtain ⟨P, hP⟩ := exists_polynomial_of_even_of_analyticAt_off_lattice n
    (g := fun w ↦ Q.eval (℘[L] w) * f w)
    (fun z ↦ by
      have := hf.1 z
      have := meromorphicAt_eval (L.meromorphic_weierstrassP z) Q
      fun_prop)
    (fun z l hl ↦ by simp only [hf.2 z l hl, isPeriodic_weierstrassP z l hl])
    (fun z ↦ by simp only [he, L.weierstrassP_neg]) hQa hn
  refine ⟨P, Q, hQ, ?_⟩
  filter_upwards [hP, eventually_codiscrete_eval_weierstrassP_ne_zero hQ] with z hz hQz
  rw [← hz, mul_div_cancel_left₀ _ hQz]

theorem exists_rational_weierstrassP {f : ℂ → ℂ} (hf : IsEllipticFunction L f) :
    ∃ P Q R S : ℂ[X], Q ≠ 0 ∧ S ≠ 0 ∧ f =ᶠ[codiscrete ℂ] fun z ↦
      P.eval (℘[L] z) / Q.eval (℘[L] z) + ℘'[L] z * (R.eval (℘[L] z) / S.eval (℘[L] z)) := by
  have hneg : Meromorphic fun z ↦ f (-z) := fun z ↦ by
    have : MeromorphicAt f (-z) := hf.1 (-z)
    exact this.comp_analyticAt (g := fun z ↦ -z) (by fun_prop)
  have hpneg : IsPeriodic L fun z ↦ f (-z) := fun z l hl ↦ by
    simp only [neg_add, ← sub_eq_add_neg]
    exact hf.2.sub (-z) hl
  obtain ⟨P, Q, hQ, h1⟩ := exists_polynomial_div_of_even (L := L)
    (f := fun z ↦ (f z + f (-z)) / 2)
    ⟨fun z ↦ ((hf.1 z).add (hneg z)).div analyticAt_const.meromorphicAt,
      fun z l hl ↦ by simp only [hf.2 z l hl, hpneg z l hl]⟩
    (fun z ↦ by simp only [neg_neg]; ring)
  obtain ⟨R, S, hS, h2⟩ := exists_polynomial_div_of_even (L := L)
    (f := fun z ↦ (f z - f (-z)) / 2 / ℘'[L] z)
    ⟨fun z ↦ (((hf.1 z).sub (hneg z)).div analyticAt_const.meromorphicAt).div
      (L.meromorphic_derivWeierstrassP z),
      fun z l hl ↦ by simp only [hf.2 z l hl, hpneg z l hl, isPeriodic_derivWeierstrassP z l hl]⟩
    (fun z ↦ by simp only [neg_neg, L.derivWeierstrassP_neg]; ring)
  refine ⟨P, Q, R, S, hQ, hS, ?_⟩
  filter_upwards [h1, h2, eventually_codiscrete_derivWeierstrassP_ne_zero (L := L)]
    with z e1 e2 e3
  rw [← e1, ← e2]
  field_simp
  ring

end Elliptic
end GroundTheory.Global
