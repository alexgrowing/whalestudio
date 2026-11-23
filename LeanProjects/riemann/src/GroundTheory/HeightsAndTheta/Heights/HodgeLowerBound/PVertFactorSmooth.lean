import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsVertFactorSmooth
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

namespace VertFactorSmooth

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem aeval_eq_eval_map (z : (Σ k, ι k) → ℂ) (g : MRing ι) :
    aeval z g = eval z (map (Int.castRingHom ℂ) g) := by
  rw [eval_map, aeval_def, algebraMap_int_eq]

theorem contDiff_evalMap (t : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) t)) := by
  induction t using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ ℂ v)

def mdeg (d : (Σ k, ι k) →₀ ℕ) : K →₀ ℕ := Finsupp.mapDomain Sigma.fst d

theorem mdeg_apply (d : (Σ k, ι k) →₀ ℕ) (k : K) : mdeg d k = ∑ i, d ⟨k, i⟩ := by
  classical
  unfold mdeg
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_sigma,
    Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [hk']
  · simp

theorem isMultiHomog_iff (g : MRing ι) (d : K →₀ ℕ) :
    IsMultiHomog g ⇑d ↔ ∀ e ∈ g.support, mdeg e = d :=
  ⟨fun h e he => Finsupp.ext fun k => by rw [mdeg_apply]; exact h e he k,
    fun h e he k => by rw [← mdeg_apply, h e he]⟩

section Cone

variable {Ω : Type} [Field Ω]

theorem mConeMap_monomial (y : (Σ k, ι k) → Ω) (e : (Σ k, ι k) →₀ ℕ) (a : ℤ) :
    mConeMap y (monomial e a) = monomial (mdeg e) ((a : Ω) * e.prod fun p n => y p ^ n) := by
  classical
  have hX : (e.prod fun p n => (X p.1 : MvPolynomial K Ω) ^ n) = monomial (mdeg e) 1 := by
    have h := rename_monomial (R := Ω) (Sigma.fst : (Σ k, ι k) → K) e 1
    rw [monomial_eq, C_1, one_mul, map_finsuppProd] at h
    simpa [rename_X, mdeg] using h
  simp only [mConeMap, aeval_monomial, mul_pow, Finsupp.prod_mul, ← map_pow, ← map_finsuppProd, hX]
  rw [show ((algebraMap ℤ (MvPolynomial K Ω)) a) = C (a : Ω) by simp, ← mul_assoc, ← map_mul, C_mul_monomial,
    mul_one]

theorem mConeMap_eq_sum (y : (Σ k, ι k) → Ω) (u : MRing ι) :
    mConeMap y u = ∑ e ∈ u.support, monomial (mdeg e) (((coeff e u : ℤ) : Ω) * e.prod fun p n => y p ^ n) := by
  conv_lhs => rw [u.as_sum]
  rw [map_sum]
  simp only [mConeMap_monomial]

open Classical in

def comp (u : MRing ι) (m : K →₀ ℕ) : MRing ι :=
  ∑ e ∈ u.support.filter (fun e => mdeg e = m), monomial e (coeff e u)

theorem coeff_comp (u : MRing ι) (m : K →₀ ℕ) (e : (Σ k, ι k) →₀ ℕ) :
    coeff e (comp u m) = if mdeg e = m then coeff e u else 0 := by
  classical
  rw [comp, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_filter, mem_support_iff]
  split_ifs <;> simp_all

theorem isMultiHomog_comp (u : MRing ι) (m : K →₀ ℕ) : IsMultiHomog (comp u m) ⇑m := by
  rw [isMultiHomog_iff]
  intro e he
  rw [mem_support_iff, coeff_comp] at he
  by_contra h
  exact he (if_neg h)

theorem aeval_comp (y : (Σ k, ι k) → Ω) (u : MRing ι) (m : K →₀ ℕ) :
    aeval y (comp u m) = coeff m (mConeMap y u) := by
  classical
  rw [mConeMap_eq_sum, coeff_sum, comp, map_sum]
  simp only [coeff_monomial, aeval_monomial, algebraMap_int_eq, eq_intCast]
  rw [← Finset.sum_filter]

theorem mConeMap_of_homog (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K →₀ ℕ} (hg : IsMultiHomog g ⇑d) :
    mConeMap y g = monomial d (aeval y g) := by
  classical
  rw [isMultiHomog_iff] at hg
  rw [mConeMap_eq_sum]
  conv_rhs => rw [g.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun e he => ?_
  rw [hg e he, aeval_monomial, algebraMap_int_eq, eq_intCast]

end Cone

theorem isMultiHomog_X_pow [DecidableEq K] (q : Σ k, ι k) (n : ℕ) : IsMultiHomog (X q ^ n : MRing ι) (Pi.single q.1 n) := by
  classical
  intro m hm k
  rw [support_X_pow, Finset.mem_singleton] at hm
  subst hm
  obtain ⟨k0, i0⟩ := q
  by_cases hk : k0 = k
  · subst hk
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  · simp [Ne.symm hk]

theorem isMultiHomog_prod_X_pow (c : (k : K) → ι k) (e : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k) e := by
  classical
  have h : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ e k)
      (∑ k ∈ s, Pi.single k (e k)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isMultiHomog_one (ι := ι)
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact isMultiHomog_mul (isMultiHomog_X_pow _ _) ih
  simpa [Finset.univ_sum_single] using h Finset.univ

theorem eval_torusSmul {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) :
    eval (torusSmul c z) (map (Int.castRingHom ℂ) g) =
      (∏ k, c k ^ d k) * eval z (map (Int.castRingHom ℂ) g) := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum,
    support_map_of_injective _ (Int.castRingHom ℂ).injective_int]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg := hg m hm
  have hc : ∏ p : Σ k, ι k, c p.1 ^ m p = ∏ k, c k ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, c k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hdeg k]
  simp only [torusSmul, mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem torusSmul_mem_mcPts {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) : torusSmul c z ∈ mcPts P := by
  obtain ⟨S, hS, hPS⟩ := hP
  refine ⟨fun k => ?_, fun g hg => ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, mul_ne_zero (hc k) hi⟩
  · have hle : Ideal.span S ≤ RingHom.ker ((eval (torusSmul c z)).comp (map (Int.castRingHom ℂ))) := by
      rw [Ideal.span_le]
      intro s hs
      obtain ⟨a, ha⟩ := hS s hs
      rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, eval_torusSmul ha,
        hz.2 s (hPS ▸ Ideal.subset_span hs), mul_zero]
    rw [hPS] at hg
    have := hle hg
    rwa [RingHom.mem_ker, RingHom.comp_apply] at this

section Component

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {Ω : Type} [Field Ω] [Algebra ℚ Ω]
  {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)] [∀ τ, Module Ω (E τ)]

theorem exists_forms (D : ComponentData II Ψ K ι Ω E) {p : ℕ} (hp : p ∈ D.S)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal D.y)) :
    ∃ (dG dH : K → ℕ) (G H : MRing ι), IsMultiHomog G dG ∧ IsMultiHomog H dH ∧
      (fun k => (dG k : ℤ) - dH k) = D.vdeg p ∧
      aeval D.y G * aeval D.y (D.vden p) = aeval D.y (D.vnum p) * aeval D.y H ∧
      eval z (map (Int.castRingHom ℂ) H) ≠ 0 := by
  classical
  have hV := D.vertical p hp
  obtain ⟨bf, bg, hf, hg, hb⟩ := hV.degrees
  have hPW : mCoordIdeal D.y ≤ mCoordIdeal z := by
    obtain ⟨S, hS, hPS⟩ := D.arith.2.1.2.1
    rw [hPS, Ideal.span_le]
    intro s hs
    obtain ⟨a, ha⟩ := hS s hs
    have hsP : s ∈ mCoordIdeal D.y := hPS ▸ Ideal.subset_span hs
    have h0 : aeval z s = 0 := by rw [aeval_eq_eval_map]; exact hz.2 s hsP
    show mConeMap z s = 0
    rw [mConeMap_of_isMultiHomog z ha, h0, map_zero, zero_mul]
  have hWprime : (mCoordIdeal z).IsPrime := RingHom.ker_isPrime _
  have hrel : IsRelevant (mCoordIdeal z) := by
    intro k
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun h => hi ?_⟩
    have h' : mConeMap z (X ⟨k, i⟩) = 0 := h
    simpa [mConeMap, X_ne_zero] using h'
  have hpW : (C (p : ℤ) : MRing ι) ∉ mCoordIdeal z := by
    intro h
    have h' : mConeMap z (C (p : ℤ)) = 0 := h
    simp [mConeMap] at h'
    exact (D.S_prime p hp).ne_zero h'
  obtain ⟨u, v, hu, -, huv⟩ := hV.unit_off_fibre _ hWprime hPW hrel hpW
  have hu' : mConeMap z u ≠ 0 := fun h => hu h
  obtain ⟨m, hm⟩ := ne_zero_iff.1 hu'
  set bf' : K →₀ ℕ := Finsupp.equivFunOnFinite.symm bf with hbf'
  set bg' : K →₀ ℕ := Finsupp.equivFunOnFinite.symm bg with hbg'
  have hf' : IsMultiHomog (D.vnum p) ⇑bf' := by simpa [bf'] using hf
  have hg' : IsMultiHomog (D.vden p) ⇑bg' := by simpa [bg'] using hg
  have key : coeff (m + bf') (mConeMap D.y (u * D.vnum p - v * D.vden p)) = 0 := by
    have h0 : mConeMap D.y (u * D.vnum p - v * D.vden p) = 0 := huv
    rw [h0, coeff_zero]
  rw [map_sub, map_mul, map_mul, mConeMap_of_homog _ hf', mConeMap_of_homog _ hg', coeff_sub,
    coeff_mul_monomial, coeff_mul_monomial'] at key
  have hfy : aeval D.y (D.vnum p) ≠ 0 := fun h => hV.num_not_mem (mem_mCoordIdeal_of_aeval_eq_zero _ hf h)
  have hHz : eval z (map (Int.castRingHom ℂ) (comp u m)) ≠ 0 := by
    rwa [← aeval_eq_eval_map, aeval_comp]
  split_ifs at key with hle
  · refine ⟨⇑(m + bf' - bg'), ⇑m, comp v (m + bf' - bg'), comp u m, isMultiHomog_comp _ _,
      isMultiHomog_comp _ _, ?_, ?_, hHz⟩
    · funext k
      rw [← hb]
      have := hle k
      simp only [bf', bg', Finsupp.coe_tsub, Finsupp.coe_add, Pi.sub_apply, Pi.add_apply,
        Finsupp.coe_equivFunOnFinite_symm] at this ⊢
      omega
    · rw [aeval_comp, aeval_comp]
      linear_combination -key
  · exfalso
    rw [sub_zero] at key
    have h0 : aeval D.y (comp u m) = 0 := by
      rw [aeval_comp]
      exact (mul_eq_zero.1 key).resolve_right hfy
    exact hHz (eval_eq_zero_of_mem_mcPts hz (mem_mCoordIdeal_of_aeval_eq_zero _ (isMultiHomog_comp u m) h0))

theorem vertFactor_eq (D : ComponentData II Ψ K ι Ω E) {p : ℕ} (hp : p ∈ D.S) {w : (Σ k, ι k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal D.y)) {dG dH : K → ℕ} {G H : MRing ι} (hG : IsMultiHomog G dG)
    (hH : IsMultiHomog H dH) (hdeg : (fun k => (dG k : ℤ) - dH k) = D.vdeg p)
    (hrel : aeval D.y G * aeval D.y (D.vden p) = aeval D.y (D.vnum p) * aeval D.y H)
    (hHw : eval w (map (Int.castRingHom ℂ) H) ≠ 0) :
    D.vertFactor p w = ‖eval w (map (Int.castRingHom ℂ) G) / eval w (map (Int.castRingHom ℂ) H)‖ := by
  classical
  have hc : ∃ c : (k : K) → ι k, ∀ k, w ⟨k, c k⟩ ≠ 0 :=
    ⟨fun k => (hw.1 k).choose, fun k => (hw.1 k).choose_spec⟩
  rw [ComponentData.vertFactor, dif_pos hc]
  have hwc : ∀ k, w ⟨k, hc.choose k⟩ ≠ 0 := hc.choose_spec
  generalize hc.choose = c at hwc ⊢
  set b := D.vdeg p with hbdef
  obtain ⟨bf, bg, hf, hg, -⟩ := (D.vertical p hp).degrees
  set Mn : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (-b k).toNat with hMn
  set Mp : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ (b k).toNat with hMp
  have hyc : ∀ k, D.y ⟨k, c k⟩ ≠ 0 := by
    intro k h
    apply hwc k
    have hX := isMultiHomog_X_pow (ι := ι) ⟨k, c k⟩ 1
    rw [pow_one] at hX
    have := eval_eq_zero_of_mem_mcPts hw (mem_mCoordIdeal_of_aeval_eq_zero D.y hX (by simpa using h))
    simpa using this
  have hHy : aeval D.y H ≠ 0 := fun h =>
    hHw (eval_eq_zero_of_mem_mcPts hw (mem_mCoordIdeal_of_aeval_eq_zero D.y hH h))
  have hgy : aeval D.y (D.vden p) ≠ 0 := fun h =>
    (D.vertical p hp).den_not_mem (mem_mCoordIdeal_of_aeval_eq_zero D.y hg h)
  have hGy : aeval D.y G = aeval D.y (D.vnum p) * aeval D.y H / aeval D.y (D.vden p) := by
    rw [eq_div_iff hgy, hrel]
  have hmono : aeval D.y Mn = chartMono D.y c (-b) * aeval D.y Mp := by
    simp only [hMn, hMp, chartMono, map_prod, map_pow, aeval_X, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, Pi.neg_apply, ← zpow_add₀ (hyc k)]
    congr 1
    omega
  have hZ : eval w (map (Int.castRingHom ℂ) Mn) * zMono w c b = eval w (map (Int.castRingHom ℂ) Mp) := by
    simp only [hMn, hMp, zMono, map_prod, map_pow, map_X, eval_X, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hwc k)]
    congr 1
    omega
  have hMpw : eval w (map (Int.castRingHom ℂ) Mp) ≠ 0 := by
    simp only [hMp, map_prod, map_pow, map_X, eval_X]
    exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hwc k)
  have hval : IsValueAt D.y (aeval D.y (D.vnum p) / aeval D.y (D.vden p) * chartMono D.y c (-b)) w
      (eval w (map (Int.castRingHom ℂ) (G * Mn)) / eval w (map (Int.castRingHom ℂ) (H * Mp))) := by
    refine ⟨dG + fun k => (-b k).toNat, G * Mn, H * Mp, isMultiHomog_mul hG (isMultiHomog_prod_X_pow c _),
      ?_, ?_, ?_, ?_, rfl⟩
    · have h := isMultiHomog_mul hH (isMultiHomog_prod_X_pow c fun k => (b k).toNat)
      convert h using 1
      funext k
      have := congrFun hdeg k
      simp only [Pi.add_apply] at this ⊢
      omega
    · rw [map_mul]
      refine mul_ne_zero hHy ?_
      simp only [hMp, map_prod, map_pow, aeval_X]
      exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
    · rw [map_mul, map_mul, hmono, hGy]
      ring
    · rw [map_mul, map_mul]
      exact mul_ne_zero hHw hMpw
  rw [valAt_eq hw hval, ← norm_mul]
  congr 1
  rw [map_mul, map_mul, map_mul, map_mul, div_mul_eq_mul_div, mul_assoc, hZ, mul_div_mul_right _ _ hMpw]

end Component

end VertFactorSmooth

open VertFactorSmooth in

theorem VertFactorSmooth.proof (hPos : VertFactorPos.Statement) : VertFactorSmooth.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D p hp
  refine ⟨fun z hz c hc => ?_, fun z hz => ?_⟩
  · obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := exists_forms D hp hz
    have hcz := torusSmul_mem_mcPts D.arith.2.1.2.1 hz hc
    have hprod : ∀ d : K → ℕ, ∏ k, c k ^ d k ≠ 0 := fun d =>
      Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hc k)
    rw [vertFactor_eq D hp hcz hG hH hdeg hrel (by rw [eval_torusSmul hH]; exact mul_ne_zero (hprod _) hHz),
      vertFactor_eq D hp hz hG hH hdeg hrel hHz, eval_torusSmul hG, eval_torusSmul hH, ← hdeg,
      mul_div_mul_comm, norm_mul, norm_div, norm_prod, norm_prod, ← Finset.prod_div_distrib]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, norm_pow, zpow_sub₀ (norm_ne_zero_iff.2 (hc k)), zpow_natCast, zpow_natCast]
  · obtain ⟨dG, dH, G, H, hG, hH, hdeg, hrel, hHz⟩ := exists_forms D hp hz
    have hpos := hPos II Ψ K ι Ω E D p hp z hz
    rw [vertFactor_eq D hp hz hG hH hdeg hrel hHz] at hpos
    have hGz : eval z (map (Int.castRingHom ℂ) G) ≠ 0 := by
      intro h
      rw [h, zero_div, norm_zero] at hpos
      exact lt_irrefl _ hpos
    have hcG := contDiff_evalMap G
    have hcH := contDiff_evalMap H
    refine ⟨{w | eval w (map (Int.castRingHom ℂ) H) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G) ≠ 0}, ?_,
      fun w => ‖eval w (map (Int.castRingHom ℂ) G) / eval w (map (Int.castRingHom ℂ) H)‖, ?_, ?_⟩
    · refine IsOpen.mem_nhds ?_ ⟨hHz, hGz⟩
      exact (isOpen_ne_fun hcH.continuous continuous_const).inter (isOpen_ne_fun hcG.continuous continuous_const)
    · intro w hw
      have hd : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun w => eval w (map (Int.castRingHom ℂ) G) * (eval w (map (Int.castRingHom ℂ) H))⁻¹) w :=
        hcG.contDiffAt.mul (hcH.contDiffAt.inv hw.1)
      simp only [← div_eq_mul_inv] at hd
      exact (hd.norm ℝ (div_ne_zero hw.2 hw.1)).contDiffWithinAt
    · rintro w ⟨hw, hwS⟩
      exact vertFactor_eq D hp hwS hG hH hdeg hrel hw.1

end GroundTheory.Heights₂.Heights.LowerBoundFree
