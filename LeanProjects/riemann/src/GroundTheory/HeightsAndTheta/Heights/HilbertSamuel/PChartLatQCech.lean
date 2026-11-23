import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartLatQCech
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PGenOnFibres
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZeroCocycleSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace ChartLatQCech

set_option linter.unusedSectionVars false

open GenOnFibres ZeroCocycleSection

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def cmq (c : ∀ k, ι k) (e : K → ℕ) : MRingOver ℚ ι :=
  MvPolynomial.map (Int.castRingHom ℚ) (cmon c e)

theorem homog_cmq (c : ∀ k, ι k) (e : K → ℕ) : IsMultiHomog (cmq c e) e :=
  homog_map _ (homog_cmon c e)

theorem cmq_add (c : ∀ k, ι k) (e f : K → ℕ) : cmq c (e + f) = cmq c e * cmq c f := by
  rw [cmq, cmon_add, map_mul]; rfl

theorem cmq_ne_zero (c : ∀ k, ι k) (e : K → ℕ) : cmq c e ≠ 0 := by
  rw [cmq, cmon, map_prod]
  exact Finset.prod_ne_zero_iff.mpr fun k _ => by
    rw [map_pow, map_X]; exact pow_ne_zero _ (X_ne_zero _)

theorem mem_cellMon_chartQ {c : ∀ k, ι k} {t : MRingOver ℚ ι} (ht : t ∈ KH.cellMon ℚ (chartCell c).1) :
    ∃ e : K → ℕ, t = cmq c e := by
  classical
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    have hi' : i = c k := Finset.mem_singleton.mp hi
    subst hi'
    refine ⟨Pi.single k 1, ?_⟩
    rw [cmq, cmon, map_prod]
    rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk']) (fun h => absurd (Finset.mem_univ k) h)]
    simp
  | one => exact ⟨0, by simp [cmq, cmon]⟩
  | mul x x' _ _ hx hx' =>
    obtain ⟨f, rfl⟩ := hx
    obtain ⟨f', rfl⟩ := hx'
    exact ⟨f + f', (cmq_add c f f').symm⟩

section Eval

variable {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}

theorem aeval_cmq (c : ∀ k, ι k) (e : K → ℕ) : aeval y (cmq c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  rw [cmq, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap, aeval_cmon]

theorem aeval_eq_zero_of_memQ {f : MRingOver ℚ ι} (hf : f ∈ idealOver y ℚ) : aeval y f = 0 := by
  have h : idealOver y ℚ ≤ RingHom.ker (aeval y : MRingOver ℚ ι →ₐ[ℚ] Ω) := by
    refine Ideal.map_le_iff_le_comap.mpr fun g hg => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, ← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap,
      aeval_eq_eval_mConeMap y g, RingHom.mem_ker.mp hg, map_zero]
  exact RingHom.mem_ker.mp (h hf)

attribute [local instance] MvPolynomial.algebraMvPolynomial in

theorem mem_idealOverQ {p : MRingOver ℚ ι} {d : K → ℕ} (hp : IsMultiHomog p d) (h0 : aeval y p = 0) :
    p ∈ idealOver y ℚ := by
  obtain ⟨⟨G, ⟨_, n, hn, rfl⟩⟩, hG⟩ :=
    IsLocalization.surj (S := MRingOver ℚ ι) (Submonoid.map (C : ℤ →+* MRing ι) (nonZeroDivisors ℤ)) p
  change p * MvPolynomial.map (algebraMap ℤ ℚ) (C n) = MvPolynomial.map (algebraMap ℤ ℚ) G at hG
  rw [map_C, algebraMap_int_eq, eq_intCast] at hG
  have hG' : (n : ℚ) • p = MvPolynomial.map (Int.castRingHom ℚ) G := by
    rw [← hG, mul_comm, C_mul']
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hn
  have hGh : IsMultiHomog G d := by
    intro m hm
    apply hp m
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    have h1 := congrArg (MvPolynomial.coeff m) hG'
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_smul] at h1
    intro h2
    rw [h2, smul_zero] at h1
    exact hm (by simpa using h1.symm)
  have hG0 : aeval y G = 0 := by
    have h1 := congrArg (aeval y) hG'
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap, map_smul, h0, smul_zero] at h1
    exact h1.symm
  have hmem := mem_idealOver (S := ℚ) hGh hG0
  rw [← hG] at hmem
  have e : p = p * C (n : ℚ) * C ((n : ℚ)⁻¹) := by
    rw [mul_assoc, ← C_mul, mul_inv_cancel₀ hn0, C_1, mul_one]
  rw [e]
  exact Ideal.mul_mem_right _ _ hmem

variable (y) in

def evQ : (MRingOver ℚ ι ⧸ idealOver y ℚ) →ₐ[ℚ] Ω :=
  Ideal.Quotient.liftₐ (idealOver y ℚ) (aeval y) fun _ ha => aeval_eq_zero_of_memQ ha

theorem evQ_mk (p : MRingOver ℚ ι) : evQ y (Ideal.Quotient.mk _ p) = aeval y p := rfl

theorem evQ_smul (r : MRingOver ℚ ι) (m : MRingOver ℚ ι ⧸ idealOver y ℚ) :
    evQ y (r • m) = aeval y r * evQ y m := by
  rw [smul_quot, map_mul, evQ_mk]

theorem cellMon_aevalQ_ne {I : ∀ k, Finset (ι k)} (hI : ∀ k, ∀ i ∈ I k, y ⟨k, i⟩ ≠ 0) :
    ∀ t ∈ KH.cellMon ℚ I, aeval y t ≠ 0 := by
  intro t ht
  induction ht using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨k, i, hi, rfl⟩ := hx
    rw [aeval_X]
    exact hI k i hi
  | one => simp
  | mul x x' _ _ hx hx' => rw [map_mul]; exact mul_ne_zero hx hx'

variable (y) in
open Classical in

def val (T : Submonoid (MRingOver ℚ ι)) (x : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ)) : Ω :=
  if hT : ∀ t ∈ T, aeval y t ≠ 0 then
    x.liftOn (fun p => evQ y p.1 / aeval y (p.2 : MRingOver ℚ ι)) (by
      rintro ⟨m, s⟩ ⟨m', s'⟩ ⟨u, hu⟩
      have h := congrArg (evQ y) hu
      simp only [Submonoid.smul_def, evQ_smul] at h
      have hu0 := hT _ u.2
      have hs := hT _ s.2
      have hs' := hT _ s'.2
      dsimp only
      rw [div_eq_div_iff hs hs']
      have h' := mul_left_cancel₀ hu0 h
      linear_combination h')
  else 0

theorem val_mk {T : Submonoid (MRingOver ℚ ι)} (hT : ∀ t ∈ T, aeval y t ≠ 0) (m : MRingOver ℚ ι ⧸ idealOver y ℚ)
    (t : T) : val y T (LocalizedModule.mk m t) = evQ y m / aeval y (t : MRingOver ℚ ι) := by
  rw [val, dif_pos hT]
  rfl

theorem val_add (T : Submonoid (MRingOver ℚ ι)) (x x' : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ)) :
    val y T (x + x') = val y T x + val y T x' := by
  by_cases hT : ∀ t ∈ T, aeval y t ≠ 0
  · induction x using LocalizedModule.induction_on with
    | h m s =>
      induction x' using LocalizedModule.induction_on with
      | h m' s' =>
        rw [LocalizedModule.mk_add_mk, val_mk hT, val_mk hT, val_mk hT]
        simp only [Submonoid.coe_mul, map_add, Submonoid.smul_def, evQ_smul, map_mul]
        have hs := hT _ s.2
        have hs' := hT _ s'.2
        field_simp
  · simp only [val, dif_neg hT, add_zero]

theorem val_smul (T : Submonoid (MRingOver ℚ ι)) (r : ℚ)
    (x : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ)) : val y T (r • x) = r • val y T x := by
  by_cases hT : ∀ t ∈ T, aeval y t ≠ 0
  · induction x using LocalizedModule.induction_on with
    | h m s =>
      rw [LocalizedModule.smul'_mk, val_mk hT, val_mk hT, map_smul, smul_div_assoc]
  · simp only [val, dif_neg hT, smul_zero]

variable (y) in

def valL (T : Submonoid (MRingOver ℚ ι)) : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ) →ₗ[ℚ] Ω where
  toFun := val y T
  map_add' := val_add T
  map_smul' := fun r x => val_smul T r x

theorem liftOfLE_mk {T T' : Submonoid (MRingOver ℚ ι)} (h : T ≤ T')
    (m : MRingOver ℚ ι ⧸ idealOver y ℚ) (s : T) :
    LocalizedModule.liftOfLE T T' h (LocalizedModule.mk m s) = LocalizedModule.mk m (⟨s.1, h s.2⟩ : T') := by
  rw [IsLocalizedModule.mk_eq_mk', IsLocalizedModule.liftOfLE_mk', ← IsLocalizedModule.mk_eq_mk']

theorem val_liftOfLE {T T' : Submonoid (MRingOver ℚ ι)} (h : T ≤ T') (hT' : ∀ t ∈ T', aeval y t ≠ 0)
    (x : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ)) :
    val y T' (LocalizedModule.liftOfLE T T' h x) = val y T x := by
  have hT : ∀ t ∈ T, aeval y t ≠ 0 := fun t ht => hT' t (h ht)
  induction x using LocalizedModule.induction_on with
  | h m s =>
    rw [liftOfLE_mk, val_mk hT', val_mk hT]

theorem locPart_liftOfLE {T T' : Submonoid (MRingOver ℚ ι)} (h : T ≤ T') {b : K → ℤ}
    {x : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) T b) :
    LocalizedModule.liftOfLE T T' h x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) T' b := by
  obtain ⟨m, t, β, ht, hm, rfl⟩ := locPart_eq_mk hx
  rw [liftOfLE_mk]
  exact Submodule.subset_span ⟨m, ⟨t, h t.2⟩, β, ht, hm, rfl⟩

theorem eq_zero_of_val {T : Submonoid (MRingOver ℚ ι)} (hT : ∀ t ∈ T, aeval y t ≠ 0) {b : K → ℤ}
    {x : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) T b) (h0 : val y T x = 0) : x = 0 := by
  obtain ⟨m, t, β, -, hm, rfl⟩ := locPart_eq_mk hx
  by_cases hm0 : m = 0
  · rw [hm0, LocalizedModule.zero_mk]
  · exfalso
    obtain ⟨-, p, hp, rfl⟩ := quotPart_eq_mk hm hm0
    rw [val_mk hT, evQ_mk, div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hm0 (Ideal.Quotient.eq_zero_iff_mem.mpr (mem_idealOverQ hp h0))
    · exact hT _ t.2 h0

theorem eq_of_val_eq {T : Submonoid (MRingOver ℚ ι)} (hT : ∀ t ∈ T, aeval y t ≠ 0) {b : K → ℤ}
    {x x' : LocalizedModule T (MRingOver ℚ ι ⧸ idealOver y ℚ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) T b)
    (hx' : x' ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) T b) (h : val y T x = val y T x') : x = x' := by
  refine sub_eq_zero.mp (eq_zero_of_val hT (sub_mem hx hx') ?_)
  show valL y T (x - x') = 0
  rw [map_sub]
  exact sub_eq_zero.mpr h

end Eval

section Chart

variable {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}

theorem aeval_div_memQ (c : ∀ k, ι k) {g : MRingOver ℚ ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    aeval y g / ∏ k, y ⟨k, c k⟩ ^ d k ∈ chartRingQ y c := by
  classical
  rw [g.as_sum, map_sum, Finset.sum_div]
  refine Subalgebra.sum_mem _ fun m hm => ?_
  rw [aeval_monomial, mul_div_assoc]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) ?_
  have key : m.prod (fun p e => y p ^ e) / ∏ k, y ⟨k, c k⟩ ^ d k = ∏ p, (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    rw [Finsupp.prod_fintype _ _ (by simp)]
    simp only [div_pow]
    rw [Finset.prod_div_distrib]
    congr 1
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  rw [key]
  exact Subalgebra.prod_mem _ fun p _ => Subalgebra.pow_mem _
    (Algebra.subset_adjoin (Set.mem_range_self (f := fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) p)) _

theorem exists_formQ (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {r : Ω} (hr : r ∈ chartRingQ y c) :
    ∃ (e : K → ℕ) (F : MRingOver ℚ ι), IsMultiHomog F e ∧ aeval y F = r * ∏ k, y ⟨k, c k⟩ ^ e k := by
  classical
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨⟨k, i⟩, rfl⟩ := hx
    refine ⟨Pi.single k 1, X ⟨k, i⟩, homog_X k i, ?_⟩
    have hprod : ∏ k', y ⟨k', c k'⟩ ^ (Pi.single k 1 : K → ℕ) k' = y ⟨k, c k⟩ := by
      rw [Finset.prod_eq_single k (fun k' _ hk' => by simp [hk'])
        (fun h => absurd (Finset.mem_univ k) h)]
      simp
    rw [hprod, aeval_X]
    field_simp [hc k]
  | algebraMap q =>
    exact ⟨0, C q, homog_C q, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨e1, F1, hF1, hv1⟩ := hx
    obtain ⟨e2, F2, hF2, hv2⟩ := hz
    refine ⟨e1 + e2, F1 * cmq c e2 + F2 * cmq c e1, ?_, ?_⟩
    · refine homog_add (homog_mul hF1 (homog_cmq c e2)) ?_
      rw [add_comm e1 e2]
      exact homog_mul hF2 (homog_cmq c e1)
    · rw [map_add, map_mul, map_mul, hv1, hv2, aeval_cmq, aeval_cmq, prod_pow_add]
      ring
  | mul x z _ _ hx hz =>
    obtain ⟨e1, F1, hF1, hv1⟩ := hx
    obtain ⟨e2, F2, hF2, hv2⟩ := hz
    refine ⟨e1 + e2, F1 * F2, homog_mul hF1 hF2, ?_⟩
    rw [map_mul, hv1, hv2, prod_pow_add]
    ring

theorem exists_fracQ (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {s : Ω} (b : K → ℤ)
    (hs : s * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ chartRingQ y c) :
    ∃ (e d : K → ℕ) (F : MRingOver ℚ ι), IsMultiHomog F d ∧ (∀ k, (d k : ℤ) = e k + b k) ∧
      aeval y F = s * ∏ k, y ⟨k, c k⟩ ^ e k := by
  obtain ⟨e, F, hF, hv⟩ := exists_formQ c hc hs
  refine ⟨e + fun k => (-b k).toNat, e + fun k => (b k).toNat, F * cmq c (fun k => (b k).toNat),
    homog_mul hF (homog_cmq c _), fun k => ?_, ?_⟩
  · simp only [Pi.add_apply, Nat.cast_add]
    omega
  · rw [map_mul, hv, aeval_cmq, prod_pow_add]
    have hk : ∀ k, y ⟨k, c k⟩ ^ (-b k) * y ⟨k, c k⟩ ^ (b k).toNat = y ⟨k, c k⟩ ^ (-b k).toNat := by
      intro k
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
      congr 1
      omega
    calc s * (∏ k, y ⟨k, c k⟩ ^ (-b k)) * (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, y ⟨k, c k⟩ ^ (b k).toNat
        = s * (∏ k, y ⟨k, c k⟩ ^ e k) * ∏ k, (y ⟨k, c k⟩ ^ (-b k) * y ⟨k, c k⟩ ^ (b k).toNat) := by
          rw [Finset.prod_mul_distrib]; ring
      _ = _ := by simp only [hk]; ring

theorem exists_rep {T : Submonoid (MRingOver ℚ ι)} (hT : ∀ t ∈ T, aeval y t ≠ 0) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hcT : ∀ e, cmq c e ∈ T) {s : Ω} {b : K → ℤ}
    (hs : s * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ chartRingQ y c) :
    ∃ x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) T b, val y T x = s := by
  obtain ⟨e, d, F, hF, hd, hv⟩ := exists_fracQ c hc b hs
  refine ⟨LocalizedModule.mk (Ideal.Quotient.mk _ F) ⟨_, hcT e⟩, ?_, ?_⟩
  · refine Submodule.subset_span ⟨_, ⟨_, hcT e⟩, e, homog_cmq c e, ?_, rfl⟩
    refine Submodule.subset_span ⟨F, ⟨fun k => ?_, ?_⟩, rfl⟩
    · have := hd k
      simp only [Pi.add_apply]
      omega
    · have hd' : (fun k => ((b + fun k => (e k : ℤ)) k).toNat) = d := funext fun k => by
        have := hd k
        simp only [Pi.add_apply]
        omega
      rw [hd']
      exact hF
  · rw [val_mk hT, evQ_mk, hv]
    show s * _ / aeval y (cmq c e) = s
    rw [aeval_cmq]
    have : ∏ k, y ⟨k, c k⟩ ^ e k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    field_simp

theorem val_mul_mem_chartRingQ {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {b : K → ℤ}
    {x : LocalizedModule (KH.cellMon ℚ (chartCell c).1) (MRingOver ℚ ι ⧸ idealOver y ℚ)}
    (hx : x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) (KH.cellMon ℚ (chartCell c).1) b) :
    val y _ x * ∏ k, y ⟨k, c k⟩ ^ (-b k) ∈ chartRingQ y c := by
  have hT := cellMon_aevalQ_ne (y := y) (chartCell_good hc)
  obtain ⟨m, t, β, ht, hm, rfl⟩ := locPart_eq_mk hx
  by_cases hm0 : m = 0
  · rw [hm0, val_mk hT, map_zero, zero_div, zero_mul]
    exact zero_mem _
  · obtain ⟨hnn, p, hp, rfl⟩ := quotPart_eq_mk hm hm0
    obtain ⟨e, he⟩ := mem_cellMon_chartQ t.2
    have hβ : β = e := by
      obtain ⟨μ, hμ⟩ : (cmq c e).support.Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr (mt MvPolynomial.support_eq_empty.mp (cmq_ne_zero c e))
      rw [he] at ht
      exact funext fun k => (ht μ hμ k).symm.trans (homog_cmq c e μ hμ k)
    subst hβ
    rw [val_mk hT, evQ_mk, he, aeval_cmq]
    have hprod : ∏ k, y ⟨k, c k⟩ ^ ((b + fun k => (β k : ℤ)) k).toNat =
        (∏ k, y ⟨k, c k⟩ ^ β k) * ∏ k, y ⟨k, c k⟩ ^ b k := by
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hc k)]
      congr 1
      have := hnn k
      simp only [Pi.add_apply] at this ⊢
      omega
    have h1 : ∏ k, y ⟨k, c k⟩ ^ β k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
    have h2 : ∏ k, y ⟨k, c k⟩ ^ b k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have key : aeval y p / (∏ k, y ⟨k, c k⟩ ^ β k) * ∏ k, y ⟨k, c k⟩ ^ (-b k) =
        aeval y p / ∏ k, y ⟨k, c k⟩ ^ ((b + fun k => (β k : ℤ)) k).toNat := by
      rw [hprod]
      simp only [zpow_neg, Finset.prod_inv_distrib]
      field_simp
    rw [key]
    exact aeval_div_memQ c hp

end Chart

section Cocycle

variable [LinearOrder K] [∀ k, LinearOrder (ι k)]

theorem resFacesS {S : Type} [CommRing S] {M : Type} [AddCommGroup M] [Module (MRingOver S ι) M] (z : KH.CechC S ι M 0)
    (hz : KH.cechD S ι M 0 z = 0) (I : KH.Cell K ι 1) (k0 : K) (i1 i2 : ι k0) (hlt : i1 < i2)
    (hI : I.1 k0 = {i1, i2}) (hrest : ∀ k ≠ k0, (I.1 k).card = 1) (J1 J2 : KH.Cell K ι 0)
    (hJ1 : J1.1 = Function.update I.1 k0 ((I.1 k0).erase i1))
    (hJ2 : J2.1 = Function.update I.1 k0 ((I.1 k0).erase i2)) :
    KH.cellRes S M J1.1 I.1 (z J1) = KH.cellRes S M J2.1 I.1 (z J2) := by
  have hne : ∀ k, (I.1 k).Nonempty := I.2.1
  have h2 : (I.1 k0).card = 2 := by rw [hI]; exact Finset.card_pair (ne_of_lt hlt)
  have hface : ∀ i ∈ I.1 k0, (∀ l, (Function.update I.1 k0 ((I.1 k0).erase i) l).Nonempty) ∧
      ∑ l, ((Function.update I.1 k0 ((I.1 k0).erase i) l).card - 1) = 0 := by
    intro i hi
    have hc : ((I.1 k0).erase i).card = 1 := by rw [Finset.card_erase_of_mem hi, h2]
    refine ⟨fun l => ?_, Finset.sum_eq_zero fun l _ => ?_⟩
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self]
        exact Finset.card_pos.mp (by omega)
      · rw [Function.update_of_ne hl]
        exact hne l
    · by_cases hl : l = k0
      · subst hl
        rw [Function.update_self, hc]
        rfl
      · rw [Function.update_of_ne hl, hrest l hl]
        rfl
  have hsumsign : ∑ l ∈ Finset.univ.filter (· < k0), ((I.1 l).card - 1) = 0 :=
    Finset.sum_eq_zero fun l hl => by rw [hrest l (ne_of_lt (Finset.mem_filter.mp hl).2)]; rfl
  have hs1 : KH.faceSign I.1 k0 i1 = 1 := by
    have f1 : (({i1, i2} : Finset (ι k0)).filter (· < i1)).card = 0 := by
      simp [Finset.filter_insert, Finset.filter_singleton, not_lt.mpr hlt.le]
    simp only [KH.faceSign, hsumsign, hI, add_zero, f1]
    norm_num
  have hs2 : KH.faceSign I.1 k0 i2 = -1 := by
    have f2 : (({i1, i2} : Finset (ι k0)).filter (· < i2)).card = 1 := by
      simp [Finset.filter_insert, Finset.filter_singleton, hlt]
    simp only [KH.faceSign, hsumsign, hI, add_zero, f2]
    norm_num
  have hi1 : i1 ∈ I.1 k0 := by rw [hI]; simp
  have hi2 : i2 ∈ I.1 k0 := by rw [hI]; simp
  have key : KH.cechD S ι M 0 z I =
      KH.faceSign I.1 k0 i1 • KH.cellRes S M (Function.update I.1 k0 ((I.1 k0).erase i1)) I.1
        (z ⟨_, hface i1 hi1⟩) + KH.faceSign I.1 k0 i2 • KH.cellRes S M
        (Function.update I.1 k0 ((I.1 k0).erase i2)) I.1 (z ⟨_, hface i2 hi2⟩) := by
    rw [KH.cechD]
    erw [LinearMap.pi_apply]
    simp only [LinearMap.sum_apply]
    rw [Finset.sum_eq_single k0]
    · rw [Finset.sum_eq_add_of_mem i1 i2 hi1 hi2 (ne_of_lt hlt)]
      · rw [dif_pos (hface i1 hi1), dif_pos (hface i2 hi2)]
        rfl
      · intro i hi hne'
        rw [hI] at hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exact absurd rfl hne'.1
        · exact absurd rfl hne'.2
    · intro k _ hk
      refine Finset.sum_eq_zero fun i hi => ?_
      split_ifs with hc
      · exfalso
        obtain ⟨hn, -⟩ := hc
        have h3 := hn k
        rw [Function.update_self] at h3
        have h4 := Finset.card_erase_of_mem hi
        rw [hrest k hk] at h4
        have h5 := Finset.card_pos.mpr h3
        omega
      · rfl
    · intro h
      exact absurd (Finset.mem_univ k0) h
  have e0 : KH.cechD S ι M 0 z I = 0 := by rw [hz]; rfl
  rw [key, hs1, hs2, one_smul, neg_one_smul, ← sub_eq_add_neg, sub_eq_zero] at e0
  obtain ⟨A1, hA1⟩ := J1
  obtain ⟨A2, hA2⟩ := J2
  simp only at hJ1 hJ2
  subst hJ1 hJ2
  exact e0

variable {Ω : Type} [Field Ω] [CharZero Ω] {y : (Σ k, ι k) → Ω}
variable {v : KH.CechC ℚ ι (MRingOver ℚ ι ⧸ idealOver y ℚ) 0}

theorem val_step_lt (hz : KH.cechD ℚ ι _ 0 v = 0) {c d : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) (k0 : K) (hcd : ∀ k ≠ k0, c k = d k)
    (hlt : c k0 < d k0) :
    val y _ (v (chartCell c)) = val y _ (v (chartCell d)) := by
  classical
  have hne : c k0 ≠ d k0 := ne_of_lt hlt
  set A : ∀ k, Finset (ι k) := Function.update (fun k => ({c k} : Finset (ι k))) k0 {c k0, d k0} with hAdef
  have hA0 : A k0 = {c k0, d k0} := Function.update_self _ _ _
  have hAk : ∀ k ≠ k0, A k = {c k} := fun k hk => Function.update_of_ne hk _ _
  have hAne : ∀ k, (A k).Nonempty := by
    intro k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      exact Finset.insert_nonempty _ _
    · rw [hAk k hk]
      exact Finset.singleton_nonempty _
  have hAsum : ∑ k, ((A k).card - 1) = 1 := by
    rw [Finset.sum_eq_single k0 (fun k _ hk => by rw [hAk k hk]; rfl)
      (fun h => absurd (Finset.mem_univ k0) h), hA0, Finset.card_pair hne]
  have hIy : ∀ k, ∀ i ∈ A k, y ⟨k, i⟩ ≠ 0 := by
    intro k i hi
    by_cases hk : k = k0
    · subst hk
      rw [hA0] at hi
      rcases Finset.mem_insert.mp hi with h | h
      · rw [h]; exact hc _
      · rw [Finset.mem_singleton.mp h]; exact hd _
    · rw [hAk k hk, Finset.mem_singleton] at hi
      rw [hi]
      exact hc k
  have hrest : ∀ k ≠ k0, (A k).card = 1 := fun k hk => by rw [hAk k hk]; rfl
  have hsc : ∀ k, (chartCell c).1 k ⊆ A k := by
    intro k
    show {c k} ⊆ A k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      simp
    · rw [hAk k hk]
  have hsd : ∀ k, (chartCell d).1 k ⊆ A k := by
    intro k
    show {d k} ⊆ A k
    by_cases hk : k = k0
    · subst hk
      rw [hA0]
      simp
    · rw [hAk k hk, hcd k hk]
  have e := resFacesS v hz ⟨A, hAne, hAsum⟩ k0 (c k0) (d k0) hlt hA0 hrest (chartCell d) (chartCell c) ?_ ?_
  · rw [cellRes_of_le (cellMon_mono hsd), cellRes_of_le (cellMon_mono hsc)] at e
    have hA := cellMon_aevalQ_ne (y := y) hIy
    rw [← val_liftOfLE (cellMon_mono hsc) hA, ← val_liftOfLE (cellMon_mono hsd) hA, e]
  · funext k
    by_cases hk : k = k0
    · subst hk
      show ({d k} : Finset (ι k)) = Function.update A k ((A k).erase (c k)) k
      rw [Function.update_self, hA0, Finset.erase_insert (by simpa using hne)]
    · show ({d k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (c k0)) k
      rw [Function.update_of_ne hk, hAk k hk, hcd k hk]
  · funext k
    by_cases hk : k = k0
    · subst hk
      show ({c k} : Finset (ι k)) = Function.update A k ((A k).erase (d k)) k
      rw [Function.update_self, hA0, Finset.pair_comm, Finset.erase_insert (by simpa using hne.symm)]
    · show ({c k} : Finset (ι k)) = Function.update A k0 ((A k0).erase (d k0)) k
      rw [Function.update_of_ne hk, hAk k hk]

theorem val_step (hz : KH.cechD ℚ ι _ 0 v = 0) {c d : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) (k0 : K) (hcd : ∀ k ≠ k0, c k = d k) :
    val y _ (v (chartCell c)) = val y _ (v (chartCell d)) := by
  rcases lt_trichotomy (c k0) (d k0) with h | h | h
  · exact val_step_lt hz hc hd k0 hcd h
  · have e : c = d := funext fun k => by
      by_cases hk : k = k0
      · subst hk; exact h
      · exact hcd k hk
    subst e
    rfl
  · exact (val_step_lt hz hd hc k0 (fun k hk => (hcd k hk).symm) h).symm

theorem val_chart_eq (hz : KH.cechD ℚ ι _ 0 v = 0) {c d : ∀ k, ι k}
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (hd : ∀ k, y ⟨k, d k⟩ ≠ 0) :
    val y _ (v (chartCell c)) = val y _ (v (chartCell d)) := by
  classical
  have hmix : ∀ (U : Finset K) k, y ⟨k, (fun k => if k ∈ U then d k else c k) k⟩ ≠ 0 := by
    intro U k
    dsimp only
    split_ifs
    exacts [hd k, hc k]
  have key : ∀ U : Finset K, val y _ (v (chartCell c)) =
      val y _ (v (chartCell fun k => if k ∈ U then d k else c k)) := by
    intro U
    induction U using Finset.induction_on with
    | empty =>
      have e0 : (fun k => if k ∈ (∅ : Finset K) then d k else c k) = c := funext fun k => by simp
      rw [e0]
    | insert k0 U hk0 ih =>
      rw [ih]
      exact val_step hz (hmix U) (hmix (insert k0 U)) k0 (fun k hk => by simp [Finset.mem_insert, hk])
  have e1 : (fun k => if k ∈ (Finset.univ : Finset K) then d k else c k) = d := funext fun k => by simp
  have h := key Finset.univ
  rw [e1] at h
  exact h

end Cocycle

theorem cell_good {Ω : Type} [Field Ω] {y : (Σ k, ι k) → Ω} (J : KH.Cell K ι 0)
    (hJ : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0) : ∀ k, ∀ i ∈ J.1 k, y ⟨k, i⟩ ≠ 0 := by
  intro k i hi
  have eJ := eq_chartCell (cellChart_mem J)
  rw [eJ] at hi
  rw [Finset.mem_singleton.mp hi]
  exact hJ k

end ChartLatQCech

open ChartLatQCech GenOnFibres ZeroCocycleSection in

theorem ChartLatQCech.proof : ChartLatQCech.Statement := by
  intro K _ _ ι _ _ Ω _ _ y d b hA
  classical
  obtain ⟨c0, hc0⟩ : ∃ c0 : ∀ k, ι k, ∀ k, y ⟨k, c0 k⟩ ≠ 0 := by
    choose c0 hc0 using hA.2.1.2.2
    refine ⟨c0, fun k h => hc0 k ?_⟩
    show mConeMap y (X ⟨k, c0 k⟩) = 0
    simp [mConeMap, h]
  have hZ : ∀ v ∈ KH.cechZc ι (KH.quotPart ℚ (idealOver y ℚ)) b 0,
      (∀ J : KH.Cell K ι 0, v J ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) (KH.cellMon ℚ J.1) b) ∧
        KH.cechD ℚ ι _ 0 v = 0 := fun v hv =>
    ⟨fun J => (Submodule.mem_inf.mp hv).1 J (Set.mem_univ _), (Submodule.mem_inf.mp hv).2⟩
  let Ψ : ↥(KH.cechZc ι (KH.quotPart ℚ (idealOver y ℚ)) b 0) →ₗ[ℚ] Ω :=
    { toFun := fun v => val y _ (v.1 (chartCell c0))
      map_add' := fun v w => val_add _ _ _
      map_smul' := fun r v => val_smul _ r _ }
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    rw [LinearMap.mem_ker] at hv
    obtain ⟨hloc, hz⟩ := hZ v.1 v.2
    refine Subtype.ext (funext fun J => ?_)
    by_cases hJ : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0
    · have eJ := eq_chartCell (cellChart_mem J)
      have h1 : val y _ (v.1 (chartCell (cellChart J))) = 0 := by
        rw [← val_chart_eq hz hc0 hJ]
        exact hv
      have h2 := eq_zero_of_val (cellMon_aevalQ_ne (chartCell_good hJ)) (hloc _) h1
      rw [← eJ] at h2
      exact h2
    · push Not at hJ
      obtain ⟨k, h0⟩ := hJ
      have := subsingleton_loc (S := ℚ) (y := y) (cellChart_mem J k) h0
      exact Subsingleton.elim _ _
  have hrange : LinearMap.range Ψ = chartLatQ y b 1 := by
    ext s
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨hloc, hz⟩ := hZ v.1 v.2
      intro c hc
      have h := val_mul_mem_chartRingQ hc (hloc (chartCell c))
      show val y _ (v.1 (chartCell c0)) * _ ∈ chartRingQ y c
      rw [val_chart_eq hz hc0 hc]
      simp only [Nat.cast_one, one_mul]
      exact h
    · intro hs
      have hex : ∀ J : KH.Cell K ι 0, (∀ k, y ⟨k, cellChart J k⟩ ≠ 0) →
          ∃ x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) (KH.cellMon ℚ J.1) b, val y _ x = s := by
        intro J hJ
        have h := hs (cellChart J) hJ
        simp only [Nat.cast_one, one_mul] at h
        exact exists_rep (cellMon_aevalQ_ne (cell_good J hJ)) (cellChart J) hJ
          (fun e => cmon_mem ℚ (cellChart_mem J) e) h
      let w : KH.CechC ℚ ι (MRingOver ℚ ι ⧸ idealOver y ℚ) 0 := fun J =>
        if h : ∃ x ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) (KH.cellMon ℚ J.1) b, val y _ x = s then
          h.choose else 0
      have hw : ∀ J, w J ∈ KH.locPart ι (KH.quotPart ℚ (idealOver y ℚ)) (KH.cellMon ℚ J.1) b := by
        intro J
        simp only [w]
        split_ifs with h
        exacts [h.choose_spec.1, zero_mem _]
      have hwv : ∀ J : KH.Cell K ι 0, (∀ k, y ⟨k, cellChart J k⟩ ≠ 0) → val y _ (w J) = s := by
        intro J hJ
        simp only [w]
        rw [dif_pos (hex J hJ)]
        exact (hex J hJ).choose_spec.2
      have hwZ : w ∈ KH.cechZc ι (KH.quotPart ℚ (idealOver y ℚ)) b 0 := by
        refine Submodule.mem_inf.mpr ⟨fun J _ => hw J, ?_⟩
        rw [Submodule.restrictScalars_mem, LinearMap.mem_ker]
        funext I
        refine cechD_zero_eq_zero _ I fun J J' hJ hJ' => ?_
        by_cases hbad : ∃ k, ∃ i ∈ I.1 k, y ⟨k, i⟩ = 0
        · obtain ⟨k, i, hi, h0⟩ := hbad
          have := subsingleton_loc (S := ℚ) (y := y) hi h0
          exact Subsingleton.elim _ _
        · push Not at hbad
          have hI := cellMon_aevalQ_ne hbad
          have hJc : ∀ k, y ⟨k, cellChart J k⟩ ≠ 0 := fun k => hbad k _ (hJ k (cellChart_mem J k))
          have hJc' : ∀ k, y ⟨k, cellChart J' k⟩ ≠ 0 := fun k => hbad k _ (hJ' k (cellChart_mem J' k))
          rw [cellRes_of_le (cellMon_mono hJ), cellRes_of_le (cellMon_mono hJ')]
          refine eq_of_val_eq hI (locPart_liftOfLE _ (hw J)) (locPart_liftOfLE _ (hw J')) ?_
          rw [val_liftOfLE _ hI, val_liftOfLE _ hI, hwv J hJc, hwv J' hJc']
      refine ⟨⟨w, hwZ⟩, ?_⟩
      show val y _ (w (chartCell c0)) = s
      refine hwv _ fun k => ?_
      rw [Finset.mem_singleton.mp (cellChart_mem (chartCell c0) k)]
      exact hc0 k
  have e0 : KH.cechHc ι (KH.quotPart ℚ (idealOver y ℚ)) b 0 ≃ₗ[ℚ]
      ↥(KH.cechZc ι (KH.quotPart ℚ (idealOver y ℚ)) b 0) :=
    Submodule.quotEquivOfEqBot _ (by
      rw [show KH.cechBc ι (KH.quotPart ℚ (idealOver y ℚ)) b 0 = ⊥ from rfl, Submodule.comap_bot,
        Submodule.ker_subtype])
  exact ⟨(LinearEquiv.ofEq _ _ hrange).symm.trans ((LinearEquiv.ofInjective Ψ hinj).symm.trans e0.symm)⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
