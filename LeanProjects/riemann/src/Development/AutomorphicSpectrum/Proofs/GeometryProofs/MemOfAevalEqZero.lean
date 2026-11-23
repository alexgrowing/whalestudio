import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsPowSubMemSpanOfIsUnitModOfIsAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace UnitChart

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem homog_zero_deg_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ) := by
  intro m hm k
  have h1 : m = 0 := by
    rw [← C_1, C_apply] at hm
    exact Finset.mem_singleton.mp (support_monomial_subset hm)
  simp [h1]

theorem homog_mul {a b : MRing ι} {da db : K → ℕ} (ha : IsMultiHomog a da) (hb : IsMultiHomog b db) :
    IsMultiHomog (a * b) (da + db) := by
  classical
  intro m hm k
  obtain ⟨x, hx, z, hz, rfl⟩ := Finset.mem_add.mp (support_mul a b hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, ha x hx k, hb z hz k]

theorem homog_add {a b : MRing ι} {d : K → ℕ} (ha : IsMultiHomog a d) (hb : IsMultiHomog b d) :
    IsMultiHomog (a + b) d := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (support_add hm) with h | h
  · exact ha m h k
  · exact hb m h k

theorem homog_sub {a b : MRing ι} {d : K → ℕ} (ha : IsMultiHomog a d) (hb : IsMultiHomog b d) :
    IsMultiHomog (a - b) d := by
  rw [sub_eq_add_neg]
  exact homog_add ha (fun m hm => hb m (by rwa [support_neg] at hm))

theorem homog_C (n : ℤ) : IsMultiHomog (C n : MRing ι) (0 : K → ℕ) := by
  intro m hm k
  rw [C_apply] at hm
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  simp

theorem homog_X [DecidableEq K] (p : Σ k, ι k) : IsMultiHomog (X p : MRing ι) (Pi.single p.1 1) := by
  classical
  rcases p with ⟨k0, i0⟩
  intro m hm k
  rw [X] at hm
  rw [Finset.mem_singleton.mp (support_monomial_subset hm)]
  by_cases hk : k = k0
  · subst hk
    rw [Finset.sum_eq_single i0]
    · simp
    · intro i _ hi
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hi (sigma_mk_injective h).symm
    · simp
  · rw [Pi.single_eq_of_ne hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hk (congrArg Sigma.fst h).symm

def cMon (c : ∀ k, ι k) (m : K → ℕ) : MRing ι := ∏ k, X ⟨k, c k⟩ ^ m k

private theorem homog_pow_lemma {a : MRing ι} {d : K → ℕ} (ha : IsMultiHomog a d) (n : ℕ) :
    IsMultiHomog (a ^ n) (n • d) := by
  induction n with
  | zero => simpa using (homog_zero_deg_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact homog_mul ih ha

private theorem homog_prod_lemma_2 [DecidableEq K] (c : ∀ k, ι k) (m : K → ℕ) (s : Finset K) :
    IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ m k) (∑ k ∈ s, m k • Pi.single k 1) := by
  induction s using Finset.induction_on with
  | empty => simpa using (homog_zero_deg_one : IsMultiHomog (1 : MRing ι) (0 : K → ℕ))
  | insert k s hk ih =>
    rw [Finset.prod_insert hk, Finset.sum_insert hk]
    exact homog_mul (homog_pow_lemma (homog_X ⟨k, c k⟩) (m k)) ih

theorem homog_cMon (c : ∀ k, ι k) (m : K → ℕ) : IsMultiHomog (cMon c m) m := by
  classical
  have h := homog_prod_lemma_2 c m Finset.univ
  have e : (∑ k ∈ Finset.univ, m k • Pi.single k 1 : K → ℕ) = m := by
    ext k'
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e] at h
  exact h

theorem aeval_cMon (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (m : K → ℕ) :
    aeval y (cMon c m) = ∏ k, y ⟨k, c k⟩ ^ m k := by
  simp only [cMon, map_prod, map_pow, aeval_X]

theorem cMon_notMem {W : Ideal (MRing ι)} [hW : W.IsPrime] {c : ∀ k, ι k}
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ W) (m : K → ℕ) : cMon c m ∉ W := by
  intro hm
  have hmem : cMon c m ∈ W.primeCompl :=
    prod_mem fun k _ => pow_mem (Ideal.mem_primeCompl_iff.mpr (hc k)) _
  exact Ideal.mem_primeCompl_iff.mp hmem hm

private theorem prod_X_fst_lemma_3 {m : (Σ k, ι k) →₀ ℕ} {d : K → ℕ} (hm : ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    (m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) = ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
  rw [Finsupp.prod_fintype _ _ (fun p => pow_zero _), Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun k _ => ?_
  dsimp only
  rw [Finset.prod_pow_eq_pow_sum, hm k]

theorem mConeMap_homog (y : (Σ k, ι k) → Ω) {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d) :
    mConeMap y h = MvPolynomial.C (aeval y h) * ∏ k, (X k : MvPolynomial K Ω) ^ d k := by
  classical
  conv_lhs => rw [h.as_sum]
  conv_rhs => rw [h.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [mConeMap, aeval_monomial, aeval_monomial, map_mul, mul_assoc]
  congr 1
  rw [← prod_X_fst_lemma_3 (Ω := Ω) (fun k => hh m hm k)]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]

theorem aeval_scaled (y : (Σ k, ι k) → Ω) (τ : K → Ω) (h : MRing ι) :
    aeval (fun p : Σ k, ι k => y p * τ p.1) h = aeval τ (mConeMap y h) := by
  induction h using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [mConeMap]

theorem aeval_scaled_homog (y : (Σ k, ι k) → Ω) (τ : K → Ω) {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) :
    aeval (fun p : Σ k, ι k => y p * τ p.1) h = aeval y h * ∏ k, τ k ^ d k := by
  rw [aeval_scaled, mConeMap_homog y hh, map_mul, aeval_C, map_prod]
  simp only [map_pow, aeval_X, Algebra.algebraMap_self, RingHom.id_apply]

theorem mem_of_aeval_eq_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d)
    (h0 : aeval y h = 0) : h ∈ mCoordIdeal y := by
  rw [mCoordIdeal, RingHom.mem_ker, mConeMap_homog y hh, h0]
  simp

theorem aeval_ne_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ} (hh : IsMultiHomog h d)
    (hn : h ∉ mCoordIdeal y) : aeval y h ≠ 0 := by
  exact fun h0 => hn (mem_of_aeval_eq_zero hh h0)

theorem chart_form {y : (Σ k, ι k) → Ω} {c : ∀ k, ι k} (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {r : Ω}
    (hr : r ∈ chartRingZ y c) :
    ∃ (m : K → ℕ) (G : MRing ι), IsMultiHomog G m ∧ r * ∏ k, y ⟨k, c k⟩ ^ m k = aeval y G := by
  classical
  induction hr using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    refine ⟨Pi.single p.1 1, X p, homog_X p, ?_⟩
    rw [aeval_X, Finset.prod_eq_single p.1 (fun k _ hk => by rw [Pi.single_eq_of_ne hk, pow_zero])
      (by simp), Pi.single_eq_same, pow_one, div_mul_cancel₀ _ (hc p.1)]
  | algebraMap z =>
    exact ⟨0, C z, homog_C z, by simp⟩
  | add x1 x2 _ _ ih1 ih2 =>
    obtain ⟨m1, G1, hG1, e1⟩ := ih1
    obtain ⟨m2, G2, hG2, e2⟩ := ih2
    refine ⟨m1 + m2, G1 * cMon c m2 + G2 * cMon c m1,
      homog_add (homog_mul hG1 (homog_cMon c m2))
        (by rw [add_comm m1 m2]; exact homog_mul hG2 (homog_cMon c m1)), ?_⟩
    rw [map_add, map_mul, map_mul, aeval_cMon, aeval_cMon, ← e1, ← e2]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring
  | mul x1 x2 _ _ ih1 ih2 =>
    obtain ⟨m1, G1, hG1, e1⟩ := ih1
    obtain ⟨m2, G2, hG2, e2⟩ := ih2
    refine ⟨m1 + m2, G1 * G2, homog_mul hG1 hG2, ?_⟩
    rw [map_mul, ← e1, ← e2]
    simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
    ring

theorem mem_of_local (R : Subalgebra ℤ Ω) (w : Ω)
    (h : ∀ q : Ideal R, q.IsPrime → ∃ a : R, a ∉ q ∧ (a : Ω) * w ∈ R) : w ∈ R := by
  let J : Ideal R :=
    { carrier := {a | (a : Ω) * w ∈ R}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        push_cast
        rw [add_mul]
        exact add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun c a ha => by
        simp only [Set.mem_setOf_eq, smul_eq_mul] at ha ⊢
        push_cast
        rw [mul_assoc]
        exact mul_mem c.2 ha }
  by_contra hw
  have hJ : J ≠ ⊤ := by
    intro hJ
    have h1 : (1 : R) ∈ J := hJ ▸ Submodule.mem_top
    apply hw
    simpa [J] using h1
  obtain ⟨q, hq, hJq⟩ := Ideal.exists_le_maximal J hJ
  obtain ⟨a, ha, haw⟩ := h q hq.isPrime
  exact ha (hJq (show a ∈ J from haw))

theorem zpow_factor {a b : K → ℕ} (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) :
    (∏ k, Y k ^ (-((a k : ℤ) - b k))) * ∏ k, Y k ^ a k = ∏ k, Y k ^ b k := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast (Y k) (b k), ← zpow_add₀ (hY k)]
  congr 1
  ring

theorem zpow_factor_inv {a b : K → ℕ} (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) :
    (∏ k, Y k ^ (-((a k : ℤ) - b k))) * ∏ k, (Y k)⁻¹ ^ b k = ∏ k, (Y k)⁻¹ ^ a k := by
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast (Y k)⁻¹ (a k), inv_zpow', inv_zpow', ← zpow_add₀ (hY k)]
  congr 1
  ring

end UnitChart

open UnitChart in

theorem isUnitSec_iff_chart (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (f g : MRing ι) (df dg : K → ℕ) (_hy : ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0)
    (hf : IsMultiHomog f df) (hg : IsMultiHomog g dg) (hfn : f ∉ mCoordIdeal y) (hgn : g ∉ mCoordIdeal y) :
    IsUnitSec (mCoordIdeal y) f g ↔ ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
      aeval y f / aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k)) ∈ chartRingZ y c ∧
      (aeval y f / aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k)))⁻¹ ∈ chartRingZ y c := by
  classical
  have hA : aeval y f ≠ 0 := aeval_ne_zero hf hfn
  have hB : aeval y g ≠ 0 := aeval_ne_zero hg hgn
  constructor
  · intro hU c hc
    have hE0 : ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hρ0 : aeval y f / aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k)) ≠ 0 :=
      mul_ne_zero (div_ne_zero hA hB) hE0
    let gens : (Σ k, ι k) → chartRingZ y c := fun p =>
      ⟨y p / y ⟨p.1, c p.1⟩, Algebra.subset_adjoin ⟨p, rfl⟩⟩
    have hD : ∀ x : MRing ι, ((aeval gens x : chartRingZ y c) : Ω) =
        aeval (fun p : Σ k, ι k => y p * (y ⟨p.1, c p.1⟩)⁻¹) x := by
      intro x
      exact (comp_aeval_apply (R := ℤ) (S₁ := chartRingZ y c) (f := gens) (chartRingZ y c).val x).trans
        (congrArg (aeval · x) (funext fun p => by simp [gens, div_eq_mul_inv]))
    have hZ : ∀ x ∈ mCoordIdeal y, aeval (fun p : Σ k, ι k => y p * (y ⟨p.1, c p.1⟩)⁻¹) x = 0 := by
      intro x hx
      rw [mCoordIdeal, RingHom.mem_ker] at hx
      have hx' : mConeMap y x = 0 := hx
      exact (aeval_scaled y (fun k => (y ⟨k, c k⟩)⁻¹) x).trans (by rw [hx', map_zero])
    have hW : ∀ q : Ideal (chartRingZ y c), q.IsPrime → ∃ u v : MRing ι, aeval gens u ∉ q ∧
        aeval gens v ∉ q ∧ u * f - v * g ∈ mCoordIdeal y := by
      intro q hq
      have hWp : (Ideal.comap (aeval gens : MRing ι →ₐ[ℤ] chartRingZ y c) q).IsPrime := inferInstance
      have hPW : mCoordIdeal y ≤ Ideal.comap (aeval gens : MRing ι →ₐ[ℤ] chartRingZ y c) q := by
        intro x hx
        rw [Ideal.mem_comap]
        have h0 : aeval gens x = 0 := Subtype.ext ((hD x).trans (hZ x hx))
        rw [h0]
        exact q.zero_mem
      have hrel : IsRelevant (Ideal.comap (aeval gens : MRing ι →ₐ[ℤ] chartRingZ y c) q) := by
        intro k
        refine ⟨c k, fun hX => hq.ne_top ((Ideal.eq_top_iff_one q).mpr ?_)⟩
        rw [Ideal.mem_comap, aeval_X] at hX
        have h1 : gens ⟨k, c k⟩ = 1 := Subtype.ext (div_self (hc k))
        rwa [h1] at hX
      exact hU _ hWp hPW hrel
    have hkey : ∀ u v : MRing ι, u * f - v * g ∈ mCoordIdeal y →
        aeval (fun p : Σ k, ι k => y p * (y ⟨p.1, c p.1⟩)⁻¹) u *
          (aeval y f / aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k))) =
        aeval (fun p : Σ k, ι k => y p * (y ⟨p.1, c p.1⟩)⁻¹) v := by
      intro u v huv
      have h0 := hZ _ huv
      rw [map_sub, map_mul, map_mul, aeval_scaled_homog y (fun k => (y ⟨k, c k⟩)⁻¹) hf,
        aeval_scaled_homog y (fun k => (y ⟨k, c k⟩)⁻¹) hg] at h0
      have h18 := zpow_factor_inv (a := df) (b := dg) (fun k => y ⟨k, c k⟩) hc
      have hTg : ∏ k, (y ⟨k, c k⟩)⁻¹ ^ dg k ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (inv_ne_zero (hc k))
      have hBB : aeval y g / aeval y g = 1 := div_self hB
      apply mul_right_cancel₀ (mul_ne_zero hTg hB)
      linear_combination h0 +
        (aeval (fun p : Σ k, ι k => y p * (y ⟨p.1, c p.1⟩)⁻¹) u * aeval y f) * h18 +
        (aeval (fun p : Σ k, ι k => y p * (y ⟨p.1, c p.1⟩)⁻¹) u * aeval y f *
          (∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k))) * ∏ k, (y ⟨k, c k⟩)⁻¹ ^ dg k) * hBB
    refine ⟨mem_of_local _ _ fun q hq => ?_, mem_of_local _ _ fun q hq => ?_⟩
    · obtain ⟨u, v, hu, hv, huv⟩ := hW q hq
      refine ⟨aeval gens u, hu, ?_⟩
      rw [hD u, hkey u v huv, ← hD v]
      exact (aeval gens v).2
    · obtain ⟨u, v, hu, hv, huv⟩ := hW q hq
      refine ⟨aeval gens v, hv, ?_⟩
      rw [hD v, (mul_inv_eq_iff_eq_mul₀ hρ0).mpr (hkey u v huv).symm, ← hD u]
      exact (aeval gens u).2
  · intro hC W hWp hPW hrel
    have hrel' : ∀ k, ∃ i, (X ⟨k, i⟩ : MRing ι) ∉ W := hrel
    choose c hcW using hrel'
    have hc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 =>
      hcW k (hPW (mem_of_aeval_eq_zero (homog_X ⟨k, c k⟩) (by rw [aeval_X]; exact h0)))
    have hE0 : ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
    have hρ0 : aeval y f / aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k)) ≠ 0 :=
      mul_ne_zero (div_ne_zero hA hB) hE0
    obtain ⟨h1, h2⟩ := hC c hc
    obtain ⟨m, G, hG, eG⟩ := chart_form hc h1
    obtain ⟨m', G', hG', eG'⟩ := chart_form hc h2
    have hGW : G ∉ W := by
      intro hGmem
      apply cMon_notMem (W := W) hcW (m + m')
      have hmem : G * G' - cMon c (m + m') ∈ mCoordIdeal y := by
        apply mem_of_aeval_eq_zero (homog_sub (homog_mul hG hG') (homog_cMon c (m + m')))
        rw [map_sub, map_mul, aeval_cMon, ← eG, ← eG']
        simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
        have hρρ := mul_inv_cancel₀ hρ0
        linear_combination ((∏ k, y ⟨k, c k⟩ ^ m k) * ∏ k, y ⟨k, c k⟩ ^ m' k) * hρρ
      have h3 := W.sub_mem (W.mul_mem_right G' hGmem) (hPW hmem)
      rwa [sub_sub_cancel] at h3
    refine ⟨cMon c (dg + m), G * cMon c df, cMon_notMem hcW _, ?_, ?_⟩
    · intro hv
      rcases hWp.mem_or_mem hv with h | h
      · exact hGW h
      · exact cMon_notMem hcW df h
    · have hd : (dg + m) + df = (m + df) + dg := by abel
      apply mem_of_aeval_eq_zero (homog_sub (homog_mul (homog_cMon c (dg + m)) hf)
        (by rw [hd]; exact homog_mul (homog_mul hG (homog_cMon c df)) hg))
      rw [map_sub, map_mul, map_mul, map_mul, aeval_cMon, aeval_cMon, ← eG]
      have h17 := zpow_factor (a := df) (b := dg) (fun k => y ⟨k, c k⟩) hc
      have hBB : aeval y g / aeval y g = 1 := div_self hB
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      linear_combination (-((∏ k, y ⟨k, c k⟩ ^ m k) * aeval y f)) * h17 -
        (aeval y f * (∏ k, y ⟨k, c k⟩ ^ (-((df k : ℤ) - dg k))) * (∏ k, y ⟨k, c k⟩ ^ m k) *
          ∏ k, y ⟨k, c k⟩ ^ df k) * hBB

end GlobalTheory.CompanionTheory.Ar.Flat
