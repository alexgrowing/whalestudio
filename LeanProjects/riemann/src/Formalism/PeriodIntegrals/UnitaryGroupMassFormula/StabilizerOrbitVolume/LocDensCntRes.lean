import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.UnifVSpec

noncomputable section

namespace PI.VolStabSW

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Res

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev iO (a : 𝓞 F) : Fv F v := algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)

theorem vcoe (x : F) : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem lt_one_iff_le_expm1 (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · constructor
    · intro _
      exact zero_le'
    · intro _
      exact zero_lt_one
  · rw [← WithZero.exp_log hg, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem v_iO_le (a : 𝓞 F) : Valued.v (iO v a) ≤ 1 := by
  show Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) ≤ 1
  rw [vcoe]
  exact v.valuation_le_one a

theorem v_iO_lt_iff (a : 𝓞 F) : Valued.v (iO v a) < 1 ↔ a ∈ v.asIdeal := by
  show Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) < 1 ↔ _
  rw [vcoe]
  exact v.valuation_lt_one_iff_mem a

private theorem appr_unit_lemma (m c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ a : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c -
      algebraMap (𝓞 F) F a) < 1 := by
  obtain ⟨c', hc'⟩ : ∃ c' : 𝓞 F, c * c' - 1 ∈ v.asIdeal := by
    haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI := Ideal.Quotient.field v.asIdeal
    have hne : Ideal.Quotient.mk v.asIdeal c ≠ 0 := by
      rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨c', hc'⟩ := Ideal.Quotient.mk_surjective (I := v.asIdeal) (Ideal.Quotient.mk v.asIdeal c)⁻¹
    refine ⟨c', ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hc', mul_inv_cancel₀ hne, map_one, sub_self]
  refine ⟨m * c', ?_⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc v.asIdeal.zero_mem
  have hcF : algebraMap (𝓞 F) F c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc0
  have hvc : v.valuation F (algebraMap (𝓞 F) F c) = 1 :=
    le_antisymm (v.valuation_le_one c) (not_lt.mp fun h => hc ((v.valuation_lt_one_iff_mem c).mp h))
  have heq : algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c - algebraMap (𝓞 F) F (m * c') =
      algebraMap (𝓞 F) F m * algebraMap (𝓞 F) F (1 - c * c') / algebraMap (𝓞 F) F c := by
    rw [map_mul, map_sub, map_one, map_mul]
    first
      | (field_simp; ring)
      | field_simp
  have h1 : v.valuation F (algebraMap (𝓞 F) F (1 - c * c')) < 1 := by
    rw [v.valuation_lt_one_iff_mem]
    have h2 : 1 - c * c' = -(c * c' - 1) := by ring
    rw [h2]
    exact v.asIdeal.neg_mem hc'
  have hm1 := v.valuation_le_one (K := F) m
  rw [heq, map_div₀, hvc, div_one, map_mul]
  calc v.valuation F (algebraMap (𝓞 F) F m) * v.valuation F (algebraMap (𝓞 F) F (1 - c * c'))
      ≤ 1 * v.valuation F (algebraMap (𝓞 F) F (1 - c * c')) := by gcongr
    _ < 1 := by rw [one_mul]; exact h1

private theorem appr_den_lemma_2 (k : F) (hk : v.valuation F k ≤ 1) :
    ∃ m c : 𝓞 F, c ∉ v.asIdeal ∧ k = algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c := by
  obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) k
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdF : algebraMap (𝓞 F) F d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hd0
  have hB : ∀ r : 𝓞 F, v.valuation F (algebraMap (𝓞 F) F r) = v.intValuation r := by
    intro r
    first
      | exact HeightOneSpectrum.valuation_of_algebraMap v r
      | exact v.valuation_of_algebraMap r
      | simp
  have hιd0 : v.intValuation d ≠ 0 := by
    rw [← hB]
    exact (Valuation.ne_zero_iff _).mpr hdF
  have hιd1 : v.intValuation d ≤ 1 := by
    rw [← hB]
    exact v.valuation_le_one d
  have hLe : WithZero.exp (WithZero.log (v.intValuation d)) = v.intValuation d := WithZero.exp_log hιd0
  have hL0 : WithZero.log (v.intValuation d) ≤ 0 := by
    have h := hιd1
    rw [← hLe, ← WithZero.exp_zero, WithZero.exp_le_exp] at h
    exact h
  obtain ⟨e, he⟩ : ∃ e : ℕ, (e : ℤ) = -WithZero.log (v.intValuation d) :=
    ⟨(-WithZero.log (v.intValuation d)).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hιd : v.intValuation d = WithZero.exp (-(e : ℤ)) := by
    rw [he, neg_neg, hLe]
  have hdiv : v.asIdeal ^ e ∣ Ideal.span {d} :=
    (HeightOneSpectrum.intValuation_le_pow_iff_dvd v d e).mp (le_of_eq hιd)
  have hndiv : ¬ v.asIdeal ^ (e + 1) ∣ Ideal.span {d} := by
    intro h
    have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_dvd v d (e + 1)).mpr h
    rw [hιd, WithZero.exp_le_exp] at h2
    push_cast at h2
    omega
  obtain ⟨J, hJ⟩ := hdiv
  have hJP : ¬ J ≤ v.asIdeal := by
    intro h
    apply hndiv
    rw [hJ, pow_succ]
    exact mul_dvd_mul_left _ (Ideal.dvd_iff_le.mpr h)
  obtain ⟨c, hcJ, hcP⟩ := SetLike.not_le_iff_exists.mp hJP
  have hn : n ∈ v.asIdeal ^ e := by
    have hιn : v.intValuation n ≤ v.intValuation d := by
      have h := hk
      rw [map_div₀, hB, hB] at h
      calc v.intValuation n = v.intValuation n / v.intValuation d * v.intValuation d := by
            rw [div_mul_cancel₀ _ hιd0]
        _ ≤ 1 * v.intValuation d := by gcongr
        _ = v.intValuation d := one_mul _
    rw [hιd] at hιn
    exact Ideal.dvd_span_singleton.mp ((HeightOneSpectrum.intValuation_le_pow_iff_dvd v n e).mp hιn)
  have hcn : c * n ∈ Ideal.span {d} := by
    rw [hJ, mul_comm c n]
    exact Ideal.mul_mem_mul hn hcJ
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton'.mp hcn
  refine ⟨m, c, hcP, ?_⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hcP v.asIdeal.zero_mem
  have hcF : algebraMap (𝓞 F) F c ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).mpr hc0
  rw [div_eq_div_iff hdF hcF, ← map_mul, ← map_mul, mul_comm n c, ← hm]

theorem exists_appr {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hx1 : Valued.v x ≤ 1 := hx
  have hnhds : {y : Fv F v | Valued.v (y - x) < 1} ∈ 𝓝 x :=
    Valued.mem_nhds.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, k, rfl⟩ :=
    mem_closure_iff_nhds.mp (HeightOneSpectrum.denseRange_algebraMap F v x) _ hnhds
  have hy' : Valued.v (x - algebraMap F (Fv F v) k) < 1 := by
    have h := hy
    rwa [Set.mem_setOf_eq, ← neg_sub, Valuation.map_neg] at h
  have hk1 : Valued.v (algebraMap F (Fv F v) k) ≤ 1 := by
    have h := Valuation.map_add_le Valued.v (le_of_lt hy) hx1
    rwa [sub_add_cancel] at h
  rw [vcoe] at hk1
  obtain ⟨m, c, hc, rfl⟩ := appr_den_lemma_2 v k hk1
  obtain ⟨a, ha⟩ := appr_unit_lemma v m c hc
  refine ⟨a, ?_⟩
  have h2 : Valued.v (algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c) - iO v a) < 1 := by
    show Valued.v (algebraMap F (Fv F v) _ - algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)) < 1
    rw [← map_sub, vcoe]
    exact ha
  have h3 : x - iO v a = (x - algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c)) +
      (algebraMap F (Fv F v) (algebraMap (𝓞 F) F m / algebraMap (𝓞 F) F c) - iO v a) := by
    ring
  rw [h3]
  exact Valuation.map_add_lt Valued.v hy' h2

open Classical in

def appr (x : Fv F v) : 𝓞 F :=
  if h : ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 then h.choose else 0

theorem appr_spec {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  rw [appr, dif_pos h]
  exact h.choose_spec

def red (x : Fv F v) : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk _ (appr v x)

theorem red_eq_mk_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  rw [red, Ideal.Quotient.eq, ← v_iO_lt_iff]
  have h1 := appr_spec v hx
  have e1 : iO v (appr v x - a) = (x - iO v a) + -(x - iO v (appr v x)) := by
    simp only [iO, map_sub]
    ring
  have e2 : x - iO v a = (x - iO v (appr v x)) + iO v (appr v x - a) := by
    simp only [iO, map_sub]
    ring
  constructor
  · intro h
    rw [e2]
    exact Valuation.map_add_lt _ h1 h
  · intro h
    rw [e1]
    refine Valuation.map_add_lt _ h ?_
    rw [Valuation.map_neg]
    exact h1

theorem mem_O_iO (a : 𝓞 F) : iO v a ∈ v.adicCompletionIntegers F := v_iO_le v a

theorem red_iO (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := (red_eq_mk_iff v (mem_O_iO v a) a).mpr (by simp)

theorem red_add {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have hxy : x + y ∈ v.adicCompletionIntegers F := add_mem hx hy
  rw [show red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) by simp only [red, map_add]]
  rw [red_eq_mk_iff v hxy]
  have e : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add]
    ring
  rw [e]
  exact Valuation.map_add_lt _ (appr_spec v hx) (appr_spec v hy)

theorem red_mul {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have hxy : x * y ∈ v.adicCompletionIntegers F := mul_mem hx hy
  rw [show red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) by simp only [red, map_mul]]
  rw [red_eq_mk_iff v hxy]
  have e : x * y - iO v (appr v x * appr v y) =
      (x - iO v (appr v x)) * y + iO v (appr v x) * (y - iO v (appr v y)) := by
    simp only [iO, map_mul]
    ring
  rw [e]
  have hy1 : Valued.v y ≤ 1 := hy
  apply Valuation.map_add_lt
  · rw [Valuation.map_mul]
    calc _ ≤ Valued.v (x - iO v (appr v x)) * 1 := by gcongr
      _ < 1 := by
        rw [mul_one]
        exact appr_spec v hx
  · rw [Valuation.map_mul]
    calc _ ≤ 1 * Valued.v (y - iO v (appr v y)) := by
          have h2 := v_iO_le v (appr v x)
          gcongr
      _ < 1 := by
        rw [one_mul]
        exact appr_spec v hy

theorem red_one : red v 1 = 1 := by
  have h : (1 : Fv F v) = iO v 1 := by simp [iO]
  rw [h, red_iO, map_one]

theorem red_eq_zero_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    red v x = 0 ↔ Valued.v x < 1 := by
  rw [← map_zero (Ideal.Quotient.mk v.asIdeal), red_eq_mk_iff v hx 0]
  simp [iO]

theorem red_zero : red v 0 = 0 := (red_eq_zero_iff v (zero_mem _)).mpr (by simp)

theorem red_neg {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : red v (-x) = -red v x := by
  have h := red_add v hx (neg_mem hx)
  rw [add_neg_cancel, red_zero] at h
  linear_combination (-1 : 𝓞 F ⧸ v.asIdeal) * h

theorem red_surj (t : 𝓞 F ⧸ v.asIdeal) : ∃ x ∈ v.adicCompletionIntegers F, red v x = t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨iO v a, mem_O_iO v a, red_iO v a⟩

theorem lt_one_iff_unif (x : Fv F v) :
    Valued.v x < 1 ↔ Valued.v ((unifV v)⁻¹ * x) ≤ 1 := by
  have hπ : Valued.v (unifV v) = WithZero.exp (-1 : ℤ) := by
    have h := vcoe v (v.valuation_exists_uniformizer F).choose
    rw [(v.valuation_exists_uniformizer F).choose_spec] at h
    exact h
  rw [Valuation.map_mul, map_inv₀, hπ, lt_one_iff_le_expm1,
    inv_mul_le_iff₀ (zero_lt_iff.mpr WithZero.exp_ne_zero), mul_one]

theorem ev_int (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).2

theorem ev_unit {x : F} (hx : x ≠ 0) : ∀ᶠ v in cofinite,
    Valued.v (algebraMap F (Fv F v) x) = 1 := by
  filter_upwards [ev_int x, ev_int x⁻¹] with w h1 h2
  have h1' : Valued.v (algebraMap F (Fv F w) x) ≤ 1 := h1
  have h2' : Valued.v (algebraMap F (Fv F w) x⁻¹) ≤ 1 := h2
  have hm : Valued.v (algebraMap F (Fv F w) x) * Valued.v (algebraMap F (Fv F w) x⁻¹) = 1 := by
    rw [← Valuation.map_mul, ← map_mul, mul_inv_cancel₀ hx, map_one, Valuation.map_one]
  refine le_antisymm h1' ?_
  by_contra hlt
  push_neg at hlt
  have h3 : Valued.v (algebraMap F (Fv F w) x) * Valued.v (algebraMap F (Fv F w) x⁻¹) ≤
      Valued.v (algebraMap F (Fv F w) x) * 1 := by gcongr
  rw [hm, mul_one] at h3
  exact absurd h3 (not_le.mpr hlt)

end Res

section Count

theorem measure_count {G V : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup V] [Finite V] (μ : Measure G) [μ.IsAddLeftInvariant] (L N : AddSubgroup G)
    (hNL : N ≤ L) (hN : MeasurableSet (N : Set G)) (φ : G → V)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, φ (x + y) = φ x + φ y) (hker : ∀ x ∈ L, φ x = 0 ↔ x ∈ N)
    (hsurj : ∀ w, ∃ x ∈ L, φ x = w) (S : Set V) :
    μ {x | x ∈ L ∧ φ x ∈ S} = (Nat.card S : ENNReal) * μ N := by
  classical
  haveI := Fintype.ofFinite V
  choose x hxL hxφ using hsurj
  have key : ∀ w y, -x w + y ∈ N → φ y = w := by
    intro w y hn
    have h1 := hadd _ (hxL w) _ (hNL hn)
    rw [add_neg_cancel_left, hxφ, (hker _ (hNL hn)).mpr hn, add_zero] at h1
    exact h1
  have hset : {y | y ∈ L ∧ φ y ∈ S} = ⋃ w ∈ S.toFinset, (fun h => -x w + h) ⁻¹' (N : Set G) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_toFinset, exists_prop, Set.mem_preimage,
      SetLike.mem_coe]
    constructor
    · rintro ⟨hy, hyS⟩
      refine ⟨φ y, hyS, ?_⟩
      have hmem : -x (φ y) + y ∈ L := L.add_mem (L.neg_mem (hxL _)) hy
      rw [← hker _ hmem]
      have h1 := hadd _ (hxL (φ y)) _ hmem
      rw [add_neg_cancel_left, hxφ] at h1
      calc φ (-x (φ y) + y) = -φ y + (φ y + φ (-x (φ y) + y)) := by abel
        _ = -φ y + φ y := by rw [← h1]
        _ = 0 := by abel
    · rintro ⟨w, hw, hn⟩
      have hyL : y ∈ L := by
        have h2 := L.add_mem (hxL w) (hNL hn)
        rwa [add_neg_cancel_left] at h2
      refine ⟨hyL, ?_⟩
      rw [key w y hn]
      exact hw
  rw [hset, MeasureTheory.measure_biUnion_finset]
  · simp only [MeasureTheory.measure_preimage_add]
    rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_toFinset]
  · intro w1 _ w2 _ hne
    exact Set.disjoint_left.mpr fun y h1 h2 => hne ((key w1 y h1).symm.trans (key w2 y h2))
  · intro w _
    exact (measurable_const_add (-x w)) hN

end Count

end PI.VolStabSW
