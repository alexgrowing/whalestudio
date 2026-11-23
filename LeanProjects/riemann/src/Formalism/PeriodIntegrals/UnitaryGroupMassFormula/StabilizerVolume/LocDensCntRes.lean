import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.UnifVSpec

noncomputable section

namespace PI.VolStabS

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Res

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev iO (a : 𝓞 F) : Fv F v := algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)

theorem vcoe (x : F) : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x

theorem lt_one_iff_le_expm1 (g : WithZero (Multiplicative ℤ)) : g < 1 ↔ g ≤ WithZero.exp (-1 : ℤ) := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rw [← WithZero.exp_log hg, ← WithZero.exp_zero, WithZero.exp_lt_exp, WithZero.exp_le_exp]
    omega

theorem v_iO_le (a : 𝓞 F) : Valued.v (iO v a) ≤ 1 := by
  rw [vcoe]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v a

theorem v_iO_lt_iff (a : 𝓞 F) : Valued.v (iO v a) < 1 ↔ a ∈ v.asIdeal := by
  rw [vcoe]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v a

theorem exists_appr {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hx1 : Valued.v x ≤ 1 := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hx
  have hd := IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) F v
  have hnhds : {y : Fv F v | Valued.v (y - x) < 1} ∈ 𝓝 x :=
    Valued.mem_nhds.mpr ⟨1, fun y hy => by simpa using hy⟩
  obtain ⟨_, hy, k, rfl⟩ := mem_closure_iff_nhds.mp (hd x) _ hnhds
  simp only [Set.mem_setOf_eq] at hy
  have hk' : Valued.v (algebraMap F (Fv F v) k) ≤ 1 := by
    have e : algebraMap F (Fv F v) k = (algebraMap F (Fv F v) k - x) + x := by ring
    rw [e]
    exact le_trans (Valuation.map_add _ _ _) (max_le hy.le hx1)
  have hk : v.valuation F k ≤ 1 := by rw [← vcoe]; exact hk'
  obtain ⟨a, ha⟩ := IsDedekindDomain.HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hk 1
  refine ⟨a, ?_⟩
  have e : x - iO v a = (x - algebraMap F (Fv F v) k) + -(iO v a - algebraMap F (Fv F v) k) := by ring
  have e2 : iO v a - algebraMap F (Fv F v) k = algebraMap F (Fv F v) (algebraMap (𝓞 F) F a - k) := by
    simp [iO, map_sub]
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
  · rw [Valuation.map_sub_swap]
    exact hy
  · rw [Valuation.map_neg, e2, vcoe]
    simpa using ha

open Classical in

def appr (x : Fv F v) : 𝓞 F :=
  if h : ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 then h.choose else 0

theorem appr_spec {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  unfold appr
  rw [dif_pos h]
  exact h.choose_spec

def red (x : Fv F v) : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk _ (appr v x)

theorem red_eq_mk_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  have hs := appr_spec v hx
  unfold red
  rw [Ideal.Quotient.eq, ← v_iO_lt_iff]
  have e : iO v (appr v x - a) = (x - iO v a) - (x - iO v (appr v x)) := by
    simp only [iO, map_sub]
    ring
  rw [e]
  constructor
  · intro h
    have e2 : x - iO v a = (x - iO v (appr v x)) + ((x - iO v a) - (x - iO v (appr v x))) := by ring
    rw [e2]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt hs h)
  · intro h
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h hs)

theorem mem_O_iO (a : 𝓞 F) : iO v a ∈ v.adicCompletionIntegers F := by
  exact (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mpr (v_iO_le v a)

theorem red_iO (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := by
  refine (red_eq_mk_iff v (mem_O_iO v a) a).mpr ?_
  rw [sub_self, map_zero]
  exact zero_lt_one

theorem red_add {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have hxy : x + y ∈ v.adicCompletionIntegers F := add_mem hx hy
  have e1 : red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) := by
    simp only [red, map_add]
  rw [e1, red_eq_mk_iff v hxy]
  have e : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add]
    ring
  rw [e]
  exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt (appr_spec v hx) (appr_spec v hy))

theorem red_mul {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have hxy : x * y ∈ v.adicCompletionIntegers F := mul_mem hx hy
  have e1 : red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) := by
    simp only [red, map_mul]
  rw [e1, red_eq_mk_iff v hxy]
  have e : x * y - iO v (appr v x * appr v y) =
      (x - iO v (appr v x)) * y + iO v (appr v x) * (y - iO v (appr v y)) := by
    simp only [iO, map_mul]
    ring
  rw [e]
  have hy1 : Valued.v y ≤ 1 := (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F v).mp hy
  have ha1 : Valued.v (iO v (appr v x)) ≤ 1 := v_iO_le v _
  apply lt_of_le_of_lt (Valuation.map_add _ _ _)
  apply max_lt
  · rw [map_mul]
    calc Valued.v (x - iO v (appr v x)) * Valued.v y ≤ Valued.v (x - iO v (appr v x)) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; exact appr_spec v hx
  · rw [map_mul]
    calc Valued.v (iO v (appr v x)) * Valued.v (y - iO v (appr v y)) ≤ 1 * Valued.v (y - iO v (appr v y)) := by
          gcongr
      _ < 1 := by rw [one_mul]; exact appr_spec v hy

theorem red_one : red v 1 = 1 := by
  have h := (red_eq_mk_iff v (one_mem _) 1).mpr (by simp [iO])
  rw [h, map_one]

theorem red_eq_zero_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    red v x = 0 ↔ Valued.v x < 1 := by
  rw [← map_zero (Ideal.Quotient.mk v.asIdeal), red_eq_mk_iff v hx]
  simp [iO]

theorem red_zero : red v 0 = 0 := by
  have h := (red_eq_mk_iff v (zero_mem _) 0).mpr (by simp [iO])
  rw [h, map_zero]

theorem red_neg {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) : red v (-x) = -red v x := by
  have hn : -x ∈ v.adicCompletionIntegers F := neg_mem hx
  have e1 : -red v x = Ideal.Quotient.mk _ (-appr v x) := by
    simp only [red, map_neg]
  rw [e1, red_eq_mk_iff v hn]
  have e : -x - iO v (-appr v x) = -(x - iO v (appr v x)) := by
    simp only [iO, map_neg]
    ring
  rw [e, Valuation.map_neg]
  exact appr_spec v hx

theorem red_surj (t : 𝓞 F ⧸ v.asIdeal) : ∃ x ∈ v.adicCompletionIntegers F, red v x = t := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective t
  exact ⟨iO v a, mem_O_iO v a, red_iO v a⟩

theorem lt_one_iff_unif (x : Fv F v) :
    Valued.v x < 1 ↔ Valued.v ((unifV v)⁻¹ * x) ≤ 1 := by
  have hne : (WithZero.exp (-1 : ℤ) : WithZero (Multiplicative ℤ)) ≠ 0 := WithZero.exp_ne_zero
  rw [map_mul, map_inv₀, unifV_val, lt_one_iff_le_expm1]
  constructor
  · intro h
    calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v x ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) :=
          by gcongr
      _ = 1 := inv_mul_cancel₀ hne
  · intro h
    have h2 : WithZero.exp (-1 : ℤ) * ((WithZero.exp (-1 : ℤ))⁻¹ * Valued.v x) ≤ WithZero.exp (-1 : ℤ) * 1 := by
      gcongr
    rwa [← mul_assoc, mul_inv_cancel₀ hne, one_mul, mul_one] at h2

theorem ev_int (x : F) : ∀ᶠ v in cofinite,
    algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  have hfin := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x
  refine Filter.eventually_cofinite.mpr (hfin.subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) F w, vcoe, not_le] at hw
  exact hw

theorem ev_unit {x : F} (hx : x ≠ 0) : ∀ᶠ v in cofinite,
    Valued.v (algebraMap F (Fv F v) x) = 1 := by
  have h1 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x
  have h2 := IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x⁻¹
  refine Filter.eventually_cofinite.mpr ((h1.union h2).subset ?_)
  intro w hw
  simp only [Set.mem_setOf_eq] at hw
  rw [vcoe] at hw
  rcases lt_or_gt_of_ne hw with h | h
  · right
    show 1 < w.valuation F x⁻¹
    rw [map_inv₀]
    exact one_lt_inv_iff₀.mpr ⟨by
      rw [zero_lt_iff]
      exact (Valuation.ne_zero_iff _).mpr hx, h⟩
  · left
    exact h

end Res

section Count

theorem measure_count {G V : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup V] [Finite V] (μ : Measure G) [μ.IsAddLeftInvariant] (L N : AddSubgroup G)
    (hNL : N ≤ L) (hN : MeasurableSet (N : Set G)) (φ : G → V)
    (hadd : ∀ x ∈ L, ∀ y ∈ L, φ (x + y) = φ x + φ y) (hker : ∀ x ∈ L, φ x = 0 ↔ x ∈ N)
    (hsurj : ∀ w, ∃ x ∈ L, φ x = w) (S : Set V) :
    μ {x | x ∈ L ∧ φ x ∈ S} = (Nat.card S : ENNReal) * μ N := by
  classical
  choose xw hxwL hxw using hsurj
  have hS : S.Finite := Set.toFinite S
  have key : ∀ w x, -xw w + x ∈ (N : Set G) → x ∈ L ∧ φ x = w := by
    intro w x hn
    have hnL : -xw w + x ∈ L := hNL hn
    have e : xw w + (-xw w + x) = x := by abel
    have hxL : x ∈ L := by
      have h2 := add_mem (hxwL w) hnL
      rwa [e] at h2
    refine ⟨hxL, ?_⟩
    have h1 := hadd (xw w) (hxwL w) (-xw w + x) hnL
    rw [e, hxw, (hker _ hnL).mpr hn, add_zero] at h1
    exact h1
  have hset : {x | x ∈ L ∧ φ x ∈ S} = ⋃ w ∈ hS.toFinset, (fun n => -xw w + n) ⁻¹' (N : Set G) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_preimage, Set.Finite.mem_toFinset, exists_prop]
    constructor
    · rintro ⟨hxL, hxS⟩
      refine ⟨φ x, hxS, ?_⟩
      have hneg : -xw (φ x) ∈ L := neg_mem (hxwL _)
      have hm : -xw (φ x) + x ∈ L := add_mem hneg hxL
      rw [SetLike.mem_coe, ← hker _ hm]
      have h1 := hadd (-xw (φ x) + x) hm (xw (φ x)) (hxwL _)
      have e : -xw (φ x) + x + xw (φ x) = x := by abel
      rw [e, hxw] at h1
      exact (add_eq_right.mp h1.symm)
    · rintro ⟨w, hwS, hn⟩
      obtain ⟨hxL, hφ⟩ := key w x hn
      exact ⟨hxL, hφ ▸ hwS⟩
  have hd : (↑hS.toFinset : Set V).PairwiseDisjoint (fun w => (fun n => -xw w + n) ⁻¹' (N : Set G)) := by
    intro w _ w' _ hne
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    exact hne ((key w x hx).2.symm.trans (key w' x hx').2)
  have hm : ∀ w ∈ hS.toFinset, MeasurableSet ((fun n => -xw w + n) ⁻¹' (N : Set G)) :=
    fun w _ => measurable_const_add _ hN
  rw [hset, measure_biUnion_finset hd hm]
  simp only [measure_preimage_add]
  rw [Finset.sum_const, nsmul_eq_mul, Nat.card_eq_card_finite_toFinset hS]

end Count

end PI.VolStabS
