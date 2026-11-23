import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree

open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.ComplRes

variable {E k : Type} [Field E] [NumberField E] [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {P : HeightOneSpectrum (𝓞 E)} {q : ℕ} {ι : E →+* k} {ϖ : kˣ}

def vI (h : IsCompl P q ι ϖ) (γ : ValueGroupWithZero k) : Ideal (𝓞 E) where
  carrier := {x | valuation k (ι (x : E)) ≤ γ}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact le_trans (Valuation.map_add _ _ _) (max_le ha hb)
  zero_mem' := by simp
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
    have hc : valuation k (ι (c : E)) ≤ 1 :=
      (Valuation.mem_integer_iff _ _).mp ((h.int _).mpr ⟨c, 1, P.asIdeal.ne_top_iff_one.mp P.isPrime.ne_top, by simp⟩)
    calc _ ≤ 1 * γ := mul_le_mul' hc hx
      _ = γ := one_mul γ

theorem mem_vI (h : IsCompl P q ι ϖ) {γ : ValueGroupWithZero k} (x : 𝓞 E) : x ∈ vI h γ ↔ valuation k (ι (x : E)) ≤ γ := Iff.rfl

theorem intAt_coe (r : 𝓞 E) : IntAt P (r : E) := ⟨r, 1, P.asIdeal.ne_top_iff_one.mp P.isPrime.ne_top, by simp⟩

theorem v_le_one (h : IsCompl P q ι ϖ) {a : E} (ha : IntAt P a) : valuation k (ι a) ≤ 1 :=
  (Valuation.mem_integer_iff _ _).mp ((h.int a).mpr ha)

theorem intAt_of_v (h : IsCompl P q ι ϖ) {a : E} (ha : valuation k (ι a) ≤ 1) : IntAt P a :=
  (h.int a).mp ((Valuation.mem_integer_iff _ _).mpr ha)

theorem v_int_le_one (h : IsCompl P q ι ϖ) (r : 𝓞 E) : valuation k (ι (r : E)) ≤ 1 := v_le_one h (intAt_coe r)

theorem v_unif_lt_one (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : valuation k (ϖ : k) < 1 := (hu ϖ).2 le_rfl

theorem v_unif_ne_zero : valuation k (ϖ : k) ≠ 0 := by simp

theorem q_ne_zero (h : IsCompl P q ι ϖ) : (q : E) ≠ 0 := by
  intro h0; have := h.unif; rw [h0, map_zero] at this; exact ϖ.ne_zero this

theorem v_eq_one_of_not_mem (h : IsCompl P q ι ϖ) {s : 𝓞 E} (hs : s ∉ P.asIdeal) : valuation k (ι (s : E)) = 1 := by
  have hs0 : (s : E) ≠ 0 := by
    intro h0; apply hs; rw [show s = 0 from by exact_mod_cast h0]; exact P.asIdeal.zero_mem
  have hinv : IntAt P ((s : E)⁻¹) := ⟨1, s, hs, by simp [hs0]⟩
  have h1 := v_le_one h hinv
  have h2 := v_int_le_one h s
  have hm : valuation k (ι (s : E)) * valuation k (ι ((s : E)⁻¹)) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ hs0, map_one, map_one]
  by_contra hne
  have hlt : valuation k (ι (s : E)) < 1 := lt_of_le_of_ne h2 hne
  have : valuation k (ι (s : E)) * valuation k (ι ((s : E)⁻¹)) < 1 :=
    calc _ ≤ valuation k (ι (s : E)) * 1 := mul_le_mul' le_rfl h1
      _ = _ := mul_one _
      _ < 1 := hlt
  rw [hm] at this; exact lt_irrefl _ this

theorem coe_mul' (a b : 𝓞 E) : ((a * b : 𝓞 E) : E) = (a : E) * (b : E) := by simp
theorem coe_nat' (n : ℕ) : (((n : ℕ) : 𝓞 E) : E) = (n : E) := by simp
theorem coe_int' (n : ℤ) : (((n : ℤ) : 𝓞 E) : E) = (n : E) := by simp

theorem mem_P_iff (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (x : 𝓞 E) :
    x ∈ P.asIdeal ↔ valuation k (ι (x : E)) < 1 := by
  have hprime : (vI h (valuation k (ϖ : k))).IsPrime := by
    refine ⟨?_, ?_⟩
    · rw [Ideal.ne_top_iff_one, mem_vI]
      intro h1
      simp only [OneMemClass.coe_one, map_one] at h1
      exact absurd (lt_of_le_of_lt h1 (v_unif_lt_one hu)) (lt_irrefl _)
    · intro a b hab
      rw [mem_vI, mem_vI, ← hu, ← hu] at *
      rw [coe_mul', map_mul, map_mul] at hab
      by_contra hn
      push_neg at hn
      have ha : valuation k (ι (a : E)) = 1 := le_antisymm (v_int_le_one h a) hn.1
      have hb : valuation k (ι (b : E)) = 1 := le_antisymm (v_int_le_one h b) hn.2
      rw [ha, hb, one_mul] at hab; exact lt_irrefl _ hab
  have hq : ((q : 𝓞 E)) ∈ vI h (valuation k (ϖ : k)) := by
    rw [mem_vI, h.unif]; simp
  have hne : vI h (valuation k (ϖ : k)) ≠ ⊥ := by
    intro hb; rw [hb, Ideal.mem_bot] at hq
    apply q_ne_zero h
    have := congrArg (fun y : 𝓞 E => (y : E)) hq
    simpa using this
  have hmax := hprime.isMaximal hne
  have hle : vI h (valuation k (ϖ : k)) ≤ P.asIdeal := by
    intro x hx
    by_contra hxP
    rw [mem_vI, v_eq_one_of_not_mem h hxP] at hx
    exact absurd (lt_of_le_of_lt hx (v_unif_lt_one hu)) (lt_irrefl _)
  have heq := hmax.eq_of_le P.isPrime.ne_top hle
  rw [← heq, mem_vI, hu]

theorem v_q (h : IsCompl P q ι ϖ) : valuation k (ι (q : E)) = valuation k (ϖ : k) := by rw [h.unif]

theorem q_mem (h : IsCompl P q ι ϖ) : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  rw [h.norm]; exact Ideal.absNorm_mem _

theorem q_not_mem_sq (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  intro hq
  have hle : P.asIdeal ^ 2 ≤ vI h (valuation k (ϖ : k) ^ 2) := by
    rw [pow_two, Ideal.mul_le]
    intro a ha b hb
    rw [mem_vI, coe_mul', map_mul, map_mul, pow_two]
    exact mul_le_mul' ((hu _).mp ((mem_P_iff h hu a).mp ha)) ((hu _).mp ((mem_P_iff h hu b).mp hb))
  have h1 := hle hq
  rw [mem_vI, coe_nat', v_q h, pow_two] at h1
  have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) := zero_lt_iff.mpr v_unif_ne_zero
  have : (1 : ValueGroupWithZero k) ≤ valuation k (ϖ : k) := by
    have h2 : valuation k (ϖ : k) * 1 ≤ valuation k (ϖ : k) * valuation k (ϖ : k) := by rwa [mul_one]
    exact le_of_mul_le_mul_left h2 h0
  exact absurd (lt_of_le_of_lt this (v_unif_lt_one hu)) (lt_irrefl _)

theorem reduction_spec {a : E} {r s : 𝓞 E} (hs : s ∉ P.asIdeal) (hsa : algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r) :
    Ideal.Quotient.mk P.asIdeal s * redP P a = Ideal.Quotient.mk P.asIdeal r := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hex : ∃ c r s, s ∉ P.asIdeal ∧ algebraMap (𝓞 E) E s * a = algebraMap (𝓞 E) E r ∧
      Ideal.Quotient.mk P.asIdeal s * c = Ideal.Quotient.mk P.asIdeal r :=
    ⟨Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹, r, s, hs, hsa, by field_simp⟩
  unfold redP
  rw [dif_pos hex]
  obtain ⟨r', s', hs', h1, h2⟩ := hex.choose_spec
  have hs0' : Ideal.Quotient.mk P.asIdeal s' ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hrr : s * r' = s' * r := by
    apply FaithfulSMul.algebraMap_injective (𝓞 E) E
    rw [map_mul, map_mul, ← h1, ← hsa]; ring
  have := congrArg (Ideal.Quotient.mk P.asIdeal) hrr
  rw [map_mul, map_mul, ← h2] at this
  apply mul_left_cancel₀ hs0'
  rw [← this]; ring

theorem v_div_q (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (a : E) :
    valuation k (ι a) < 1 ↔ IntAt P (a / (q : E)) := by
  have hq := q_ne_zero h
  have hsplit : valuation k (ι a) = valuation k (ι (a / (q : E))) * valuation k (ϖ : k) := by
    rw [h.unif, ← map_mul, ← map_mul, div_mul_cancel₀ a hq]
  have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) := zero_lt_iff.mpr v_unif_ne_zero
  rw [hu, hsplit]
  constructor
  · intro hle
    apply intAt_of_v h
    have : valuation k (ι (a / (q : E))) * valuation k (ϖ : k) ≤ 1 * valuation k (ϖ : k) := by rwa [one_mul]
    exact le_of_mul_le_mul_right this h0
  · intro hi
    calc _ ≤ 1 * valuation k (ϖ : k) := mul_le_mul' (v_le_one h hi) le_rfl
      _ = _ := one_mul _

theorem v_lt_one_iff_red (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {a : E} (ha : IntAt P a) :
    valuation k (ι a) < 1 ↔ redP P a = 0 := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  obtain ⟨r, s, hs, hsa⟩ := ha
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hspec := reduction_spec hs hsa
  have hv : valuation k (ι a) = valuation k (ι (r : E)) := by
    have e := congrArg (fun y => valuation k (ι y)) hsa
    simp only [map_mul] at e
    have e2 : valuation k (ι (algebraMap (𝓞 E) E s)) = 1 := v_eq_one_of_not_mem h hs
    rw [e2, one_mul] at e
    exact e
  rw [hv, ← mem_P_iff h hu, ← Ideal.Quotient.eq_zero_iff_mem, ← hspec]
  constructor
  · intro h0; exact (mul_eq_zero.mp h0).resolve_left hs0
  · intro h0; rw [h0, mul_zero]

theorem v_eq_one_iff_red (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) {a : E} (ha : IntAt P a) :
    valuation k (ι a) = 1 ↔ IsUnit (redP P a) := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  rw [isUnit_iff_ne_zero, Ne, ← v_lt_one_iff_red h hu ha]
  have := v_le_one h ha
  constructor
  · intro e; rw [e]; exact lt_irrefl _
  · intro hn; exact le_antisymm this (not_lt.mp hn)

theorem card_quot (h : IsCompl P q ι ϖ) : Nat.card (𝓞 E ⧸ P.asIdeal) = q := by
  rw [h.norm, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem q_prime_char (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) :
    q.Prime ∧ CharP (𝓞 E ⧸ P.asIdeal) q := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  have hq0 : q ≠ 0 := by
    intro h0; apply q_ne_zero h; rw [h0, Nat.cast_zero]
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by rw [card_quot h]; exact hq0)
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  haveI := ringChar.charP (𝓞 E ⧸ P.asIdeal)
  obtain ⟨n, hp, hcard⟩ := FiniteField.card (𝓞 E ⧸ P.asIdeal) (ringChar (𝓞 E ⧸ P.asIdeal))
  set p := ringChar (𝓞 E ⧸ P.asIdeal) with hpdef
  have hqp : q = p ^ (n : ℕ) := by rw [← card_quot h, Nat.card_eq_fintype_card, hcard]
  have hpP : ((p : ℕ) : 𝓞 E) ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ p
  have hv : valuation k (ι (p : E)) < 1 := by
    have := (mem_P_iff h hu _).mp hpP; rwa [coe_nat'] at this
  have hv0 : 0 < valuation k (ι (p : E)) := by
    rw [zero_lt_iff, Ne, map_eq_zero, map_eq_zero]; exact_mod_cast hp.ne_zero
  have hle : valuation k (ι (p : E)) ^ 1 ≤ valuation k (ι (p : E)) ^ (n : ℕ) := by
    rw [pow_one, ← map_pow, ← map_pow, ← Nat.cast_pow, ← hqp, ← h.unif, ← hu]
    exact hv
  have hn1 : (n : ℕ) ≤ 1 := (pow_le_pow_iff_right_of_lt_one₀ hv0 hv).mp hle
  have hn : (n : ℕ) = 1 := le_antisymm hn1 n.pos
  rw [hn, pow_one] at hqp
  subst hqp
  exact ⟨hp, inferInstance⟩

theorem unif_eq_cast (h : IsCompl P q ι ϖ) : (ϖ : k) = (q : k) := by rw [h.unif, map_natCast]

theorem v_nat_le_one (h : IsCompl P q ι ϖ) (i : ℕ) : valuation k (i : k) ≤ 1 := by
  have := v_int_le_one h (i : 𝓞 E); rwa [coe_nat', map_natCast] at this

theorem dvd_of_v (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (m : ℕ) :
    ∀ z : ℤ, valuation k (z : k) ≤ valuation k (ϖ : k) ^ m → (q : ℤ) ^ m ∣ z := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  haveI := (q_prime_char h hu).2
  have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) := zero_lt_iff.mpr v_unif_ne_zero
  induction m with
  | zero => intro z _; simp
  | succ m ih =>
    intro z hz
    have hz1 : valuation k (z : k) ≤ valuation k (ϖ : k) :=
      le_trans hz (pow_le_of_le_one zero_le' (le_of_lt (v_unif_lt_one hu)) (Nat.succ_ne_zero m))
    have hzP : ((z : ℤ) : 𝓞 E) ∈ P.asIdeal := by
      rw [mem_P_iff h hu, coe_int', map_intCast, hu]; exact hz1
    have hdq : (q : ℤ) ∣ z := by
      rw [← CharP.intCast_eq_zero_iff (𝓞 E ⧸ P.asIdeal) q, ← map_intCast (Ideal.Quotient.mk P.asIdeal),
        Ideal.Quotient.eq_zero_iff_mem]
      exact hzP
    obtain ⟨w, rfl⟩ := hdq
    have hw : valuation k (w : k) ≤ valuation k (ϖ : k) ^ m := by
      rw [Int.cast_mul, map_mul, Int.cast_natCast, ← unif_eq_cast h, pow_succ'] at hz
      exact le_of_mul_le_mul_left hz h0
    rw [pow_succ']
    exact mul_dvd_mul_left _ (ih w hw)

theorem exists_rep_one (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (x : k) (hx : valuation k x ≤ 1) :
    ∃ i : ℕ, i < q ∧ valuation k (x - i) ≤ valuation k (ϖ : k) := by
  haveI := P.isMaximal
  letI := Ideal.Quotient.field P.asIdeal
  haveI := (q_prime_char h hu).2
  have hq0 : q ≠ 0 := (q_prime_char h hu).1.ne_zero
  haveI : Finite (𝓞 E ⧸ P.asIdeal) := Nat.finite_of_card_ne_zero (by rw [card_quot h]; exact hq0)
  letI := Fintype.ofFinite (𝓞 E ⧸ P.asIdeal)
  have hU : {y | valuation k (y - x) < 1} ∈ nhds x := by
    rw [IsValuativeTopology.mem_nhds_iff]
    exact ⟨1, by rintro _ ⟨z, hz, rfl⟩; simpa using hz⟩
  obtain ⟨_, hy, a, rfl⟩ := mem_closure_iff_nhds.mp (h.dense x) _ hU
  simp only [Set.mem_setOf_eq] at hy
  have ha : IntAt P a := by
    apply intAt_of_v h
    have e : ι a = (ι a - x) + x := by ring
    rw [e]
    exact le_trans (Valuation.map_add _ _ _) (max_le (le_of_lt hy) hx)
  obtain ⟨r, s, hs, hsa⟩ := ha
  have hs0 : Ideal.Quotient.mk P.asIdeal s ≠ 0 := by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  let f : Fin q → 𝓞 E ⧸ P.asIdeal := fun i => ((i : ℕ) : 𝓞 E ⧸ P.asIdeal)
  have hinj : Function.Injective f := by
    intro i j hij
    have := (CharP.natCast_eq_natCast (𝓞 E ⧸ P.asIdeal) q).mp hij
    exact Fin.ext (this.eq_of_lt_of_lt i.2 j.2)
  have hbij : Function.Bijective f := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, card_quot h]
  obtain ⟨i, hi⟩ := hbij.2 (Ideal.Quotient.mk P.asIdeal r * (Ideal.Quotient.mk P.asIdeal s)⁻¹)
  refine ⟨i, i.2, ?_⟩
  have hmem : s * ((i : ℕ) : 𝓞 E) - r ∈ P.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, map_natCast]
    change Ideal.Quotient.mk P.asIdeal s * f i - _ = 0
    rw [hi]; field_simp; ring
  have hv1 := (mem_P_iff h hu _).mp hmem
  have hvs : valuation k (ι (algebraMap (𝓞 E) E s)) = 1 := v_eq_one_of_not_mem h hs
  have hai : valuation k (ι a - (i : ℕ)) < 1 := by
    have e : ι (algebraMap (𝓞 E) E s) * (ι a - ((i : ℕ) : k)) = - ι ((s * ((i : ℕ) : 𝓞 E) - r : 𝓞 E) : E) := by
      have e2 : (((s * ((i : ℕ) : 𝓞 E) - r : 𝓞 E)) : E) = algebraMap (𝓞 E) E s * (i : ℕ) - algebraMap (𝓞 E) E r := by
        simp
      rw [e2, ← hsa]; simp; ring
    have := congrArg (valuation k) e
    rw [map_mul, hvs, one_mul, Valuation.map_neg] at this
    rw [this]; exact hv1
  rw [← hu]
  have e : x - ((i : ℕ) : k) = (x - ι a) + (ι a - (i : ℕ)) := by ring
  rw [e]
  refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ hai)
  rw [Valuation.map_sub_swap]; exact hy

theorem exists_rep (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (n : ℕ) :
    ∀ x : k, valuation k x ≤ 1 → ∃ i : ℕ, i < q ^ n ∧ valuation k (x - i) ≤ valuation k (ϖ : k) ^ n := by
  have h0 : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) := zero_lt_iff.mpr v_unif_ne_zero
  induction n with
  | zero => intro x hx; exact ⟨0, by simp, by simpa using hx⟩
  | succ n ih =>
    intro x hx
    obtain ⟨i, hi, hv⟩ := ih x hx
    have hϖn : ((ϖ : k) ^ n) ≠ 0 := pow_ne_zero _ ϖ.ne_zero
    set y := (x - i) / (ϖ : k) ^ n with hydef
    have hxy : x - i = y * (ϖ : k) ^ n := by rw [hydef, div_mul_cancel₀ _ hϖn]
    have hy : valuation k y ≤ 1 := by
      rw [hxy, map_mul, map_pow] at hv
      have h0n : (0 : ValueGroupWithZero k) < valuation k (ϖ : k) ^ n := pow_pos h0 n
      exact le_of_mul_le_mul_right (by rwa [one_mul]) h0n
    obtain ⟨j, hj, hvj⟩ := exists_rep_one h hu y hy
    refine ⟨i + q ^ n * j, ?_, ?_⟩
    · have h1 : q ^ n * (j + 1) ≤ q ^ n * q := Nat.mul_le_mul_left _ hj
      rw [pow_succ]; linarith
    · have e : x - ((i + q ^ n * j : ℕ) : k) = (ϖ : k) ^ n * (y - j) := by
        rw [unif_eq_cast h] at hxy ⊢
        push_cast
        linear_combination hxy
      rw [e, map_mul, map_pow, pow_succ]
      exact mul_le_mul' le_rfl hvj

theorem rep (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) (n : ℕ) (x : k) (hx : x ∈ 𝒪[k]) :
    ∃! i : ℕ, i < q ^ n ∧ valuation k (x - (i : k)) ≤ valuation k ((ϖ : k) ^ n) := by
  rw [Valuation.mem_integer_iff] at hx
  obtain ⟨i, hi, hv⟩ := exists_rep h hu n x hx
  refine ⟨i, ⟨hi, by rwa [map_pow]⟩, ?_⟩
  rintro i' ⟨hi', hv'⟩
  rw [map_pow] at hv'
  have hd : valuation k (((i : ℤ) - (i' : ℤ) : ℤ) : k) ≤ valuation k (ϖ : k) ^ n := by
    have e : (((i : ℤ) - (i' : ℤ) : ℤ) : k) = (x - (i' : k)) - (x - (i : k)) := by push_cast; ring
    rw [e]
    exact le_trans (Valuation.map_sub _ _ _) (max_le hv' hv)
  have := dvd_of_v h hu n _ hd
  have hmod : i' ≡ i [MOD q ^ n] := by
    rw [Nat.modEq_iff_dvd]; push_cast; exact this
  exact hmod.eq_of_lt_of_lt hi' hi

theorem residue_eq_zero_iff' (y : 𝒪[k]) : IsLocalRing.residue 𝒪[k] y = 0 ↔ valuation k (y : k) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  constructor
  · intro h; exact lt_of_le_of_ne y.2 h
  · intro h; exact ne_of_lt h

theorem resCard_eq (h : IsCompl P q ι ϖ) (hu : GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ) : resCard k = q := by
  have hmem : ∀ i : ℕ, (i : k) ∈ 𝒪[k] := fun i => (Valuation.mem_integer_iff _ _).mpr (v_nat_le_one h i)
  let f : Fin q → 𝓀[k] := fun i => IsLocalRing.residue 𝒪[k] ⟨((i : ℕ) : k), hmem i⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro i j hij
      have h1 : IsLocalRing.residue 𝒪[k] (⟨((i : ℕ) : k), hmem i⟩ - ⟨((j : ℕ) : k), hmem j⟩) = 0 := by
        rw [map_sub]; exact sub_eq_zero.mpr hij
      rw [residue_eq_zero_iff', hu] at h1
      have hd : valuation k ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : k) ≤ valuation k (ϖ : k) ^ 1 := by
        rw [pow_one]; push_cast; exact h1
      have := dvd_of_v h hu 1 _ hd
      have hmod : (j : ℕ) ≡ (i : ℕ) [MOD q ^ 1] := by
        rw [Nat.modEq_iff_dvd]; push_cast at this ⊢; exact this
      exact Fin.ext (hmod.eq_of_lt_of_lt (by simpa using j.2) (by simpa using i.2)).symm
    · intro z
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
      obtain ⟨i, hi, hv⟩ := exists_rep_one h hu (x : k) ((Valuation.mem_integer_iff _ _).mp x.2)
      refine ⟨⟨i, hi⟩, ?_⟩
      show IsLocalRing.residue 𝒪[k] _ = _
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff']
      have e : ((⟨((i : ℕ) : k), hmem i⟩ - x : 𝒪[k]) : k) = - ((x : k) - i) := by
        simp
      rw [e, Valuation.map_neg, hu]; exact hv
  unfold resCard
  rw [← Nat.card_eq_of_bijective f hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem residues : ∀ (E k : Type) [Field E] [NumberField E] [StarRing E] [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ) (ι : E →+* k) (ϖ : kˣ),
    IsCompl P q ι ϖ → GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum.IsUnif ϖ →
      (∀ a, valuation k (ι a) < 1 ↔ IntAt P (a / (q : E))) ∧
      (∀ a, IntAt P a → (valuation k (ι a) < 1 ↔ redP P a = 0)) ∧
      (∀ a, IntAt P a → (valuation k (ι a) = 1 ↔ IsUnit (redP P a))) ∧
      (q : E) ≠ 0 ∧ ((q : ℕ) : 𝓞 E) ∈ P.asIdeal ∧ ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧ resCard k = q ∧
      ∀ (n : ℕ) (x : k), x ∈ 𝒪[k] → ∃! i : ℕ, i < q ^ n ∧ valuation k (x - (i : k)) ≤ valuation k ((ϖ : k) ^ n) := by
  intro E k _ _ _ _ _ _ _ P q ι ϖ h hu
  exact ⟨v_div_q h hu, fun a ha => v_lt_one_iff_red h hu ha, fun a ha => v_eq_one_iff_red h hu ha, q_ne_zero h, q_mem h,
    q_not_mem_sq h hu, resCard_eq h hu, fun n x hx => rep h hu n x hx⟩

end GlobalTheory.SymBridge.ComplRes
