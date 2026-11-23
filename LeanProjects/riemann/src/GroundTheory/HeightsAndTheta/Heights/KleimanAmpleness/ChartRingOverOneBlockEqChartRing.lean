import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreTer
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

section Frac

theorem coe_ne_zero_of_not_mem {A : Subalgebra S Ω} {p : Ideal A} {b : A} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]
  exact p.zero_mem

theorem one_not_mem_of_prime {A : Subalgebra S Ω} {p : Ideal A} (hp : p.IsPrime) : (1 : A) ∉ p :=
  fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)

def fracSub (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : Subalgebra S Ω where
  carrier := {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_add_div _ _ (coe_ne_zero_of_not_mem hb) (coe_ne_zero_of_not_mem hb')]
  algebraMap_mem' r := ⟨algebraMap S A r, 1, one_not_mem_of_prime hp, by simp⟩

theorem mem_locIn {A : Subalgebra S Ω} {p : Ideal A} [p.IsPrime] {u : Ω} :
    u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p ↔ ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b := by
  constructor
  · intro h
    exact (Subring.closure_le (t := (fracSub A p).toSubring)).mpr (fun v hv => hv) h
  · intro h
    exact Subring.subset_closure h

theorem span_subset_span {A B : Subalgebra S Ω} (hAB : A ≤ B) (s : Set Ω) :
    (Submodule.span A s : Set Ω) ⊆ Submodule.span B s := by
  intro z (hz : z ∈ Submodule.span A s)
  induction hz using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul a z _ hz =>
    have e : a • z = (⟨a, hAB a.2⟩ : B) • z := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ hz

theorem mul_eq_one_of_le {A B : Subalgebra S Ω} (hAB : A ≤ B) (M Q' : Submodule A Ω) (h : M * Q' = 1) :
    Submodule.span B (M : Set Ω) * Submodule.span B (Q' : Set Ω) = 1 := by
  rw [Submodule.span_mul_span]
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨m, hm, q, hq, rfl⟩
    have h1 := Submodule.mul_mem_mul hm hq
    rw [h, Submodule.mem_one] at h1
    obtain ⟨y, hy⟩ := h1
    rw [SetLike.mem_coe, Submodule.mem_one]
    exact ⟨⟨y, hAB y.2⟩, hy⟩
  · rw [Submodule.one_le]
    have h1 : (1 : Ω) ∈ M * Q' := by rw [h]; exact Submodule.one_le.mp le_rfl
    rw [Submodule.mul_eq_span_mul_set] at h1
    exact span_subset_span hAB _ h1

theorem exists_sum_eq_one {A : Subalgebra S Ω} {m : ℕ} (g : Fin m → Ω) (Q' : Submodule A Ω)
    (hQQ : Submodule.span A (Set.range g) * Q' = 1) :
    ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ (∀ a b, g a * w b ∈ A) ∧ ∑ b, g b * w b = 1 := by
  classical
  have hone : (1 : Ω) ∈ Submodule.span A (Set.range g) * Q' := by
    rw [hQQ]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  obtain ⟨w, hwQ, hsum⟩ : ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = 1 := by
    refine Submodule.mul_induction_on
      (C := fun z => ∃ w : Fin m → Ω, (∀ b, w b ∈ Q') ∧ ∑ b, g b * w b = z) hone ?_ ?_
    · intro q hq q' hq'
      obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp hq
      refine ⟨fun b => (a b : Ω) * q', fun b => Q'.smul_mem (a b) hq', ?_⟩
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul]
      ring
    · rintro _ _ ⟨w, hw, rfl⟩ ⟨w', hw', rfl⟩
      refine ⟨w + w', fun b => Q'.add_mem (hw b) (hw' b), ?_⟩
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by simp [mul_add]
  refine ⟨w, hwQ, fun a b => ?_, hsum⟩
  have h := Submodule.mul_mem_mul (Submodule.subset_span ⟨a, rfl⟩ : g a ∈ Submodule.span A (Set.range g))
    (hwQ b)
  rw [hQQ, Submodule.mem_one] at h
  obtain ⟨y, hy⟩ := h
  rw [← hy]
  exact y.2

theorem chartRingOver_oneBlock_eq_chartRing {N : ℕ} (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (h : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Kleiman.chartRing S x (Kleiman.singleChart h) := by
  rw [← TranslateEq.chartRing.equiv S x h]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Frac

section Dom

variable {N N' : ℕ}

variable (S) in

def LocGen (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) : Prop :=
  ∀ c : Unit → Fin (N' + 1), x' (c ()) ≠ 0 →
    ∀ p : Ideal (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c), p.IsPrime →
      ∃ i, x i ≠ 0 ∧ ∀ a, x a / x i ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c) p

theorem exists_inv_of_loc (A : Subalgebra S Ω) (x : Fin (N + 1) → Ω)
    (h : ∀ P : Ideal A, P.IsPrime → ∃ i, x i ≠ 0 ∧ ∀ a, x a / x i ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A P) :
    ∃ Q' : Submodule A Ω, Submodule.span A (Set.range x) * Q' = 1 := by
  classical
  let Q' : Submodule A Ω :=
    { carrier := {w | ∀ a, x a * w ∈ A}
      add_mem' := fun {u v} hu hv a => by rw [mul_add]; exact A.add_mem (hu a) (hv a)
      zero_mem' := fun a => by rw [mul_zero]; exact A.zero_mem
      smul_mem' := fun c w hw a => by
        rw [Subalgebra.smul_def, smul_eq_mul, mul_left_comm]; exact A.mul_mem c.2 (hw a) }
  refine ⟨Q', le_antisymm ?_ ?_⟩
  · rw [Submodule.mul_le]
    intro z hz w hw
    rw [Submodule.mem_one]
    have hzw : z * w ∈ A := by
      induction hz using Submodule.span_induction with
      | mem z hz => obtain ⟨a, rfl⟩ := hz; exact hw a
      | zero => rw [zero_mul]; exact A.zero_mem
      | add u v _ _ hu hv => rw [add_mul]; exact A.add_mem hu hv
      | smul c u _ hu => rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc]; exact A.mul_mem c.2 hu
    exact ⟨⟨z * w, hzw⟩, rfl⟩
  · rw [Submodule.one_le]
    by_contra h1
    let J : Ideal A := Submodule.comap (Algebra.linearMap A Ω) (Submodule.span A (Set.range x) * Q')
    have hJ : J ≠ ⊤ := by
      intro hJ
      apply h1
      have : (1 : A) ∈ J := hJ ▸ Submodule.mem_top
      simpa [J] using this
    obtain ⟨P, hP, hJP⟩ := Ideal.exists_le_maximal J hJ
    have := hP.isPrime
    obtain ⟨i, hi, hdiv⟩ := h P hP.isPrime
    have hfr : ∀ a, ∃ u v : A, v ∉ P ∧ x a / x i = (u : Ω) / v := fun a => mem_locIn.mp (hdiv a)
    choose u v hv huv using hfr
    let V : A := ∏ a, v a
    have hV : V ∉ P := by
      intro hV'
      obtain ⟨a, _, ha⟩ := Ideal.IsPrime.prod_mem_iff.mp hV'
      exact hv a ha
    have hw : (V : Ω) / x i ∈ Q' := by
      intro a
      have hva := coe_ne_zero_of_not_mem (hv a)
      have hprod : (V : Ω) = v a * ∏ b ∈ Finset.univ.erase a, (v b : Ω) := by
        simp only [V]
        push_cast
        exact (Finset.mul_prod_erase _ _ (Finset.mem_univ a)).symm
      have e : x a * ((V : Ω) / x i) = u a * ∏ b ∈ Finset.univ.erase a, (v b : Ω) := by
        calc x a * ((V : Ω) / x i) = (x a / x i) * V := by ring
          _ = ((u a : Ω) / v a) * (v a * ∏ b ∈ Finset.univ.erase a, (v b : Ω)) := by rw [huv, hprod]
          _ = u a * ∏ b ∈ Finset.univ.erase a, (v b : Ω) := by field_simp
      rw [e]
      exact A.mul_mem (u a).2 (Subalgebra.prod_mem _ fun b _ => (v b).2)
    have hmem : (V : Ω) ∈ Submodule.span A (Set.range x) * Q' := by
      have := Submodule.mul_mem_mul
        (Submodule.subset_span ⟨i, rfl⟩ : x i ∈ Submodule.span A (Set.range x)) hw
      rwa [mul_div_cancel₀ _ hi] at this
    exact hV (hJP hmem)

theorem locGen_of_isDomination {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
    (hd : Kleiman.IsDomination S x x') : LocGen S x x' := by
  intro c hc p hp
  have := hp
  obtain ⟨Q', hQ'⟩ := hd.invertible (Kleiman.singleChart hc)
  have hA := chartRingOver_oneBlock_eq_chartRing (S := S) x' c hc
  obtain ⟨w, -, hwA, hsum⟩ := exists_sum_eq_one x Q' hQ'
  have hwB : ∀ a b, x a * w b ∈ chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c := fun a b => by
    rw [hA]; exact hwA a b
  let e : Fin (N + 1) → chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c := fun b => ⟨x b * w b, hwB b b⟩
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ p := by
    by_contra hall
    push Not at hall
    apply hp.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 : (1 : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c) = ∑ b, e b :=
      Subtype.ext (by simp [e, hsum])
    rw [h1]
    exact Ideal.sum_mem _ fun b _ => hall b
  have hei : (e i : Ω) ≠ 0 := coe_ne_zero_of_not_mem hi
  have hxi : x i ≠ 0 := fun h0 => hei (by simp [e, h0])
  have hwi : w i ≠ 0 := fun h0 => hei (by simp [e, h0])
  refine ⟨i, hxi, fun a => mem_locIn.mpr ⟨⟨x a * w i, hwB a i⟩, e i, hi, ?_⟩⟩
  simp only [e]
  field_simp

theorem isDomination_of_locGen {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω} (h : LocGen S x x') :
    Kleiman.IsDomination S x x' := by
  refine ⟨fun I => ?_⟩
  obtain ⟨i', hi'I⟩ := I.2.1
  have hi' : x' i' ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi'I)
  have hA := chartRingOver_oneBlock_eq_chartRing (S := S) x' (fun _ => i') hi'
  obtain ⟨Q₁, hQ₁⟩ : ∃ Q₁ : Submodule (Kleiman.chartRing S x' (Kleiman.singleChart hi')) Ω,
      Submodule.span _ (Set.range x) * Q₁ = 1 := by
    refine exists_inv_of_loc _ x fun P hP => ?_
    have := hP
    let φ := Subalgebra.equivOfEq _ _ hA
    obtain ⟨i, hi, hdiv⟩ := h (fun _ => i') hi' (P.comap φ) inferInstance
    refine ⟨i, hi, fun a => ?_⟩
    obtain ⟨u, v, hv, huv⟩ := mem_locIn.mp (hdiv a)
    exact mem_locIn.mpr ⟨φ u, φ v, hv, huv⟩
  have hle : Kleiman.chartRing S x' (Kleiman.singleChart hi') ≤ Kleiman.chartRing S x' I :=
    Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hi'I)
  refine ⟨Submodule.span _ (Q₁ : Set Ω), ?_⟩
  have h1 := mul_eq_one_of_le hle _ Q₁ hQ₁
  have hspan : Submodule.span (Kleiman.chartRing S x' I)
      (Submodule.span (Kleiman.chartRing S x' (Kleiman.singleChart hi')) (Set.range x) : Set Ω) =
      Submodule.span (Kleiman.chartRing S x' I) (Set.range x) := by
    apply le_antisymm
    · rw [Submodule.span_le]; exact span_subset_span hle _
    · exact Submodule.span_mono Submodule.subset_span
  rw [hspan] at h1
  exact h1

theorem locGen_of_dominates {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω}
    (h : IndefiniteRowSideFullHecke.Kleiman2.Dominates S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x)) : LocGen S x x' := by
  intro c hc p hp
  have := hp
  obtain ⟨_, ⟨c₀, hc₀, q, hq, rfl⟩, hle, -⟩ :=
    h _ ⟨c, fun k => by cases k; exact hc, p, hp, rfl⟩
  have := hq
  refine ⟨c₀ (), hc₀ (), fun a => hle ?_⟩
  refine mem_locIn.mpr ⟨⟨_, Algebra.subset_adjoin ⟨⟨(), a⟩, rfl⟩⟩, 1, one_not_mem_of_prime hq, ?_⟩
  rw [OneMemClass.coe_one, div_one]
  rfl

theorem num_mem_of_eq {B : Subalgebra S Ω} {p : Ideal B} [hp : p.IsPrime] {a b a' b' : B} (hb : b ∉ p)
    (hb' : b' ∉ p) (h : (a : Ω) / b = a' / b') (ha : a ∈ p) : a' ∈ p := by
  have h0 := coe_ne_zero_of_not_mem hb
  have h0' := coe_ne_zero_of_not_mem hb'
  have e : a * b' = a' * b := by
    apply Subtype.ext
    push_cast
    rw [div_eq_div_iff h0 h0'] at h
    exact h
  have : a' * b ∈ p := e ▸ p.mul_mem_right b' ha
  exact (hp.mem_or_mem this).resolve_right hb

theorem exists_dominated (B A : Subalgebra S Ω) (p : Ideal B) [hp : p.IsPrime] (hAZ : A ≤ fracSub B p) :
    ∃ q : Ideal A, q.IsPrime ∧ IndefiniteRowSideFullHecke.Kleiman2.locIn A q ≤ IndefiniteRowSideFullHecke.Kleiman2.locIn B p ∧
      ∀ a ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A q, a⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn B p → a⁻¹ ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A q := by
  have h1p := one_not_mem_of_prime hp
  have hA1 : ∀ w : A, ∃ r t : B, t ∉ p ∧ (w : Ω) = r / t := fun w => hAZ w.2
  let q : Ideal A :=
    { carrier := {w | ∃ u v : B, u ∈ p ∧ v ∉ p ∧ (w : Ω) = u / v}
      zero_mem' := ⟨0, 1, p.zero_mem, h1p, by simp⟩
      add_mem' := by
        rintro w w' ⟨u, v, hu, hv, hw⟩ ⟨u', v', hu', hv', hw'⟩
        refine ⟨u * v' + v * u', v * v', p.add_mem (p.mul_mem_right _ hu) (p.mul_mem_left _ hu'),
          fun h => (hp.mem_or_mem h).elim hv hv', ?_⟩
        push_cast
        rw [hw, hw', div_add_div _ _ (coe_ne_zero_of_not_mem hv) (coe_ne_zero_of_not_mem hv')]
      smul_mem' := by
        rintro c w ⟨u, v, hu, hv, hw⟩
        obtain ⟨r, t, ht, hrt⟩ := hA1 c
        refine ⟨r * u, t * v, p.mul_mem_left _ hu, fun h => (hp.mem_or_mem h).elim ht hv, ?_⟩
        rw [smul_eq_mul]
        push_cast
        rw [hw, hrt, div_mul_div_comm] }
  have hq_not : ∀ (w : A) (r t : B), t ∉ p → (w : Ω) = r / t → w ∉ q → r ∉ p :=
    fun w r t ht hw hwq hr => hwq ⟨r, t, hr, ht, hw⟩
  have hq_mem : ∀ (w : A) (r t : B), t ∉ p → (w : Ω) = r / t → w ∈ q → r ∈ p := by
    rintro w r t ht hw ⟨u, v, hu, hv, hw'⟩
    exact num_mem_of_eq hv ht (hw'.symm.trans hw) hu
  have hqp : q.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro hq
      have : (1 : A) ∈ q := hq ▸ Submodule.mem_top
      exact h1p (hq_mem 1 1 1 h1p (by simp) this)
    · intro w w' hww
      obtain ⟨r, t, ht, hw⟩ := hA1 w
      obtain ⟨r', t', ht', hw'⟩ := hA1 w'
      have := hq_mem (w * w') (r * r') (t * t') (fun h => (hp.mem_or_mem h).elim ht ht')
        (by push_cast; rw [hw, hw', div_mul_div_comm]) hww
      rcases hp.mem_or_mem this with h | h
      · exact Or.inl ⟨r, t, h, ht, hw⟩
      · exact Or.inr ⟨r', t', h, ht', hw'⟩
  refine ⟨q, hqp, ?_, ?_⟩
  · intro u hu
    obtain ⟨c', d, hd, rfl⟩ := mem_locIn.mp hu
    obtain ⟨r, t, ht, hc'⟩ := hA1 c'
    obtain ⟨r', t', ht', hd'⟩ := hA1 d
    have hr' : r' ∉ p := hq_not d r' t' ht' hd' hd
    refine mem_locIn.mpr ⟨r * t', t * r', fun h => (hp.mem_or_mem h).elim ht hr', ?_⟩
    rw [hc', hd', div_div_div_eq]
    push_cast
    rfl
  · intro a ha hinv
    obtain ⟨c', d, hd, rfl⟩ := mem_locIn.mp ha
    by_cases hc0 : (c' : Ω) = 0
    · rw [hc0, zero_div, inv_zero]
      exact zero_mem _
    have hcq : c' ∉ q := by
      intro hcq
      obtain ⟨r, t, ht, hc'⟩ := hA1 c'
      have hr : r ∈ p := hq_mem c' r t ht hc' hcq
      obtain ⟨r', t', ht', hd'⟩ := hA1 d
      have hr' : r' ∉ p := hq_not d r' t' ht' hd' hd
      obtain ⟨e, f, hf, hef⟩ := mem_locIn.mp hinv
      have hr0 : (r : Ω) ≠ 0 := by
        intro h0; apply hc0; rw [hc', h0, zero_div]
      have ht0 := coe_ne_zero_of_not_mem ht
      have ht'0 := coe_ne_zero_of_not_mem ht'
      have hf0 := coe_ne_zero_of_not_mem hf
      have key : r' * t * f = e * (t' * r) := by
        apply Subtype.ext
        rw [inv_div, hc', hd', div_div_div_eq, div_eq_div_iff (mul_ne_zero ht'0 hr0) hf0] at hef
        push_cast
        linear_combination hef
      have : r' * t * f ∈ p := key ▸ p.mul_mem_left _ (p.mul_mem_left _ hr)
      rcases hp.mem_or_mem this with h | h
      · rcases hp.mem_or_mem h with h | h
        · exact hr' h
        · exact ht h
      · exact hf h
    rw [inv_div]
    exact mem_locIn.mpr ⟨d, c', hcq, rfl⟩

theorem dominates_of_locGen {x : Fin (N + 1) → Ω} {x' : Fin (N' + 1) → Ω} (h : LocGen S x x') :
    IndefiniteRowSideFullHecke.Kleiman2.Dominates S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) := by
  rintro _ ⟨c, hc, p, hp, rfl⟩
  have := hp
  obtain ⟨i, hi, hdiv⟩ := h c (hc ()) p hp
  have hAZ : chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) (fun _ : Unit => i) ≤
      fracSub (chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') c) p :=
    Algebra.adjoin_le (by rintro _ ⟨⟨⟨⟩, a⟩, rfl⟩; exact mem_locIn.mp (hdiv a))
  obtain ⟨q, hq, hle, hloc⟩ := exists_dominated _ _ p hAZ
  exact ⟨_, ⟨fun _ => i, fun _ => hi, q, hq, rfl⟩, hle, hloc⟩

theorem isDomination_iff_dominates (x : Fin (N + 1) → Ω) (x' : Fin (N' + 1) → Ω) :
    Kleiman.IsDomination S x x' ↔
      IndefiniteRowSideFullHecke.Kleiman2.Dominates S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) :=
  ⟨fun h => dominates_of_locGen (locGen_of_isDomination h),
    fun h => isDomination_of_locGen (locGen_of_dominates h)⟩

end Dom

section Join

variable {N N' m : ℕ}

def joinChart3 (i' : Fin (N' + 1)) (i : Fin (N + 1)) (j : Fin m) :
    ∀ k, Sum.elim (fun _ : Unit => Fin (N' + 1)) (graphIdx N m) k :=
  IndefiniteRowSideFullHecke.Kleiman2.joinChart (fun _ : Unit => i') (graphChart i j)

variable (S) in

abbrev joinRing (x' : Fin (N' + 1) → Ω) (x : Fin (N + 1) → Ω) (s : Fin m → Ω) (i' : Fin (N' + 1))
    (i : Fin (N + 1)) (j : Fin m) : Subalgebra S Ω :=
  chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (graphVec x s)) (joinChart3 i' i j)

variable (S) in

def pairRing (x' : Fin (N' + 1) → Ω) (x : Fin (N + 1) → Ω) (i' : Fin (N' + 1)) (i : Fin (N + 1)) :
    Subalgebra S Ω :=
  Algebra.adjoin S (Set.range (fun a => x' a / x' i') ∪ Set.range (fun a => x a / x i))

variable {x' : Fin (N' + 1) → Ω} {x : Fin (N + 1) → Ω}

theorem joinRing_le (s : Fin m → Ω) (i' : Fin (N' + 1)) (i : Fin (N + 1)) (j : Fin m) (T : Subalgebra S Ω)
    (h1 : ∀ a, x' a / x' i' ∈ T) (h2 : ∀ a, x a / x i ∈ T) (h3 : ∀ b, s b / s j ∈ T) :
    joinRing S x' x s i' i j ≤ T := by
  refine Algebra.adjoin_le ?_
  rintro _ ⟨⟨⟨⟩ | ⟨⟩ | ⟨⟩, a⟩, rfl⟩
  · exact h1 a
  · exact h2 a
  · exact h3 a

theorem pairRing_le_joinRing (s : Fin m → Ω) (i' : Fin (N' + 1)) (i : Fin (N + 1)) (j : Fin m) :
    pairRing S x' x i' i ≤ joinRing S x' x s i' i j := by
  refine Algebra.adjoin_le ?_
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · exact Algebra.subset_adjoin ⟨⟨Sum.inl (), a⟩, rfl⟩
  · exact Algebra.subset_adjoin ⟨⟨Sum.inr (Sum.inl ()), a⟩, rfl⟩

theorem chartRing_le_pairRing' {i' : Fin (N' + 1)} (hi' : x' i' ≠ 0) (i : Fin (N + 1)) :
    Kleiman.chartRing S x' (Kleiman.singleChart hi') ≤ pairRing S x' x i' i := by
  rw [← TranslateEq.chartRing.equiv S x' hi']
  refine Algebra.adjoin_le ?_
  rintro _ ⟨a, rfl⟩
  exact Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)

theorem chartRing_le_pairRing (i' : Fin (N' + 1)) {i : Fin (N + 1)} (hi : x i ≠ 0) :
    Kleiman.chartRing S x (Kleiman.singleChart hi) ≤ pairRing S x' x i' i := by
  rw [← TranslateEq.chartRing.equiv S x hi]
  refine Algebra.adjoin_le ?_
  rintro _ ⟨a, rfl⟩
  exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)

theorem graphRing_le_joinRing (s : Fin m → Ω) (i' : Fin (N' + 1)) {i : Fin (N + 1)} (hi : x i ≠ 0) (j : Fin m) :
    graphRing S x s i j ≤ joinRing S x' x s i' i j :=
  graphRing_le x s hi j _ ((chartRing_le_pairRing i' hi).trans (pairRing_le_joinRing s i' i j))
    fun b => Algebra.subset_adjoin ⟨⟨Sum.inr (Sum.inr ()), b⟩, rfl⟩

theorem prod_join (s : Fin m → Ω) (β : Unit ⊕ (Unit ⊕ Unit) → ℤ) (i' : Fin (N' + 1)) (i : Fin (N + 1))
    (j : Fin m) :
    ∏ k, IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (graphVec x s) ⟨k, joinChart3 i' i j k⟩ ^ (-β k) =
      x' i' ^ (-β (Sum.inl ())) * (x i ^ (-β (Sum.inr (Sum.inl ()))) * s j ^ (-β (Sum.inr (Sum.inr ())))) := by
  simp only [Fintype.prod_sum_type, Fintype.univ_unit, Finset.prod_singleton]
  rfl

theorem mem_secOver_join_iff (s : Fin m → Ω) (n : ℤ) (t : Ω) :
    t ∈ secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (graphVec x s))
        (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (graphDeg n)) ↔
      ∀ i' i j, x' i' ≠ 0 → x i ≠ 0 → s j ≠ 0 → t * (x i ^ n * (s j)⁻¹) ∈ joinRing S x' x s i' i j := by
  have hprod : ∀ i' i j, ∏ k, IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (graphVec x s)
      ⟨k, joinChart3 i' i j k⟩ ^ (-(IndefiniteRowSideFullHecke.Kleiman2.pullDeg (graphDeg n)) k) = x i ^ n * (s j)⁻¹ := by
    intro i' i j
    rw [prod_join]
    simp [IndefiniteRowSideFullHecke.Kleiman2.pullDeg, graphDeg]
  simp only [secOver, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulRight_apply,
    Subalgebra.mem_toSubmodule]
  constructor
  · intro h i' i j hi' hi hj
    have := h (joinChart3 i' i j) (by rintro (⟨⟩ | ⟨⟩ | ⟨⟩); exacts [hi', hi, hj])
    rwa [hprod] at this
  · intro h c hc
    obtain ⟨i', i, j, rfl⟩ : ∃ i' i j, c = joinChart3 i' i j :=
      ⟨c (Sum.inl ()), c (Sum.inr (Sum.inl ())), c (Sum.inr (Sum.inr ())), by
        funext k; rcases k with ⟨⟩ | ⟨⟩ | ⟨⟩ <;> rfl⟩
    rw [hprod]
    exact h i' i j (hc (Sum.inl ())) (hc (Sum.inr (Sum.inl ()))) (hc (Sum.inr (Sum.inr ())))

theorem mem_pullSys_pow_one (a : Fin (N + 1)) (I : Kleiman.Chart x') :
    x a ∈ ((Kleiman.pullSys (S := S) x x').pow 1).sub I := by
  change x a ∈ Submodule.span _ _
  refine Submodule.subset_span ⟨x a, Submodule.subset_span ⟨a, rfl⟩, 1, ?_, by rw [smul_eq_mul, mul_one]⟩
  exact (TranslateEq.pow_zero_sub _ I 1).mpr (one_mem _)

theorem div_pow_mem_pairRing {i' : Fin (N' + 1)} (hi' : x' i' ≠ 0) (i : Fin (N + 1)) (k : ℕ) (y : Ω)
    (hy : y ∈ ((Kleiman.pullSys (S := S) x x').pow k).sub (Kleiman.singleChart hi')) :
    y / x i ^ k ∈ pairRing S x' x i' i := by
  have hA := chartRing_le_pairRing' (S := S) (x := x) hi' i
  induction k generalizing y with
  | zero =>
    rw [TranslateEq.pow_zero_sub] at hy
    rw [pow_zero, div_one]
    exact hA hy
  | succ k ih =>
    change y ∈ Submodule.span _ _ at hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨q, hq, z', hz', rfl⟩ := hz
      have hq' : q / x i ∈ pairRing S x' x i' i := by
        change q ∈ Submodule.span _ (Set.range x) at hq
        induction hq using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨a, rfl⟩ := hz
          exact Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)
        | zero => rw [zero_div]; exact Subalgebra.zero_mem _
        | add u v _ _ hu hv => rw [add_div]; exact Subalgebra.add_mem _ hu hv
        | smul c u _ hu =>
          rw [Kleiman.chartRing_smul_def, mul_div_assoc]
          exact Subalgebra.mul_mem _ (hA c.2) hu
      have e : q • z' / x i ^ (k + 1) = (q / x i) * (z' / x i ^ k) := by
        rw [smul_eq_mul, pow_succ]; ring
      rw [e]
      exact Subalgebra.mul_mem _ hq' (ih z' hz')
    | zero => rw [zero_div]; exact Subalgebra.zero_mem _
    | add u v _ _ hu hv => rw [add_div]; exact Subalgebra.add_mem _ hu hv
    | smul c u _ hu =>
      rw [Kleiman.chartRing_smul_def, mul_div_assoc]
      exact Subalgebra.mul_mem _ (hA c.2) hu

theorem mem_pairRing_of_mem_domRing {i' : Fin (N' + 1)} (hi' : x' i' ≠ 0) {i : Fin (N + 1)} (hi : x i ≠ 0)
    {a : Ω} (ha : a ∈ Kleiman.domRing S x x' i) : a ∈ pairRing S x' x i' i := by
  rw [Kleiman.domRing, Kleiman.ampleRing] at ha
  obtain ⟨k, hk⟩ := Set.mem_iInter.mp ha (Kleiman.singleChart hi')
  rw [one_mul] at hk
  have := div_pow_mem_pairRing hi' i k _ hk
  rwa [mul_div_assoc, div_self (pow_ne_zero k hi), mul_one] at this

variable (x x') in

def ampleChartSub (i : Fin (N + 1)) (I : Kleiman.Chart x') : Subalgebra S Ω where
  carrier := Kleiman.ampleChart (Kleiman.pullSys (S := S) x x') 1 (x i) I
  mul_mem' := by
    rintro a b ⟨n, hn⟩ ⟨n', hn'⟩
    refine ⟨n + n', ?_⟩
    have e : a * b * x i ^ (n + n') = a * x i ^ n * (b * x i ^ n') := by ring
    rw [e, Nat.mul_add]
    exact TranslateEq.mul_mem_pow _ I hn hn'
  add_mem' := by
    rintro a b ⟨n, hn⟩ ⟨n', hn'⟩
    refine ⟨n + n', ?_⟩
    have hh := mem_pullSys_pow_one (S := S) (x' := x') (x := x) i I
    have e : (a + b) * x i ^ (n + n') = a * x i ^ n * x i ^ n' + b * x i ^ n' * x i ^ n := by ring
    rw [e, Nat.mul_add]
    refine add_mem (TranslateEq.mul_mem_pow _ I hn (TranslateEq.pow_mem_pow _ I hh n')) ?_
    rw [Nat.add_comm (1 * n)]
    exact TranslateEq.mul_mem_pow _ I hn' (TranslateEq.pow_mem_pow _ I hh n)
  algebraMap_mem' r := ⟨0, by
    rw [pow_zero, mul_one, Nat.mul_zero, TranslateEq.pow_zero_sub]
    exact Subalgebra.algebraMap_mem _ r⟩

theorem pairRing_le_ampleChartSub {i' : Fin (N' + 1)} (hi' : x' i' ≠ 0) (i : Fin (N + 1))
    (I : Kleiman.Chart x') (hI : i' ∈ I.1) : pairRing S x' x i' i ≤ ampleChartSub x' x i I := by
  refine Algebra.adjoin_le ?_
  rintro _ (⟨a, rfl⟩ | ⟨a, rfl⟩)
  · refine ⟨0, ?_⟩
    rw [pow_zero, mul_one, Nat.mul_zero, TranslateEq.pow_zero_sub]
    exact Kleiman.chartRing_mono (Finset.singleton_subset_iff.mpr hI) (Kleiman.ratio hi' a).2
  · refine ⟨1, ?_⟩
    by_cases hi : x i = 0
    · change x a / x i * x i ^ 1 ∈ _
      rw [hi, div_zero, zero_mul]
      exact zero_mem _
    · change x a / x i * x i ^ 1 ∈ _
      rw [pow_one, div_mul_cancel₀ _ hi, Nat.mul_one]
      exact mem_pullSys_pow_one a I

theorem mem_domRing_of_forall {i : Fin (N + 1)} {a : Ω} (h : ∀ i', x' i' ≠ 0 → a ∈ pairRing S x' x i' i) :
    a ∈ Kleiman.domRing S x x' i := by
  rw [Kleiman.domRing, Kleiman.ampleRing]
  refine Set.mem_iInter.mpr fun I => ?_
  obtain ⟨i', hi'I⟩ := I.2.1
  have hi' : x' i' ≠ 0 := (Kleiman.mem_support x').mp (I.2.2 hi'I)
  exact pairRing_le_ampleChartSub hi' i I hi'I (h i' hi')

theorem pullSecs_eq (Q : Kleiman.LineBundle S x) (n : ℤ) (s : Fin m → Ω) (hgen : IsGraphGen Q n s) :
    Kleiman.pullSecs x' Q.toSubSystem =
      secOver S (IndefiniteRowSideFullHecke.Kleiman2.joinVec (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x') (graphVec x s))
        (IndefiniteRowSideFullHecke.Kleiman2.pullDeg (graphDeg n)) := by
  ext t
  rw [mem_secOver_join_iff]
  simp only [Kleiman.pullSecs, Submodule.mem_iInf]
  constructor
  · intro h i' i j hi' hi hj
    have ht := h i hi
    clear h
    induction ht using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨b, hb, l, hl, rfl⟩ := hz
      have hb' : b ∈ joinRing S x' x s i' i j :=
        pairRing_le_joinRing s i' i j (mem_pairRing_of_mem_domRing hi' hi hb)
      have hl' := graphRing_le_joinRing (x' := x') s i' hi j ((mem_sub_iff_graph Q n s hgen hi l).mp hl j hj)
      rw [mul_assoc]
      exact Subalgebra.mul_mem _ hb' hl'
    | zero => rw [zero_mul]; exact Subalgebra.zero_mem _
    | add u v _ _ hu hv => rw [add_mul]; exact Subalgebra.add_mem _ hu hv
    | smul r u _ hu =>
      rw [Algebra.smul_def, mul_assoc]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ r) hu
  · intro h i hi
    set I := Kleiman.singleChart hi with hIdef
    have hiI : i ∈ I.1 := Finset.mem_singleton_self i
    let g : Fin m → Ω := fun b => x i ^ (-n) * s b
    have hgQ : Submodule.span (Kleiman.chartRing S x I) (Set.range g) = Q.sub I := by
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨b, rfl⟩
        have hb : s b ∈ (Q.twist (Kleiman.twistSys S x n)).sub I := by
          rw [← hgen I]; exact Submodule.subset_span ⟨b, rfl⟩
        obtain ⟨y, hy, hyb⟩ := (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI (s b)).mp hb
        have : g b = y := by
          simp only [g, hyb, smul_eq_mul, zpow_neg]
          field_simp
        rw [SetLike.mem_coe, this]
        exact hy
      · intro y hy
        have hy' : x i ^ n * y ∈ Submodule.span (Kleiman.chartRing S x I) (Set.range s) := by
          rw [hgen I]
          exact (TranslateEq.mem_twist_twistSys_iff Q.toSubSystem n I hiI _).mpr ⟨y, hy, rfl⟩
        obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hy'
        rw [Submodule.mem_span_range_iff_exists_fun]
        refine ⟨a, ?_⟩
        simp only [g, Subalgebra.smul_def, smul_eq_mul] at ha ⊢
        have : ∑ b, (a b : Ω) * (x i ^ (-n) * s b) = x i ^ (-n) * ∑ b, (a b : Ω) * s b := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
        rw [this, ha, zpow_neg]
        field_simp
    obtain ⟨Q', hQ'⟩ := Q.invertible I
    rw [← hgQ] at hQ'
    obtain ⟨w, -, hgw, hsum⟩ := exists_sum_eq_one g Q' hQ'
    have hgdiv : ∀ b j, g b / g j = s b / s j := by
      intro b j
      simp only [g, zpow_neg]
      field_simp
    have hgt : ∀ j, t / g j = t * (x i ^ n * (s j)⁻¹) := by
      intro j
      simp only [g, zpow_neg]
      field_simp
    have htw : ∀ b, t * w b ∈ Kleiman.domRing S x x' i := by
      intro b
      refine mem_domRing_of_forall fun i' hi' => ?_
      have hAD : Kleiman.chartRing S x I ≤ pairRing S x' x i' i := chartRing_le_pairRing i' hi
      have hinv := mul_eq_one_of_le hAD _ Q' hQ'
      have hspan : Submodule.span (pairRing S x' x i' i)
          (Submodule.span (Kleiman.chartRing S x I) (Set.range g) : Set Ω) =
          Submodule.span (pairRing S x' x i' i) (Set.range g) := by
        apply le_antisymm
        · rw [Submodule.span_le]; exact span_subset_span hAD _
        · exact Submodule.span_mono Submodule.subset_span
      rw [hspan] at hinv
      have htD : t ∈ Submodule.span (pairRing S x' x i' i) (Set.range g) := by
        refine mem_span_of_div_mem _ _ g hinv (fun j => joinRing S x' x s i' i j) ?_ t ?_
        · intro j _
          refine joinRing_le s i' i j _ (fun a => ?_) (fun a => ?_) (fun b => ?_)
          · exact Algebra.subset_adjoin (Or.inl (Algebra.subset_adjoin (Or.inl ⟨a, rfl⟩)))
          · exact Algebra.subset_adjoin (Or.inl (Algebra.subset_adjoin (Or.inr ⟨a, rfl⟩)))
          · rw [← hgdiv]
            exact Algebra.subset_adjoin (Or.inr ⟨b, rfl⟩)
        · intro j hj
          have hsj : s j ≠ 0 := by
            intro h0; apply hj; simp [g, h0]
          rw [hgt]
          exact h i' i j hi' hi hsj
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp htD
      rw [← hc, Finset.sum_mul]
      refine Subalgebra.sum_mem _ fun a _ => ?_
      rw [Subalgebra.smul_def, smul_eq_mul, mul_assoc]
      exact Subalgebra.mul_mem _ (c a).2 (hAD (hgw a b))
    have e : t = ∑ b, t * w b * g b := by
      calc t = t * ∑ b, g b * w b := by rw [hsum, mul_one]
        _ = ∑ b, t * w b * g b := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun b _ => by ring
    rw [e]
    refine Submodule.sum_mem _ fun b _ => Submodule.subset_span ⟨t * w b, htw b, g b, ?_, rfl⟩
    rw [← hgQ]
    exact Submodule.subset_span ⟨b, rfl⟩

end Join

theorem DomEq.full : DomEq.Statement := by
  intro S _ N N' Ω _ _ x x'
  exact ⟨isDomination_iff_dominates x x', fun _ Q n m s hgen => pullSecs_eq Q n s hgen⟩

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
