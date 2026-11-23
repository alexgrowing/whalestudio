import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.DivCount
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootsInjective.TwoPowCardPrimeFactorsLe

open Polynomial

noncomputable section

open Classical

namespace PI.SqfRootsInj.W

open PI.SqfLab

def LS (g r n : ℕ) : Finset ℕ := n.primeFactors.filter (fun ℓ => ℓ ∉ BB r g)

def WA (g e j ℓ : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  (nthRoots ((g ^ j - 1) * Lp g e ℓ) (1 : Fbar g)).toFinset.filter
    (fun w => (minpoly (ZMod g) w).natDegree = e)

def YB (g e' : ℕ) [Fact g.Prime] : Finset (Fbar g) :=
  ((X ^ (g ^ e') - X : (Fbar g)[X]).roots.toFinset).filter
    (fun y => (minpoly (ZMod g) y).natDegree = e')

def XB (g e ℓ : ℕ) [Fact g.Prime] (y : Fbar g) : Finset (Fbar g) :=
  (nthRoots (Lp g e ℓ) ((primeToPart ℓ y) ^ Lp g e ℓ)).toFinset.filter
    (fun x => (minpoly (ZMod g) x).natDegree = e)

def SA (g r : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2), ∑ ℓ ∈ LS g r (g ^ e - 1),
    (g ^ j - 1) * Lp g e ℓ * g ^ (r - e)

def SB (g r : ℕ) : ℕ :=
  ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)), ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
    g ^ e' * Lp g e ℓ * g ^ (r - e - e')

theorem lp_pos {g e ℓ : ℕ} (hℓ : ℓ.Prime) : 0 < Lp g e ℓ := pow_pos hℓ.pos _

theorem minpoly_monic' {g : ℕ} [Fact g.Prime] (w : Fbar g) : (minpoly (ZMod g) w).Monic :=
  minpoly.monic (Algebra.IsIntegral.isIntegral w)

def PA (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 2 r, ∃ j ∈ Finset.Icc 1 (e / 2),
    ∃ ℓ ∈ LS g r (g ^ e - 1), ∃ w ∈ WA g e j ℓ, minpoly (ZMod g) w ∣ f

def PB (g r : ℕ) [Fact g.Prime] (f : (ZMod g)[X]) : Prop :=
  ∃ e ∈ Finset.Icc 1 r, ∃ e' ∈ Finset.Icc 1 (min e (r - e)),
    ∃ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∃ y ∈ YB g e', ∃ x ∈ XB g e ℓ y,
      minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f

theorem g_pow_sub_one_ne {g e : ℕ} (hg2 : 1 < g) (he : 1 ≤ e) : g ^ e - 1 ≠ 0 := by
  have := Nat.one_lt_pow (by omega : e ≠ 0) hg2
  omega

theorem caseA_PA {g r ℓ : ℕ} [hg : Fact g.Prime] {f : (ZMod g)[X]} (hℓ : ℓ.Prime)
    (hB : ℓ ∉ BB r g) (h : CaseA g r ℓ f) : PA g r f := by
  have hg2 : 1 < g := hg.out.one_lt
  obtain ⟨e, j, w, he2, her, hj1, hj2, hdv, hdeg, hdvd, hpow⟩ := h
  refine ⟨e, ?_, j, ?_, ℓ, ?_, w, ?_, hdvd⟩
  · exact Finset.mem_Icc.2 ⟨he2, her⟩
  · exact Finset.mem_Icc.2 ⟨hj1, by omega⟩
  · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2 ⟨hℓ, hdv, g_pow_sub_one_ne hg2 (by omega)⟩, hB⟩
  · refine Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_nthRoots ?_).2 hpow), hdeg⟩
    have : 1 ≤ g ^ j - 1 := by
      have := Nat.one_lt_pow (by omega : j ≠ 0) hg2
      omega
    exact Nat.mul_pos this (lp_pos hℓ)

theorem caseB_PB {g r ℓ : ℕ} [hg : Fact g.Prime] {f : (ZMod g)[X]} (hℓ : ℓ.Prime)
    (hB : ℓ ∉ BB r g) (h : CaseB g r ℓ f) : PB g r f := by
  have hg2 : 1 < g := hg.out.one_lt
  obtain ⟨e, e', x, y, he', he'e, hsum, hdv, hdx, hdy, hdvd, hy, hx⟩ := h
  refine ⟨e, ?_, e', ?_, ℓ, ?_, y, ?_, x, ?_, hdvd⟩
  · exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  · exact Finset.mem_Icc.2 ⟨he', by omega⟩
  · exact Finset.mem_filter.2 ⟨Nat.mem_primeFactors.2
      ⟨hℓ, hdv, Nat.mul_ne_zero (g_pow_sub_one_ne hg2 (by omega)) (g_pow_sub_one_ne hg2 he')⟩, hB⟩
  · refine Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ?_, hdy⟩
    have hM : 1 < g ^ e' := Nat.one_lt_pow (by omega) hg2
    rw [mem_roots (FiniteField.X_pow_card_sub_X_ne_zero _ hM)]
    simp [hy]
  · exact Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 ((mem_nthRoots (lp_pos hℓ)).2 hx), hdx⟩

theorem cardA (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PA g r)).card ≤ SA g r := by
  calc (T.filter (PA g r)).card ≤ ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2),
      ∑ ℓ ∈ LS g r (g ^ e - 1), ∑ w ∈ WA g e j ℓ,
        (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 2 r).biUnion fun e =>
          (Finset.Icc 1 (e / 2)).biUnion fun j => (LS g r (g ^ e - 1)).biUnion fun ℓ =>
            (WA g e j ℓ).biUnion fun w => T.filter (fun f => minpoly (ZMod g) w ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, j, hj, ℓ, hℓ, w, hw, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, j, hj, ℓ, hℓ, w, hw, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun j _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SA g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun j _ =>
          Finset.sum_le_sum fun ℓ _ => ?_
        calc ∑ w ∈ WA g e j ℓ, (T.filter (fun f => minpoly (ZMod g) w ∣ f)).card
            ≤ ∑ w ∈ WA g e j ℓ, g ^ (r - e) := by
              refine Finset.sum_le_sum fun w hw => ?_
              have h1 := divCount r T hmon _ (minpoly_monic' w)
              have h2 : (minpoly (ZMod g) w).natDegree = e := (Finset.mem_filter.1 hw).2
              rw [h2] at h1
              exact h1
          _ = (WA g e j ℓ).card * g ^ (r - e) := by rw [Finset.sum_const, smul_eq_mul]
          _ ≤ (g ^ j - 1) * Lp g e ℓ * g ^ (r - e) :=
              Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))

theorem cardB (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r) : (T.filter (PB g r)).card ≤ SB g r := by
  have hg2 : 1 < g := hg.out.one_lt
  calc (T.filter (PB g r)).card ≤ ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)),
      ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)), ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
        (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card := by
        refine (Finset.card_le_card (t := (Finset.Icc 1 r).biUnion fun e =>
          (Finset.Icc 1 (min e (r - e))).biUnion fun e' => (LS g r ((g ^ e - 1) * (g ^ e' - 1))).biUnion fun ℓ =>
            (YB g e').biUnion fun y => (XB g e ℓ y).biUnion fun x =>
              T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)) ?_).trans ?_
        · intro f hf
          obtain ⟨hfT, e, he, e', he', ℓ, hℓ, y, hy, x, hx, hd⟩ := Finset.mem_filter.1 hf
          simp only [Finset.mem_biUnion]
          exact ⟨e, he, e', he', ℓ, hℓ, y, hy, x, hx, Finset.mem_filter.2 ⟨hfT, hd⟩⟩
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun e' _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun ℓ _ => ?_)
        refine Finset.card_biUnion_le.trans (Finset.sum_le_sum fun y _ => ?_)
        exact Finset.card_biUnion_le
    _ ≤ SB g r := by
        refine Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun e' he' =>
          Finset.sum_le_sum fun ℓ _ => ?_
        have he1 : 1 ≤ e' := (Finset.mem_Icc.1 he').1
        calc ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y,
              (T.filter (fun f => minpoly (ZMod g) x * minpoly (ZMod g) y ∣ f)).card
            ≤ ∑ y ∈ YB g e', ∑ x ∈ XB g e ℓ y, g ^ (r - e - e') := by
              refine Finset.sum_le_sum fun y hy => Finset.sum_le_sum fun x hx => ?_
              have h1 := divCount r T hmon _ ((minpoly_monic' x).mul (minpoly_monic' y))
              have h2 : (minpoly (ZMod g) x * minpoly (ZMod g) y).natDegree = e + e' := by
                rw [(minpoly_monic' x).natDegree_mul (minpoly_monic' y),
                  (Finset.mem_filter.1 hx).2, (Finset.mem_filter.1 hy).2]
              rw [h2] at h1
              rw [Nat.sub_sub]
              exact h1
          _ = ∑ y ∈ YB g e', (XB g e ℓ y).card * g ^ (r - e - e') := by
              simp only [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ y ∈ YB g e', Lp g e ℓ * g ^ (r - e - e') :=
              Finset.sum_le_sum fun y _ => Nat.mul_le_mul_right _
                ((Finset.card_filter_le _ _).trans (card_nthRoots_toFinset_le _ _))
          _ = (YB g e').card * (Lp g e ℓ * g ^ (r - e - e')) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ g ^ e' * (Lp g e ℓ * g ^ (r - e - e')) :=
              Nat.mul_le_mul_right _ ((Finset.card_filter_le _ _).trans
                (card_roots_X_pow_sub_X_le _ (Nat.one_lt_pow (by omega) hg2)))
          _ = g ^ e' * Lp g e ℓ * g ^ (r - e - e') := by rw [mul_assoc]

theorem card_le_SA_SB (g r : ℕ) [hg : Fact g.Prime] (T : Finset (ZMod g)[X])
    (hT : ∀ f ∈ T, IsLab g r f ∧ ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∉ BB r g ∧
      (CaseA g r ℓ f ∨ CaseB g r ℓ f)) :
    T.card ≤ SA g r + SB g r := by
  have hmon : ∀ f ∈ T, f.Monic ∧ f.natDegree = r := fun f hf => ⟨(hT f hf).1.1, (hT f hf).1.2.1⟩
  have hcov : T ⊆ T.filter (PA g r) ∪ T.filter (PB g r) := by
    intro f hf
    obtain ⟨_, ℓ, hℓ, hB, hAB⟩ := hT f hf
    rcases hAB with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hf, caseA_PA hℓ hB h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hf, caseB_PB hℓ hB h⟩)
  calc T.card ≤ (T.filter (PA g r) ∪ T.filter (PB g r)).card := Finset.card_le_card hcov
    _ ≤ (T.filter (PA g r)).card + (T.filter (PB g r)).card := Finset.card_union_le _ _
    _ ≤ SA g r + SB g r := Nat.add_le_add (cardA g r T hmon) (cardB g r T hmon)

end PI.SqfRootsInj.W
