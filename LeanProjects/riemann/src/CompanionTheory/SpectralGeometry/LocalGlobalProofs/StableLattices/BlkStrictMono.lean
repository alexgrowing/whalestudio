import Mathlib
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.CapelliDeterminantBlockProduct
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

open Finset

noncomputable section

namespace GlobalTheory.CompanionTheory.ZetaHighest

open CompanionTheory.D.DSIC Formalism.REAL

variable {n : ℕ}

theorem blk_strictMono (ε : Fin n → Bool) (s : Bool) : StrictMono (blk ε s) :=
  ((univ.filter fun a => ε a = s).orderEmbOfFin rfl).strictMono

theorem blk_mem (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) : ε (blk ε s i) = s := by
  have h := Finset.orderEmbOfFin_mem (univ.filter fun a => ε a = s) rfl i
  exact (Finset.mem_filter.1 h).2

theorem blk_surj (ε : Fin n → Bool) (s : Bool) (a : Fin n) (h : ε a = s) : ∃ i, blk ε s i = a := by
  have h1 : a ∈ Set.range ((univ.filter fun a => ε a = s).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    simpa using h
  exact h1

theorem prod_blk (ε : Fin n → Bool) (s : Bool) (f : Fin n → ℂ) :
    ∏ i, f (blk ε s i) = ∏ a ∈ univ.filter (fun a => ε a = s), f a := by
  refine Finset.prod_bij (fun i _ => blk ε s i) ?_ ?_ ?_ ?_
  · intro i _; simp [blk_mem]
  · intro i _ j _ h; exact (blk_strictMono ε s).injective h
  · intro a ha
    obtain ⟨i, hi⟩ := blk_surj ε s a (Finset.mem_filter.1 ha).2
    exact ⟨i, mem_univ _, hi⟩
  · intro i _; rfl

theorem card_below (ε : Fin n → Bool) (s : Bool) (i : Fin (nb ε s)) :
    (univ.filter fun b => b < blk ε s i ∧ ε b = ε (blk ε s i)).card = i := by
  rw [← Fin.card_Iio i]
  symm
  refine Finset.card_bij (fun j _ => blk ε s j) ?_ ?_ ?_
  · intro j hj
    simp only [mem_filter, mem_univ, true_and, blk_mem, and_true]
    exact blk_strictMono ε s (Finset.mem_Iio.1 hj)
  · intro i _ j _ h; exact (blk_strictMono ε s).injective h
  · intro a ha
    have ha' := (Finset.mem_filter.1 ha).2
    obtain ⟨j, hj⟩ := blk_surj ε s a (ha'.2.trans (blk_mem ε s i))
    refine ⟨j, Finset.mem_Iio.2 ?_, hj⟩
    rw [← (blk_strictMono ε s).lt_iff_lt, hj]
    exact ha'.1

theorem card_total (ε : Fin n → Bool) (c : Fin n) :
    ((univ.filter fun b => c < b ∧ ε b = ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b = ε c).card : ℝ) +
      ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) + 1
      = n := by
  have h1 : (1 : ℝ) = ∑ b : Fin n, if b = c then 1 else 0 := by simp
  have h2 : (n : ℝ) = ∑ _b : Fin n, (1 : ℝ) := by simp
  rw [h2]
  conv_lhs => rw [h1]
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · by_cases e : ε b = ε c <;> simp [h, h.ne, not_lt.2 h.le, e]
  · simp [h]
  · by_cases e : ε b = ε c <;> simp [h, h.ne', not_lt.2 h.le, e]

theorem card_other (ε : Fin n → Bool) (c : Fin n) (hc : ε c = true) :
    ((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) + ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ)
      = nb ε false := by
  unfold nb
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases lt_trichotomy b c with h | h | h
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]
  · simp [h, hc]
  · cases e : ε b <;> simp [h, not_lt.2 h.le, hc]

theorem wt_false (ε : Fin n → Bool) (c : Fin n) (hc : ε c = false) :
    wtA (A1 ε) c = -((univ.filter fun b => c < b ∧ ε b ≠ ε c).card : ℝ) := by
  have h1 : ((A1 ε).filter fun i => i.1.1 = c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ h => ?_
    have := i.2.1
    rw [h, hc] at this
    exact Bool.false_ne_true this
  have h2 : ((A1 ε).filter fun i => i.1.2 = c).card = (univ.filter fun b => c < b ∧ ε b ≠ ε c).card := by
    refine Finset.card_bij (fun i _ => i.1.1) ?_ ?_ ?_
    · intro i hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi ⊢
      refine ⟨hi.2 ▸ hi.1, ?_⟩
      rw [i.2.1, hc]; simp
    · intro i hi j hj h
      simp only [A1, mem_filter, mem_univ, true_and] at hi hj
      exact Subtype.ext (Prod.ext h (hi.2.trans hj.2.symm))
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      refine ⟨⟨(a, c), ?_, hc⟩, ?_, rfl⟩
      · have := ha.2; rw [hc] at this; simpa using this
      · simp only [A1, mem_filter, mem_univ, true_and]
        exact ⟨ha.1, trivial⟩
  unfold wtA
  rw [h1, h2]; simp

theorem wt_true (ε : Fin n → Bool) (c : Fin n) (hc : ε c = true) :
    wtA (A1 ε) c = ((univ.filter fun b => b < c ∧ ε b ≠ ε c).card : ℝ) := by
  have h1 : ((A1 ε).filter fun i => i.1.2 = c) = ∅ := by
    refine Finset.filter_eq_empty_iff.2 fun i _ h => ?_
    have := i.2.2
    rw [h, hc] at this
    exact Bool.false_ne_true this.symm
  have h2 : ((A1 ε).filter fun i => i.1.1 = c).card = (univ.filter fun b => b < c ∧ ε b ≠ ε c).card := by
    refine Finset.card_bij (fun i _ => i.1.2) ?_ ?_ ?_
    · intro i hi
      simp only [A1, mem_filter, mem_univ, true_and] at hi ⊢
      refine ⟨hi.2 ▸ hi.1, ?_⟩
      rw [i.2.2, hc]; simp
    · intro i hi j hj h
      simp only [A1, mem_filter, mem_univ, true_and] at hi hj
      exact Subtype.ext (Prod.ext (hi.2.trans hj.2.symm) h)
    · intro a ha
      simp only [mem_filter, mem_univ, true_and] at ha
      refine ⟨⟨(c, a), hc, ?_⟩, ?_, rfl⟩
      · have := ha.2; rw [hc] at this; simpa using this
      · simp only [A1, mem_filter, mem_univ, true_and]
        exact ⟨ha.1, trivial⟩
  unfold wtA
  rw [h1, h2]; simp

theorem gam_false (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε false)) :
    gam ε lam (blk ε false i) = lam (blk ε false i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by
  have h1 := card_total ε (blk ε false i)
  have h2 := wt_false ε _ (blk_mem ε false i)
  have h3 := card_below ε false i
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith

theorem gam_true (ε : Fin n → Bool) (lam : Fin n → ℝ) (i : Fin (nb ε true)) :
    gam ε lam (blk ε true i) = lam (blk ε true i) - ((n : ℝ) - 1) / 2 + (nb ε false : ℝ) + (i : ℕ) := by
  have h1 := card_total ε (blk ε true i)
  have h2 := wt_true ε _ (blk_mem ε true i)
  have h3 := card_below ε true i
  have h4 := card_other ε _ (blk_mem ε true i)
  simp only [gam, PI.UpqRep.lowK, PI.UpqRep.rhoN, PI.UpqRep.rhoC, Pi.add_apply, Pi.sub_apply]
  rw [h2]
  rw [h3] at h1 ⊢
  linarith

theorem block_eigen (ε : Fin n → Bool) (s : Bool) (μ : Fin n → ℝ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (F : Fin n → Fin n → Module.End ℂ V) (x : V) (hF : KRel ε F) (hx : KHighest ε F μ x) (u : ℂ) :
    qminor F (blk ε s) (blk ε s) u x = (∏ i : Fin (nb ε s), (u - (i : ℂ) + (μ (blk ε s i) : ℂ))) • x := by
  have inj : ∀ i j, blk ε s i = blk ε s j ↔ i = j := fun i j => (blk_strictMono ε s).injective.eq_iff
  have hgl : GlRel (fun i j => F (blk ε s i) (blk ε s j)) := by
    intro a b c d
    have := hF (blk ε s a) (blk ε s b) (blk ε s c) (blk ε s d) (by simp [blk_mem]) (by simp [blk_mem])
    simpa only [inj] using this
  have hw : IsHW (fun i j => F (blk ε s i) (blk ε s j)) (fun i => (μ (blk ε s i) : ℂ)) x :=
    ⟨fun a => hx.1 _, fun a b h => hx.2 _ _ (blk_strictMono ε s h) (by simp [blk_mem])⟩
  have hq : qminor F (blk ε s) (blk ε s) u = qdet (fun i j => F (blk ε s i) (blk ε s j)) u := by
    simp only [qdet, qminor, Tm, inj, id]
  rw [hq]
  exact qDetHW V _ _ _ x hgl hw u

theorem zetaHW : CompanionTheory.D.DSIC.ZetaHW := by
  intro n ε lam V _ _ F x hF hx Y
  unfold zeta
  rw [Module.End.mul_apply, block_eigen ε true _ V F x hF hx, map_smul, block_eigen ε false _ V F x hF hx,
    smul_smul]
  congr 1
  have e1 : ∀ i : Fin (nb ε true), (Y + ((n : ℂ) - 1) / 2 - (nb ε false : ℂ) - (i : ℂ) +
      (gam ε lam (blk ε true i) : ℂ)) = Y + lam (blk ε true i) := by
    intro i; rw [gam_true]; push_cast; ring
  have e2 : ∀ i : Fin (nb ε false), (Y + ((n : ℂ) - 1) / 2 - (i : ℂ) +
      (gam ε lam (blk ε false i) : ℂ)) = Y + lam (blk ε false i) := by
    intro i; rw [gam_false]; push_cast; ring
  simp only [e1, e2]
  rw [prod_blk ε true fun a => Y + (lam a : ℂ), prod_blk ε false fun a => Y + (lam a : ℂ), Formalism.QuantumDeterminants.capP,
    ← Finset.prod_filter_mul_prod_filter_not univ (fun a => ε a = true)]
  simp only [Bool.not_eq_true]

end GlobalTheory.CompanionTheory.ZetaHighest
