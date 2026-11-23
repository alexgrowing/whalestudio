import Mathlib
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport

open Finset CompanionTheory.RgExh CompanionTheory.RgExh.U
open CompanionTheory.D.LK (Pos Cn ann cre lift bd om cpt allT LocFin)
open Formalism.REAL (GlRel KHighest IsWeight)
open CompanionTheory.D.DSIC (KUnit)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.RgExh

theorem adC_mem_omU {n : ℕ} {ε : Fin n → Bool} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hε : ε p = ε q)
    (hl : lev p = lev q) {i k : Pos n} (hc : adC p q i k ≠ 0) (hi : i ∈ omU ε lev) :
    k ∈ omU ε lev ∧ k ≠ i := by
  have hcase : (q = i.1.1 ∧ k.1 = (p, i.1.2)) ∨ (i.1.2 = p ∧ k.1 = (i.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adC, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : ε i.1.1 = ε i.1.2 ∧ lev i.1.1 < lev i.1.2 := (mem_filter.1 hi).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε p = ε i.1.2; rw [hε, e1, h1]
    · rw [e2]; show lev p < lev i.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e2]; show ε i.1.1 = ε q; rw [h1, e1, hε]
    · rw [e2]; show lev i.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem lF_single_omU : ∀ (n : ℕ) (ε : Fin n → Bool) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E : Fin n → Fin n → Module.End ℂ V) (γ : Fin n → ℝ) (u : V), KHighest ε E γ u →
    ∀ p q : Fin n, p < q → ε p = ε q → lev p = lev q →
      lF E p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
  intro n ε lev V _ _ E γ u hu p q hpq hε hl
  have hE : E p q u = 0 := hu.2 p q hpq hε
  have h1 : lift n (E p q) (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    funext A
    rw [CompanionTheory.D.LK.lift_apply]
    by_cases e : A = omU ε lev
    · subst e
      rw [Pi.single_eq_same]
      exact hE
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adL p q (Pi.single (omU ε lev) u : Cn n V) = 0 := by
    simp only [adL, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hc : adC p q i k = 0
    · rw [hc, zero_smul]
    suffices h : cre k (ann i (Pi.single (omU ε lev) u : Cn n V)) = 0 by rw [h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := CompanionTheory.D.LK.cre_ne h
    obtain ⟨-, h4⟩ := CompanionTheory.D.LK.ann_ne h3
    have e : insert i (B.erase k) = omU ε lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hi : i ∈ omU ε lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hki⟩ := adC_mem_omU hpq hε hl hc hi
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hki h5
    · exact notMem_erase _ _ h5
  show lift n (E p q) _ + adL p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.RgExh
