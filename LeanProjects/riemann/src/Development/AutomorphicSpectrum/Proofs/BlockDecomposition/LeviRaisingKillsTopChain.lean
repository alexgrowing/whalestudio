import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.InjectiveDecompositionAction
import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.FarRegularity.LKTExists
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.CreationOperators.DifferentialBoundedSupport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwLMulSelf

open Finset PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.LvChain
open CompanionTheory.D.LK (Pos)
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.LvChain

theorem adCL_mem_omU {n : ℕ} {lev : Fin n → ℕ} {p q : Fin n} (hpq : p < q) (hl : lev p = lev q) {l k : Lt n}
    (hc : adCL false p q l k ≠ 0) (hm : l ∈ omU lev) : k ∈ omU lev ∧ k ≠ l := by
  have hcase : (q = l.2.1.1 ∧ k.1 = xor false l.1 ∧ k.2.1 = (p, l.2.1.2)) ∨
      (l.2.1.2 = p ∧ k.1 = xor false l.1 ∧ k.2.1 = (l.2.1.1, q)) := by
    by_contra hn
    rw [not_or] at hn
    exact hc (by simp only [adCL, if_neg hn.1, if_neg hn.2, sub_self])
  obtain ⟨h1, h2⟩ : l.1 = false ∧ lev l.2.1.1 < lev l.2.1.2 := (mem_filter.1 hm).2
  have hne : p ≠ q := ne_of_lt hpq
  rcases hcase with ⟨e1, e0, e2⟩ | ⟨e1, e0, e2⟩
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev p < lev l.2.1.2; rw [hl, e1]; exact h2
    · rw [e] at e2; exact hne (e1.trans (congrArg Prod.fst e2)).symm
  · refine ⟨mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, fun e => ?_⟩
    · rw [e0, h1]; rfl
    · rw [e2]; show lev l.2.1.1 < lev q; rw [← hl, ← e1]; exact h2
    · rw [e] at e2; exact hne (e1.symm.trans (congrArg Prod.snd e2))

theorem Lv_single_omU : ∀ (n : ℕ) (lev : Fin n → ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (u : V),
    (∀ a b : Fin n, a < b → kA E1 E2 a b u = 0) → ∀ p q : Fin n, p < q → lev p = lev q →
      Lv lev E1 E2 p q (Pi.single (omU lev) u : Cq n V) = 0 := by
  intro n lev V _ _ E1 E2 u hu p q hpq hl
  have h1 : liftL n (kA E1 E2 p q) (Pi.single (omU lev) u : Cq n V) = 0 := by
    funext A
    rw [liftL_apply]
    by_cases e : A = omU lev
    · subst e
      rw [Pi.single_eq_same]
      exact hu p q hpq
    · rw [Pi.single_eq_of_ne e, map_zero]
      rfl
  have h2 : adLL lev false p q (Pi.single (omU lev) u : Cq n V) = 0 := by
    simp only [adLL, LinearMap.sum_apply]
    refine Finset.sum_eq_zero fun l _ => Finset.sum_eq_zero fun k _ => ?_
    split_ifs with hS
    swap
    · rfl
    by_cases hc : adCL false p q l k = 0
    · rw [hc, zero_smul]; rfl
    suffices h : creL k (annL l (Pi.single (omU lev) u : Cq n V)) = 0 by
      rw [LinearMap.smul_apply, Module.End.mul_apply, h, smul_zero]
    funext B
    by_contra h
    obtain ⟨-, h3⟩ := creL_ne h
    obtain ⟨-, h4⟩ := annL_ne h3
    have e : insert l (B.erase k) = omU lev := by
      by_contra h'
      exact h4 (Pi.single_eq_of_ne h' _)
    have hm : l ∈ omU lev := e ▸ mem_insert_self _ _
    obtain ⟨hk, hkl⟩ := adCL_mem_omU hpq hl hc hm
    rw [← e] at hk
    rcases mem_insert.1 hk with h5 | h5
    · exact hkl h5
    · exact notMem_erase _ _ h5
  show liftL n (kA E1 E2 p q) _ + adLL lev false p q _ = 0
  rw [h1, h2, add_zero]

end GlobalTheory.CompanionTheory.LvChain
