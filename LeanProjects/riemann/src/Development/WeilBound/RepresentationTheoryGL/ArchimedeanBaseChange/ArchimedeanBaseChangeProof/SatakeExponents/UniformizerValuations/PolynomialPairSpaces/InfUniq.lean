import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.InfParts

noncomputable section

open Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.F.LemDd.InfinitesimalUniqueness

theorem prod_X_add_C_eq (m : Multiset ℂ) :
    (m.map fun x => (X + C x : ℂ[X])).prod = ((m.map fun x => -x).map fun a => (X - C a : ℂ[X])).prod := by
  rw [Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp [sub_eq_add_neg]

theorem eval_prod_X_add_C (m : Multiset ℂ) (u : ℂ) :
    ((m.map fun x => (X + C x : ℂ[X])).prod).eval u = (m.map fun x => u + x).prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro x _
  simp

theorem eq_of_prod_eq (m m' : Multiset ℂ) (h : ∀ u : ℂ, (m.map fun x => u + x).prod = (m'.map fun x => u + x).prod) :
    m = m' := by
  have hP : (m.map fun x => (X + C x : ℂ[X])).prod = (m'.map fun x => (X + C x : ℂ[X])).prod := by
    apply Polynomial.funext
    intro u
    rw [eval_prod_X_add_C, eval_prod_X_add_C, h u]
  rw [prod_X_add_C_eq, prod_X_add_C_eq] at hP
  have hr := congrArg Polynomial.roots hP
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

end PositivityTheory.Rg.BcB.F.LemDd.InfinitesimalUniqueness

namespace PositivityTheory.Rg.BcB.F.LemDd

theorem InfUniq_holds : InfUniq := by
  intro E _ _ _ N V τ m m' hV h h'
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  apply InfinitesimalUniqueness.eq_of_prod_eq
  intro u
  have e := (h.2 u φ hφ).symm.trans (h'.2 u φ hφ)
  exact smul_left_injective ℂ hφ0 e

end PositivityTheory.Rg.BcB.F.LemDd

end
