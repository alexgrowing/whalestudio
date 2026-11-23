import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FirstIn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.MCellone
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.FPiece
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSupportOfIsSubquotientProdIrr

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas UpperTheory.Lit.Red

theorem UpperTheory.Lit.Full.multOne :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (P : Set (IrrGL k)) (y z : IrrGL k) (N : ℕ) (hd : ∑ a, (![y, z] a).1 = N), SuppIn y P → FirstIn z Pᶜ → jm ![y, z] hd (prodIrr ![y, z] hd) ≤ 1 := by
  intro hG hBZ k _ _ _ _ P y z N hd hy hz
  refine UpperTheory.Lit.Mix.cellone hG hBZ k y z N hd fun q hq hpos hjm p hc => ?_
  by_contra hne
  obtain ⟨A, hA, hAP⟩ := hy
  obtain ⟨B, hB, w, hwB, hwP⟩ := (UpperTheory.Lit.Full.piece hG hBZ k z Pᶜ q hq hjm).1 hz hpos
  obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_hasSupport hBZ hG p
  have ht : ∀ a, HasSupport (![p, q 0] a).rep (![C, B] a) := fun a => by
    fin_cases a
    · exact hC
    · exact hB
  have hS := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (hd := hc) ht y.2.rep.irr
    (jhMult_ne_zero_iff.1 hne)
  have hE := GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG hBZ hA hS
  refine hwP (hAP w ?_)
  rw [hE, Fin.sum_univ_two]
  exact Multiset.mem_add.2 (Or.inr hwB)
