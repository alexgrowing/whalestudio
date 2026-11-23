import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.StrictJoinCandidates.IntertwiningCandidates.StrictJoin
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocIso
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.FiniteDiscreteFamilies.LocalCompatibilityGL.LocUniq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.BcB.SpectralAccumulation
open scoped Classical

set_option synthInstance.maxHeartbeats 200000

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.FX.Bo

open PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.F.RS

theorem StrictProd_holds : StrictProd := by
  intro E _ _ _ n P P' hS w
  obtain ⟨c, N, h, V, σ, m, pos, disc, loc, inf⟩ := P
  obtain ⟨c', N', h', V', σ', m', pos', disc', loc', inf'⟩ := P'
  obtain ⟨hF, hc, -⟩ := hS
  simp only at hc
  subst hc
  have key : ∀ i : Fin c, SIso (E := E) ⟨N i, V i⟩ ⟨N' i, V' i⟩ := by
    intro i
    have := (List.forall₂_iff_get.1 hF).2 i.1 (by simp [parts]) (by simp [parts])
    simpa [parts] using this
  have hN : N = N' := funext fun i => (key i).1
  subst hN
  have hσ : ∀ i, Nonempty ((σ i w).ρ.Equiv (σ' i w).ρ) := by
    intro i
    obtain ⟨hNi, hiso⟩ := key i
    have hl : IsLocCompGL (V' i) w (σ i w) := Bo.LocIso_holds E (N i) (V i) (V' i) hiso w (σ i w) (loc i w)
    exact GlobalTheory.LocGL.IrrGL.of_eq_of.1 (Bo.LocUniq_holds E (N i) (V' i) (disc' i) w _ _ hl (loc' i w))
  exact ⟨GlobalTheory.LocGL.multiProdEquiv _ fun i => (hσ i).some⟩

end PositivityTheory.Rg.BcB.F.FX.Bo

end
