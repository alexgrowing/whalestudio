import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridLocalTensorPlacesOverSplitPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.AdelicU

namespace GlobalTheory.LocPlTau

theorem exists_splitPrime_locPl : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}
    (_hL : L.Is μ₀) (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)), (∃ w ∈ locPl G t, w.under (𝓞 D.host.F) = v) →
    ∃ τ : D.host.E →ₐ[D.host.F] Fv D.host.F v, ∀ w ∈ locPl G t, w.under (𝓞 D.host.F) = v → splitPrime τ = w := by
  intro D T L sc G μ₀ hL t v ⟨w, hw, hv⟩
  subst hv
  obtain ⟨τ⟩ := GlobalTheory.LocPlSplit.locPl_split hL t w hw
  have hc := GlobalTheory.AdelicU.isCMExt_host D
  have hex : ∃ ρ : D.host.E →ₐ[D.host.F] Fv D.host.F (w.under (𝓞 D.host.F)), splitPrime ρ = w := by
    by_cases e : w = splitPrime τ
    · exact ⟨τ, e.symm⟩
    · exact (existsUnique_splitPrime_eq hc e rfl (splitPrime_under τ)).exists
  obtain ⟨ρ, hρ⟩ := hex
  exact ⟨ρ, fun w' hw' h => hρ.trans (GlobalTheory.FunObj.Good.under_injOn hL G t hw hw' h.symm)⟩

end GlobalTheory.LocPlTau
