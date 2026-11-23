import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyCompactSecondCountableT2
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.CuspKillProof

theorem cuspKill_holds : ∀ D : D7, CuspKill D := by
  intro D W ν hν s I hI Γ hΓQ hNΓ hnorm 𝓓 h𝓓 Φ φ hΦc hΦΓ hΦN hφ hcusp hint
  obtain ⟨i1, i2, i3⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W
  haveI : BorelSpace (GA D W) := ⟨rfl⟩
  haveI : Countable (GQ W) := GlobalTheory.AutomorphicL2Unitary.countable_of_discrete
  haveI : Countable Γ := Function.Injective.countable (Subgroup.inclusion_injective hΓQ)
  have hNc : IsClosed (NI W I : Set (GA D W)) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField D.host.F
    exact GlobalTheory.Cusp.IsoFlag.isClosed_unip _ _ _
  have hcc : GlobalTheory.Cusp.Cocompact (GQ W) (NI W I) := by
    rw [← GlobalTheory.Cusp.NA_frameFlag hI]
    exact GlobalTheory.Cusp.cocompact_single _
  haveI : LocallyCompactSpace (NI W I) := hNc.locallyCompactSpace
  have hsub : Γ.subgroupOf (NI W I) = (GQ W).subgroupOf (NI W I) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun h => hΓQ h, fun h => hNΓ ⟨x.2, h⟩⟩
  set κ : Measure (NI W I) := Measure.haar
  set 𝓝 : Set (NI W I) := GlobalTheory.AutomorphicL2Unitary.stdDom ((GQ W).subgroupOf (NI W I))
  have h𝓝Q : IsFundamentalDomain ((GQ W).subgroupOf (NI W I)) 𝓝 κ := GlobalTheory.AutomorphicL2Unitary.isFundamentalDomain_stdDom _ κ
  have h𝓝Γ : IsFundamentalDomain (Γ.subgroupOf (NI W I)) 𝓝 κ := by rw [hsub]; exact h𝓝Q
  have h𝓝t : κ 𝓝 ≠ ⊤ := hcc.measure_ne_top h𝓝Q
  have h0 : ∀ g, ∫ n in 𝓝, φ ((n : GA D W) * g) ∂κ = 0 := hcusp s I hI κ 𝓝 inferInstance h𝓝Q
  exact GlobalTheory.UnfoldNormal.unfold_zero_mean (GA D W) ν Γ (NI W I) inferInstance hNc hnorm κ 𝓝 inferInstance h𝓝Γ h𝓝t
    Φ φ hΦc.measurable hφ.cont.measurable hΦN hΦΓ (fun γ hγ g => hφ.left γ (hΓQ hγ) g) h0 𝓓 h𝓓 hint

end GlobalTheory.CuspKillProof
