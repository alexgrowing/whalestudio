import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsStageTrivialTwist
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UpNeNSOfUpNe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjPlNeOfIsSplit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainEachStepSplitPlaceWithoutExcludedParamsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw

theorem stepLam_of_ns : ∀ D : D7, SoftQ D → UpParQ D → UpQ D → QOfVal D → UpVal D → StepExactNS D → LFull D → Restore D → StepLam D := by
  intro D h1 h2 h3 h4 h5 h6 h7 h8
  intro hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' m X hX mR hmR φ v hv H₀ hH₀ hκ B hB u₁ hu hq
  obtain ⟨H, -, hH, -, hL, hol⟩ := h7 c hw.com B hB k hk
  obtain ⟨r1, -, r2, r3⟩ := h8 hG c w hw k hk s s' hs hs' p hp
  have hinv := GlobalTheory.ChainTw.invFam_bounded D c w hw k hk.le s hs u₁ B hu hB
  have hns := GlobalTheory.T.chain_each_step_splitPlace_without_excludedParams D c hw.com c.S subset_rfl B hB hinv k hk
  have hKF : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hv.1, rfl⟩
  have ex := fun u₂ => h6 hG c w hw k hk s s' hs hs' p hp ipD ip hM m X hX mR hmR φ v hv u₁ u₂ _ hu hq hns _ hol
  simp only [GlobalTheory.ChainTw.Check.const_eq w k p m X mR φ v _ H H₀ (r1 H H₀ hH hH₀) r2 r3] at ex
  have hne : p.up φ (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) ≠ 0 := fun h0 => by
    have e := ex u₁
    rw [h0] at e
    have z : s'.pet 0 0 = 0 := by simp [PiLocalization₂.pet, Lift.pet]
    rw [z] at e
    rcases mul_eq_zero.1 e.symm with e | e
    · exact mul_ne_zero hκ hL ((map_eq_zero _).1 e)
    · have := hM.pos u₁ hu.1
      rw [e] at this
      simp at this
  obtain ⟨v1, v2⟩ := h5 hG c w hw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ _ hKF
  obtain ⟨w₀, hw0, hadj⟩ := v1 ⟨u₁, hne⟩
  refine ⟨w₀, hw0, hadj, fun x₁ hx₁ => ?_⟩
  have e1 := v2 w₀ hadj u₁ x₁ hx₁
  refine ⟨?_, ?_, fun u₂ x₂ hx₂ => ?_⟩
  · exact (h1 c w hw (k + 1) hk s' hs').2.2.2 x₁ w₀ _ (e1 ▸ hne) (e1 ▸ h2 hG c w hw k hk s s' hs hs' p hp u₁ _ φ hu _ hKF hne)
  · exact (h4 c w hw (k + 1) hk s' hs').1 x₁ w₀ (e1 ▸ hne) (e1 ▸ h3 hG c w hw k hk s s' hs hs' p hp u₁ φ hq _ hKF)
  · have e := ex u₂
    rw [e1, v2 w₀ hadj u₂ x₂ hx₂] at e
    rw [← e]
    exact (hM'.schur x₁ x₂ w₀ w₀).symm

end GlobalTheory.ChainTw

end
