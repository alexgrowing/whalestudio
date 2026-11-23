import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemRangeAdjointOfMemSpanEvaluationValues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainAdjointNonvanishingStep
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem upVal_of_span_adj : ∀ D : D7, SoftQ D → UpSpanQ D → UpAdjQ D → UpVal D := by
  intro D hSoft hSpan hAdj
  intro hgap c tw htw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ v hv
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := (hSoft c tw htw (k + 1) hk' s' hs').1
  have hl : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → ∀ (y : s'.CC c), ∀ w ∈ s'.KF,
      s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = ip' y x * ipD (p.It φ w) v := by
    intro u x hx y w hw
    rw [hx y]
    exact (hAdj hgap c tw htw k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)
  have key : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → p.up φ (PiLocalization₂.val u v) ≠ 0 →
      x ≠ 0 ∧ ∃ w₁, IsAdjVec p ipD ipD' φ v w₁ ∧ p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := by
    intro u x hx hF
    obtain ⟨hx0, w₁, hw₁, hFx⟩ := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c)
      (s'.CC c).subtype s'.KF ipD' ip' s'.pet hM'.hermD hM'.posD hM'.herm hM'.pos
      (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v)
      (hSpan hgap c tw htw k hk s s' hs hs' p hp u φ v hv) (hl u x hx) hF
    have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := hFx
    refine ⟨hx0, w₁, ⟨hw₁, fun w hw => ?_⟩, hFx'⟩
    have h1 := hl u x hx x w hw
    rw [hFx'] at h1
    have h2 := (hM'.schur x x w w₁).symm.trans h1
    have hxx : ip' x x ≠ 0 := fun h => by
      have := hM'.pos x hx0
      rw [h] at this
      simp at this
    exact mul_left_cancel₀ hxx h2
  refine ⟨fun ⟨u, hF⟩ => ?_, fun w₀ hw₀ u x hx => ?_⟩
  · obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
    obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
    refine ⟨w₁, fun h => hF ?_, hw₁⟩
    rw [hFx, h]
    simp
  · by_cases hF : p.up φ (PiLocalization₂.val u v) = 0
    · have h1 := hl u x hx x w₀ hw₀.1
      rw [hF, ← hw₀.2 w₀ hw₀.1] at h1
      have h0 : s'.pet (PiLocalization₂.val x w₀) (0 : GA D s'.V → ℂ) = 0 := by
        simp [PiLocalization₂.pet, Lift.pet]
      rw [h0] at h1
      rw [hF]
      rcases mul_eq_zero.mp h1.symm with h | h
      · have hx0 : x = 0 := by
          by_contra hne
          have := hM'.pos x hne
          rw [h] at this
          simp at this
        subst hx0
        first | rfl | simp [PiLocalization₂.val]
      · have hw0 : w₀ = 0 := by
          by_contra hne
          have := hM'.posD w₀ hne
          rw [h] at this
          simp at this
        subst hw0
        simp
    · obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
      have hd : w₁ = w₀ := by
        by_contra hne
        have hdK : w₁ - w₀ ∈ s'.KF := s'.KF.sub_mem hw₁.1 hw₀.1
        have hz : ipD' (w₁ - w₀) (w₁ - w₀) = 0 := by
          rw [map_sub, hw₁.2 _ hdK, hw₀.2 _ hdK, sub_self]
        have := hM'.posD _ (sub_ne_zero.mpr hne)
        rw [hz] at this
        simp at this
      rw [hFx, hd]

end GlobalTheory.ChainTw
