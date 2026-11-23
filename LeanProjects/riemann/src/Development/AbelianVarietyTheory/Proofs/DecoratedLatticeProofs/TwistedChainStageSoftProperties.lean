import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainCuspSpaceFiniteDimOfHarishChandra
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageCuspFormMapEqZeroOfValueZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelProperties
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainInnerProductsExistOfRapidDecay
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeParametersOfElementFromOneNonzeroValueStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevelStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
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

noncomputable section
namespace GlobalTheory.ChainTw
variable {D : D7}

theorem t_fd {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (hFD : FiniteDimensional ℂ ((flat c w j s hr).CC c)) :
    FiniteDimensional ℂ (s.CC c) := by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  exact @FiniteDimensional.of_injective ℂ _ _ _ _ _ _ _ ι (Submodule.inclusion_injective hle) hFD

theorem t_met {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (h : ∃ ipD ip, IsMet c (flat c w j s hr) ipD ip) :
    ∃ ipD ip, IsMet c s ipD ip := by
  obtain ⟨ipD, ipF, hm⟩ := h
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  let ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ := (ipF.comp ι).compl₂ ι
  have hι : ∀ x : s.CC c, ι x ≠ 0 ↔ x ≠ 0 := fun x => (Submodule.inclusion_injective hle).ne_iff' (map_zero ι)
  exact ⟨ipD, ip, hm.pure, hm.hermD, hm.posD, fun x y => hm.herm (ι x) (ι y),
      fun x hx => hm.pos (ι x) ((hι x).2 hx), fun x y v v' => hm.integ (ι x) (ι y) v v',
      fun x y v v' => hm.schur (ι x) (ι y) v v'⟩

theorem t_van {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0) :
    ∀ (x : s.CC c) v, v ≠ 0 → PiLocalization₂.val x v = 0 → x = 0 := by
  intro x v hv h0
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  by_contra hx
  exact (Submodule.inclusion_injective hle).ne_iff' (map_zero ι) |>.2 hx (h (ι x) v hv h0)

theorem t_par {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} {hr : D.R.r ≤ s.V.rank}
    (hle : s.CC c ≤ (flat c w j s hr).CC c)
    (h : ∀ (x : (flat c w j s hr).CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c (flat c w j s hr) (PiLocalization₂.val x v) B → IsPar x B) :
    ∀ (x : s.CC c) v B, PiLocalization₂.val x v ≠ 0 → ParFun c s (PiLocalization₂.val x v) B → IsPar x B := fun x v B hv hP => by
  let ι : s.CC c →ₗ[ℂ] (flat c w j s hr).CC c := Submodule.inclusion hle
  have h' := h (ι x) v B hv hP
  exact ⟨fun h0 => h'.1 (by rw [h0]; exact map_zero ι), fun v' hv' => h'.2 v' hv'⟩

theorem softQ_all : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := by
  intro hHC hCR D c w hw j hj s hs
  obtain ⟨hr, hL, hf⟩ := hs
  have hle : s.CC c ≤ (flat c w j s hr).CC c := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw j hj s ⟨hr, hL, hf⟩ hr
  have hMet : MetEx D := GlobalTheory.ChainMetric.metEx hCR D
  have hLev : LevFacts D := LevelFacts.levFacts D
  exact ⟨t_fd hle (finDim_of_levFacts hHC D hLev c hw.com j hj _ hf), t_met hle (hMet c hw.com j hj _ hf),
    t_van hle (val_eq_zero_imp D hMet c hw.com j hj _ hf), t_par hle (GlobalTheory.T.hecke_parameters_of_element_from_one_nonzero_value hCR D hMet hLev c hw.com j hj _ hf)⟩

example : GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SoftQ D := softQ_all

end GlobalTheory.ChainTw
end
