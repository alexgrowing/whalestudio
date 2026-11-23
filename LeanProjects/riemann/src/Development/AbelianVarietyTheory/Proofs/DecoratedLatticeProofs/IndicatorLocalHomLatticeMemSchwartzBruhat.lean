import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TensorOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSBExtFunEqHalfInd
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil ValuativeRel

noncomputable section

namespace GlobalTheory.LatIndSB

theorem indicator_latO_mem_SB : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (M : Lat S) (M' : Lat T), IsSelfDualC S M → IsSelfDualC T M' → ∀ (P : LocPl ψ S T M M'), Set.indicator {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} (fun _ => (1 : ℂ)) ∈ SB (Matrix P.Y P.Y' P.k) := by
  intro D ψ S T M M' hM hM' P
  classical
  have hset : {x | (ofSplit P.q).up P.FS P.FT x ∈ latO S T (M : Set _) (M' : Set _) (· = P.q.v)} =
      (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k)) := by
    obtain ⟨ε, hε, heε⟩ := GlobalTheory.FinPl.HalfInd.exists_idem P.q
    ext x
    refine ⟨fun h => GlobalTheory.PlaceModel.latO_le_top _ h, fun h => ?_⟩
    have h2 := (GlobalTheory.PlaceModel.idem_smul_mem hε P.q.split.1 heε h).1
    have hh : (ofSplit P.q).up P.FS P.FT x ∈ GlobalTheory.PlaceModel.half S T P.q.e :=
      (GlobalTheory.PlaceModel.isHalf_iff S T).1 (GlobalTheory.LocMod.Witness.up_half (ofSplit P.q) P.FS P.FT x)
    have h3 : P.q.e • (ofSplit P.q).up P.FS P.FT x = (ofSplit P.q).up P.FS P.FT x := (GlobalTheory.PlaceModel.mem_half S T).1 hh
    change P.q.e • (ofSplit P.q).up P.FS P.FT x ∈ (latO S T (M : Set _) (M' : Set _) fun w => w = P.q.v) at h2
    rw [h3] at h2
    exact h2
  rw [hset]
  have ho := GlobalTheory.LocMod.Witness.lat_open (ofSplit P.q) P.FS P.FT hM hM'
  have hc := GlobalTheory.LocMod.Witness.lat_compact (ofSplit P.q) P.FS P.FT hM hM'
  have hcl := AddSubgroup.isClosed_of_isOpen _ ho
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ?_, ?_⟩
  · by_cases hx : x ∈ (((latO S T (M : Set _) (M' : Set _) fun _ => True).comap
        (GlobalTheory.LocMod.Witness.upH (ofSplit P.q) P.FS P.FT) : AddSubgroup _) : Set (Matrix P.Y P.Y' P.k))
    · exact ⟨_, ho, hx, fun y hy => by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
    · exact ⟨_, hcl.isOpen_compl, hx, fun y hy => by rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩
  · exact HasCompactSupport.intro hc fun x hx => Set.indicator_of_notMem hx _

end GlobalTheory.LatIndSB

end
