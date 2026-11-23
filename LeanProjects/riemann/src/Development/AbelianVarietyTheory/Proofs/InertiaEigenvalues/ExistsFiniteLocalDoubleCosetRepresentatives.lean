import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ForallExistsTransfer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

noncomputable section

namespace GlobalTheory.LocalRepsFin

theorem exists_isCosetRep_finIdem : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (v : HeightOneSpectrum (𝓞 D.host.F)) (f : AE D), IsFinIdem D v f → ∀ α : GA D V, SuppF V f α → ∃ C : Finset (GA D V), (∀ γ ∈ C, SuppF V f γ) ∧ IsCosetRep V {k | k ∈ levG V β L ∧ SuppF V f k} α C := by
  intro D V β L v f hf α hα
  obtain ⟨ε, hε, rfl⟩ := hf
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hG : ∀ g, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g → g ∈ GfC V := fun g hg =>
    GlobalTheory.IdemSupport.mem_GfC_of_suppF V (GlobalTheory.IdemSupport.place_comp hΦ hε).1 hg
  let S : Subgroup (GA D V) := GlobalTheory.IdemSupport.suppGroup V (algebraMap _ (Formalism.L2.Theta.AE D) ε)
  have hS : ∀ g, g ∈ S ↔ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) g := fun _ => Iff.rfl
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨R, r1, r2⟩ := GlobalTheory.HeckeLabels.exists_reps (GlobalTheory.HeckeLabels.relIndex_conj_ne_zero (L := S)
    (GlobalTheory.ParahoricCompact.isCompact_levG V β L) (GlobalTheory.ParahoricCompact.isOpen_comap_lev V β L)
    (fun k hk hk' => ⟨hG k ((hS k).1 hk), hk'⟩) ((hS α).2 hα))
  have hK : {k | k ∈ levG V β L ∧ SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) k} =
      (levG V β L ⊓ S : Subgroup (GA D V)) :=
    Set.ext fun k => and_congr_right fun _ => (hS k).symm
  have r0 : ∀ γ ∈ R, SuppF V (algebraMap _ (Formalism.L2.Theta.AE D) ε) γ := fun γ hγ => by
    obtain ⟨a, ha, b, hb, rfl⟩ := r1 γ hγ
    exact (hS _).1 (mul_mem (mul_mem ha.2 ((hS α).2 hα)) hb.2)
  rw [hK]
  exact ⟨R, r0, fun γ hγ => ⟨hG γ (r0 γ hγ), r1 γ hγ⟩, r2⟩

end GlobalTheory.LocalRepsFin
