import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContMapRepIotaOQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

namespace GlobalTheory.PstModel

theorem charPol_upRep_of_isPstAt : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∃ (LL' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ LL'.1), GlobalTheory.Pst.IsPst (D.loc (D.nd.l i)) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))))) ∧ ∀ (σ : Gw D.nd w) (hσ : (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (p : (D.nd.O i)[X]), p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ((p.map (D.nbr i w hw).toLL).map (IntermediateField.inclusion hL).toRingHom).map ((D.naut.iotaQC i).toRingHom.comp (algebraMap ↥LL'.1 (Om (D.nd.l i)))) = (GlobalTheory.Pst.wdPst (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w)))))).charPol (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) := by
  intro D i w hw m r h
  obtain ⟨LL', r', ⟨hL, hmod⟩, hpst, hwd⟩ := GlobalTheory.Pst.wdAt_of_isPstAt (P := D.loc (D.nd.l i)) (D.naut.iotaQC i)
    (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) h
  have key : r' = GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))) := by
    ext g a b
    have h1 := congrArg (fun f => ((f g : GL (Fin m) (Om (D.nd.l i))) : Matrix (Fin m) (Fin m) (Om (D.nd.l i))) a b) hmod
    have h2 := (D.loc_tie i w hw).1 (((r g : GL (Fin m) (D.nd.O i)) : Matrix (Fin m) (Fin m) (D.nd.O i)) a b)
    simp only [mapRep, GlobalTheory.Pst.resDec, GlobalTheory.PstLine.upRep] at h1 ⊢
    simp at h1 ⊢
    exact h1.trans h2
  refine ⟨LL', hL, key ▸ hpst, ?_⟩
  intro σ hσ p hp
  rw [← key, ← hwd, ← GlobalTheory.WeilDeligne.WD.inePol_of_mem_Ine, ← hp, Polynomial.map_map, Polynomial.map_map]
  congr 1
  ext x
  have h2 := (D.loc_tie i w hw).1 x
  simp only [iotaO, iotaOQ] at h2 ⊢
  simp at h2 ⊢
  exact h2.symm

end GlobalTheory.PstModel
