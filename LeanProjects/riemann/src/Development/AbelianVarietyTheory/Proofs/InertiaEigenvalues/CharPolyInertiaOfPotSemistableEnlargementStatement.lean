import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharPolyInertiaOfPotSemistableEnlargement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charPoly_inertia_of_potSemistable_enlargement : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (m : ℕ) (r : GE D.nd →* GL (Fin m) (D.nd.O i)), GlobalTheory.Pst.IsPstAt (D.loc (D.nd.l i)) (D.nbr i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w) → ∃ (LL' : FinExt (D.nd.l i)) (hL : (D.nbr i w hw).LL.1 ≤ LL'.1), GlobalTheory.Pst.IsPst (D.loc (D.nd.l i)) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w))))) ∧ ∀ (σ : Gw D.nd w) (hσ : (σ : GE D.nd) ∈ Ine (F := D.host.E) (D.nd.plOm.1 w)) (p : (D.nd.O i)[X]), p.map (iotaO D.nd D.naut i) = (GlobalTheory.Pst.wdAt (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) (GlobalTheory.Pst.resDec D.nd.plOm.1 (mapRep (iotaOQ D.nd D.naut i) r) w)).inePol (σ : GE D.nd) → ((p.map (D.nbr i w hw).toLL).map (IntermediateField.inclusion hL).toRingHom).map ((D.naut.iotaQC i).toRingHom.comp (algebraMap ↥LL'.1 (Om (D.nd.l i)))) = (GlobalTheory.Pst.wdPst (D.loc (D.nd.l i)) (D.naut.iotaQC i) (D.nbr i w hw) (D.nd.plOm.2 w) (D.nbr_ind i w hw) ((D.nbr i w hw).repE LL' (GlobalTheory.PstLine.upRep hL m (mapRep (D.nbr i w hw).toLL (r.comp (decS D.nd w)))))).charPol (GlobalTheory.WeilDeligne.ineIncl (D.nd.plOm.2 w) ⟨(σ : GE D.nd), hσ⟩) := by
  first | exact @GlobalTheory.PstModel.charPol_upRep_of_isPstAt | exact GlobalTheory.PstModel.charPol_upRep_of_isPstAt | (intros; apply GlobalTheory.PstModel.charPol_upRep_of_isPstAt <;> assumption)
