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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainSplittingCharactersResidueUnramifiStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitProjectionUnderEqResidueCardEqAbsNormStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TameLiftResidueCharacterIsTameNotUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LiftsCharOfResidueCharAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTopologicalIsoParahoricChartSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ParahoricChartIntegralGLEqLatticeStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightSplitPlaceChartBiInvariantTorusValStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainChartParahoricEqLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelCharacterOnParahoricChartImageStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt

namespace GlobalTheory.ChartTwist

theorem chart_dict : ∀ D : D7, ForStageQ D fun c w j s => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → v = PP.under (𝓞 D.host.F) ∧ GlobalTheory.SplitWeil.resCard (Fv D.host.F v) = Ideal.absNorm PP.asIdeal ∧ (∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → GlobalTheory.SplitWeil.IsTame ξl ∧ ¬ GlobalTheory.SplitWeil.IsUnram ξl) ∧ (∀ k < D.R.m, ∀ μ : (Fv D.host.F v)ˣ →* ℂˣ, ((∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chS (k + 1) x)) ∨ (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μ y = Circle.toUnits (c.chT (k + 1) x))) → LiftsChar φ PP μ (w.ξ PP)) ∧ ∀ ι, IsChart s j φ ι → (∃ e : GL (Fin D.R.r ⊕ Blocks j D.R.t) (Fv D.host.F v) ≃ₜ* GlobalTheory.FinZeta.Gv s.V v, (∀ y, ι y = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v (e y)) ∧ (∀ y, e y ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig s.V.gram s.Λ v ↔ y ∈ GlobalTheory.SplitWeil.KO (Fv D.host.F v) _) ∧ ∀ x ϖ, IsLocUnif φ x ϖ → GlobalTheory.ParHecke.IsHgt ϖ fun y => GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV s.V s.Λ v (e y)) ∧ (∀ y, ι y ∈ Lev.levG s.V s.β s.L ↔ y ∈ parahoric (Fv D.host.F v) _ _) ∧ ∀ ξl, LiftsChar φ PP ξl (w.ξ PP) → ∀ y ∈ parahoric (Fv D.host.F v) _ _, ∀ d : (Fv D.host.F v)ˣ, (d : Fv D.host.F v) = y.1.toBlocks₂₂.det → Lev.levChi s.V s.β s.L (ι y) = (((ξl d)⁻¹ : ℂˣ) : ℂ) := by
  intro D c w hw j hj s hs PP hPP v φ hφ
  have hpl := GlobalTheory.T.split_projection_under_eq_residue_card_eq_absNorm D v φ PP hφ
  refine ⟨hpl.1, hpl.2, fun ξl h => GlobalTheory.T.tame_lift_residue_character_isTame_not_unramified D v φ PP (w.ξ PP) hφ (hw.ne PP hPP) ξl h, ?_, ?_⟩
  · intro k hk μ hμ
    have hres := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hw.com k hk
    have hPg : PP ∈ c.Pg := by
      classical
      rw [hw.union]; exact Finset.mem_union.2 (Or.inr hPP)
    have hq : (c.chi (k + 1) PP)⁻¹ = w.ξ PP := by rw [hw.chiQ (k + 1) PP hPP, inv_inv]
    rcases hμ with hμ | hμ
    · exact GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ (hq ▸ (hres.1 PP hPg).1) v φ hφ μ hμ
    · exact GlobalTheory.T.liftsChar_of_residueChar_at_splitPlace D _ PP _ (hq ▸ (hres.1 PP hPg).2) v φ hφ μ hμ
  · intro ι hι
    have hfl := hs.choose_spec.2
    obtain ⟨e, he⟩ := GlobalTheory.T.exists_topological_iso_parahoric_chart_split_place D s j v φ ι hfl.selfDual hfl.frame hι
    refine ⟨⟨e, he, GlobalTheory.T.parahoric_chart_integral_GL_eq_lattice_stabilizer D s j v φ ι hfl.selfDual hfl.frame hι e he, GlobalTheory.T.doublingHeight_splitPlaceChart_biInvariant_torus_value D s j v φ ι hfl.selfDual hfl.frame hι e he⟩,
      GlobalTheory.T.twisted_chain_chart_parahoric_eq_level D c w hw j hj s hs PP hPP v φ hφ ι hι, ?_⟩
    intro ξl hξ y hy d hd
    exact GlobalTheory.T.level_character_on_parahoric_chart_image D c w hw j hj s hs PP hPP v φ hφ ι hι ξl hξ y hy d hd

end GlobalTheory.ChartTwist
