import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGLocModel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGVanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BDataOfR
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CorankRelation
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.VanishingOrbitalPoints
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalInvariants
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormChainLemmas
import Formalism.HermitianCurvature.HeisenbergConjugationMeasurePreserving
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.NormGramAtOrigin
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StepPinExistsOfPlace
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGPinLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FormRelHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NmlInvHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NormalCount
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PointUniformity
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.NGHTie

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.NGLeaves

open Formalism.BasicNotions Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic

theorem ranks_of_dictionary (hD : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (D : D7) :
    Formalism.MainNotions.NonGenericAndKTwoTheorems.Conclusion1 D 39 := fun hk =>
  Formalism.L2.SG.NGDict.local_counting_bound_thirty_nine _ _ hk (Formalism.L2.SG.Pf.glue_constant_thirty_nine _ _) (hD _ _ hk)

theorem nondegenerate_gram_tuple : NondegenerateGramTuple := by
  intro D X
  have hn : 2 * D.R.rS + 2 ≤ X.B.I.n := by
    rw [X.n_eq]
    have h1 := D.R.rS_two
    have h2 := D.R.r_eq
    have h3 := D.R.k_ge
    omega
  have hH : ∀ i j, star (X.B.I.J j i) = X.B.I.J i j := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm i) j
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply] at this
    exact this
  obtain ⟨X0, hX⟩ := exists_nondegenerate X.B.I.E X.B.I.n (2 * D.R.rS + 2) hn X.B.I.J hH X.B.I.J_det
  refine ⟨X0, ?_⟩
  have e : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.gramE X.B.I.cm.sig X.B.I.J X0 = PI.NormGramAtOrigin.gram (starRingEnd _) X.B.I.J X0 := by
    ext a b; rfl
  rw [e]; exact hX

theorem rowNGC_of_leaves
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hNml : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv) (hNC : Formalism.L2.SG.NGCut.NormalInvariants.NormCount)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hPt : Formalism.L2.SG.Pf.BDat.PtUnif)
    (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r)
    (hX : NondegenerateGramTuple) (hB : StepChoiceConstantsC) (hE : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC)
    (hFam : Formalism.L2.SG.NGLocModel.StepFamC) : Formalism.L2.SG.RowsConc.RowNGC :=
  Formalism.L2.SG.NGLocModel.rowNGC_of_fam Formalism.FourierDecayAlt.Final.pn_rowNGJoint Formalism.FourierDecayAlt.P.norm_chain (ranks_of_dictionary hDict) hX
    hB hE (Formalism.L2.SG.NGVanish.stepTermVanish_of_form hF) hFam
    (Formalism.L2.SG.Pf.BDatR.stepThmBPinnedC_ofR hB3 hAmp hPt hRB) Formalism.L2.SG.NGCut.CorankRelation.corankOne_equivalence_holds
    (Formalism.L2.SG.NGCut.NormalInvariants.stepNormals_of hNml hNC (Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepNormOne_of_ooVanish hOV))
    (Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepPoints_of_ooVanish hOV) (Formalism.L2.SG.NGCut.VanishingOrbitalPoints.stepNormOne_of_ooVanish hOV)

theorem rowNGC_of_leaves'
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hNml : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv) (hNC : Formalism.L2.SG.NGCut.NormalInvariants.NormCount)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hPt : Formalism.L2.SG.Pf.BDat.PtUnif)
    (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r)
    (hB : StepChoiceConstantsC) (hE : StepPinExists) (hF : Formalism.L2.SG.NGVanish.FormNGC)
    (hFam : Formalism.L2.SG.NGLocModel.StepFamC) : Formalism.L2.SG.RowsConc.RowNGC :=
  rowNGC_of_leaves hOV hNml hNC hB3 hAmp hPt hRB hDict nondegenerate_gram_tuple hB hE hF hFam

theorem rowNGC_of_leaves2
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hNml : Formalism.L2.SG.NGCut.NormalInvariants.NmlInv) (hNC : Formalism.L2.SG.NGCut.NormalInvariants.NormCount)
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hPt : Formalism.L2.SG.Pf.BDat.PtUnif)
    (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r)
    (hB : StepChoiceConstantsC) (hPl : Formalism.L2.SG.NGPin.PlaceHaar) (hF : Formalism.L2.SG.NGVanish.FormRelC)
    (hG6 : ∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9) (hH : Formalism.L2.SG.FamDefs.HTie)
    (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG) (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric)
    (hE : Formalism.L2.SG.FamDefs.ExistNG) : Formalism.L2.SG.RowsConc.RowNGC :=
  rowNGC_of_leaves' hOV hNml hNC hB3 hAmp hPt hRB hDict hB (Formalism.L2.SG.NGPin.stepPinExists_of_place hPl)
    (Formalism.L2.SG.NGVanish.formNGC_of_rel hF) (Formalism.L2.SG.FamDefs.stepFamC_of hG6 hH hG5 hW hG4 hE)

theorem rowNGC_of_leaves3
    (hOV : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word),
      Formalism.L2.SG.TermOp.KExpCut.OOVanish (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') (X := X))
    (hB3 : Formalism.L2.SG.ThmBUseR.JointNormBoundRotatedUniform) (hAmp : Formalism.L2.SG.Pf.BDat.AmpUnif) (hRB : Formalism.L2.SG.Pf.BDatR.RowBDataUnifR)
    (hDict : ∀ k r : ℕ, 4 * r + 7 ≤ k → Formalism.L2.SG.NGDict.DictAll k r) (hB : StepChoiceConstantsC)
    (hG6 : ∀ D : D7, 4 * D.R.rS + 7 ≤ D.R.k → Formalism.L2.SG.FamDefs.LocalLowerBoundAllCosets D.R.k D.R.rS 9)
    (hHP : Formalism.L2.SG.NGHTie.HTPlace) (hHD : Formalism.L2.SG.NGHTie.HTDelta) (hHT : Formalism.L2.SG.NGHTie.HTTheta)
    (hG5 : Formalism.L2.SG.FamDefs.OrbitFamilyIdentityNonGeneric) (hW : Formalism.L2.SG.FamDefs.WeightsNG) (hG4 : Formalism.L2.SG.FamDefs.ProductStructureNonGeneric)
    (hE : Formalism.L2.SG.FamDefs.ExistNG) : Formalism.L2.SG.RowsConc.RowNGC :=
  rowNGC_of_leaves' hOV Formalism.L2.SG.NGCut.NormalVectorPairings.NmlInv_holds Formalism.L2.SG.NGCut.NormalCount.NormCount_holds hB3 hAmp Formalism.L2.SG.PointUniformity.ptUnif' hRB hDict hB
    Formalism.L2.SG.NGPin.stepPinExists Formalism.L2.SG.Pf.formNGC_holds
    (Formalism.L2.SG.FamDefs.stepFamC_of hG6 (Formalism.L2.SG.NGHTie.hTie_of hHP hHD hHT) hG5 hW hG4 hE)

end Formalism.L2.SG.NGLeaves
