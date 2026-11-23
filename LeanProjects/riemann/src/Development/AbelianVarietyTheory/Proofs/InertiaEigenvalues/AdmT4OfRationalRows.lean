import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.VpBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetHypOfIsTripleOfGalHodge
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.TwistSeries
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.HkSupSizedOfHkSup
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeValueIntegrality
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLatticeConditionOfSeriesComparisonUniversal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmT4OfRootsInFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UniversalTwistedSeriesDistributionOfCompatibilitStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemLevelTypeFormsOfUniversalCoeffReading
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisInputs
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupLawsOfSides
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LawsOfSerSide
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HkSSOfSides
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnivSupOfXi
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiType

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs

theorem levelOf_of_serSide {D : D7} {X : RealSide D} {E : IntegralHeckeForms.XD D} (Y : SerSide X E) : Y.Z.ρ.LevelOf D.nexp :=
  ⟨fun i j b g => (Y.Z.tie i j b).U_eq g, fun i j b u hu => (Y.Z.tie i j b).psiU_eq u hu⟩

theorem inputs_of_sides : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator →
    ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), ∀ G : GalSide D,
      (∀ i, D.ntw.NonzeroIndexPlace i → ∀ j b, RatRow Y.YS X.geo.v₀ Y.Z.good i j b) → XiBdd Y.Z.rd →
      (∀ j, GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt X.core X.R.toRealDat j) → GlobalTheory.TripleLocal.GalHodge D G.wd →
      (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange) →
      ∃ N0, Inputs D E N0 := by
  intro hCh hArt hTor D X E Y G hRat hBdd hSup hHodge hRoots
  obtain ⟨a1, a2, a8, good, sig, ⟨N0, a9⟩, a10, hyp⟩ := GlobalTheory.TwGalInputs.galois_inputs hCh hArt hTor D G hHodge
  have hL : Laws Y.Z.good Y.Z.rd := laws_of_serSide D X E Y hRat
  have hXi : XiType Y.Z.rd := GlobalTheory.XiTypeProof.xiType D Y.Z.ρ Y.Z.good Y.Z.rd hL.faithful hL.act (levelOf_of_serSide Y)
  obtain ⟨supG, supFull, supHk, commG, comm⟩ := supLaws_of_sides D X E Y hSup
  exact ⟨N0,
    { a1 := a1
      a2 := a2
      a8 := a8
      good := good
      sig := sig
      a9 := a9
      a10 := a10
      univChar := Y.Z.univ
      off := Y.off
      rel := GlobalTheory.T.universalTwistedSeriesDistribution_of_compatibility D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      l3 := GlobalTheory.SeriesTie.thetaLatticeCondition_of_fullSeriesComparison D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL
      t4 := GlobalTheory.T.admT4_of_roots_in_field D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hRoots E
      type := GlobalTheory.ExportType.typeKept_of_fullTie D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL.act E
      univ := univSup_of_xi D Y.Z.ρ Y.Z.good Y.Z.rd Y.Z.full hL hXi hBdd E
      supG := supG
      supFull := supFull
      supHk := supHk
      commG := commG
      comm := comm
      ss := GlobalTheory.TwHkSS.hkSS_of_sides D X E Y commG comm supFull
      hyp := hyp }⟩

example {D : D7} {X : RealSide D} (hX : FieldOk X) :
    ∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (Formalism.L2.Host.embLL0 D).fieldRange := hX.roots

end GlobalTheory.TwInputs
