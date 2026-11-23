import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAdjoinSplitHeckeGeneratorsDualsSpherical
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalHeckeConjPlaceEqDualLabelStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightCocharacterEqOfGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.Hk3

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Hk3.SysE.matched_keeps_eigen : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R t) h → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (cX c0 : List ℤ →₀ ℂ), GlobalTheory.Hk3.MatchE R t P cX c0 → ∀ (x : R.HE.H) (l : ℂ), h P c0 x = l • x → h P c0 (R.Th t (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh hhn P hg cX c0 hM x l hx
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have hX01 := (GlobalTheory.DefiniteOps.definite_ops R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX, hXo, hXn⟩
  have comm : ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg c0 (R.Th t y)).symm
  have eX : LinearMap.adjoint (hX P cX) = hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hXn.2 P hg cX
  have cX' : Commute (hX P cX) (hX P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hXn.1 P P hg hg _ _
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX P cX) B) _ _ eX.symm cX'
  have eE : LinearMap.adjoint (h P c0) = h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := hhn.2 P hg c0
  have cE : Commute (h P c0) (h P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := hhn.1 P P hg hg _ _
  have nE : Commute (h P c0) (LinearMap.adjoint (h P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h P c0) B) _ _ eE.symm cE
  have up : hX P cX (LinearMap.adjoint (R.Th t) x) = l • LinearMap.adjoint (R.Th t) x :=
    GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h P c0)
      (fun _ u => comm u) (fun _ => nX) (fun _ => nE) () l x hx
  have c1 := comm (LinearMap.adjoint (R.Th t) x)
  have c2 : R.Th t (hX P cX (LinearMap.adjoint (R.Th t) x)) = l • R.Th t (LinearMap.adjoint (R.Th t) x) := by
    exact (congrArg (R.Th t) up).trans ((R.Th t).map_smul l _)
  exact c1.symm.trans c2
