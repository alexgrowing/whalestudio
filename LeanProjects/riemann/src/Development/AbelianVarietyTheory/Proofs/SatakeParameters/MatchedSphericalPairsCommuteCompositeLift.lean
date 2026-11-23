import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftLevelsGoodPrimesProperties
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigenvectorAdjointIntertwinerNormalOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspacesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperatorsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3.SysE

set_option maxHeartbeats 1000000 in

theorem matched_commute : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ SF, IsSF R SF → ∀ t P, Good R t P → ∀ cX c0, MatchE R t P cX c0 → ∀ hX, IsOpsX R t hX → (∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y)) ∧ ∀ c, ∀ w ∈ EEc R SF c, hX P cX (LinearMap.adjoint (R.Th t) w) = evC (Yc D 0) P (fun d => c P (dualLab d)) c0 • LinearMap.adjoint (R.Th t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS SF hSF t P hg cX c0 hM hX hXo
  have gd := GlobalTheory.GoodPrimes.good_primes R F hC.lev
  have hg0 : Good R A.μ0 P := (gd.2.1 t P hg).2.2
  have injE : Function.Injective R.HE.e := hC.models.HE.1
  have injX : Function.Injective (R.HX t).e := (hC.models.HX t).1

  have part1 : ∀ h, IsOpsE R h → ∀ y, R.Th t (hX P cX y) = h P c0 (R.Th t y) := by
    intro h hh y
    apply injE
    exact (hM y (hX P cX y) (hXo P hg cX y)).trans (hh P hg0 c0 (R.Th t y)).symm
  refine ⟨part1, ?_⟩
  intro c w hw
  have h01 := GlobalTheory.T.exists_sphericalOperators_rows_normal_eigenspaces R F hC hS SF hSF
  rcases h01 with ⟨h0, h0o, h0n, -, h0e, -⟩
  have hX01 := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).1 t
  rcases hX01 with ⟨hX0, hX0o, hX0n⟩
  have eqX : hX P cX = hX0 P cX := by
    ext x
    apply injX
    exact (hXo P hg cX x).trans (hX0o P hg cX x).symm
  have eX : LinearMap.adjoint (hX0 P cX) = hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX)) := hX0n.2 P hg cX
  have cX' : Commute (hX0 P cX) (hX0 P (dualC (Finsupp.mapRange star (star_zero ℂ) cX))) := hX0n.1 P P hg hg _ _
  have nX0 : Commute (hX0 P cX) (LinearMap.adjoint (hX0 P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute (hX0 P cX) B) _ _ eX.symm cX'
  have nX : Commute (hX P cX) (LinearMap.adjoint (hX P cX)) :=
    @Eq.subst (Module.End ℂ (R.HX t).H) (fun B => Commute B (LinearMap.adjoint B)) _ _ eqX.symm nX0
  have eE : LinearMap.adjoint (h0 P c0) = h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0)) := h0n.2 P hg0 c0
  have cE : Commute (h0 P c0) (h0 P (dualC (Finsupp.mapRange star (star_zero ℂ) c0))) := h0n.1 P P hg0 hg0 _ _
  have nE : Commute (h0 P c0) (LinearMap.adjoint (h0 P c0)) :=
    @Eq.subst (Module.End ℂ R.HE.H) (fun B => Commute (h0 P c0) B) _ _ eE.symm cE
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.Th t) (fun _ : Unit => hX P cX) (fun _ : Unit => h0 P c0)
    (fun _ u => part1 h0 h0o u) (fun _ => nX) (fun _ => nE) () _ w (h0e c P hg0 c0 w hw)

end GlobalTheory.Hk3.SysE
