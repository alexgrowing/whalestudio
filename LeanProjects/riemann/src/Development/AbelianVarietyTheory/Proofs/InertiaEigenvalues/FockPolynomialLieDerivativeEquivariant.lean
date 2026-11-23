import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorTargetLieOneParamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockScalarLinearSubstitutionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialSubstitutionCommuteTargetGlActionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

open GlobalTheory.ExportSeries GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

namespace GlobalTheory.LieEquivFock

theorem lie_equivariant : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (ψ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) → (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ' ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ' w'))) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t τ Y hY ψ ψ' hψ hψ'
  obtain ⟨a, hL⟩ := GlobalTheory.T.hasDerivAt_fockVector_targetLieOneParam D G Pl0 T A Ks R F hG hF i t τ Y hY
  have hinj : Function.Injective (R.ptP i t) := (GlobalTheory.CoefActIo.thetaVector_laws (i := i) hG.core t).2.2
  have hlin : ∀ (c : ℂ) (P : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t (c • P) = c • R.ptP i t P := by
    intro c P
    unfold RealDat.ptP
    exact map_smul _ c P
  set Y' := (R.MW i (sg0 D A)).fr τ * Y * ((R.MW i (sg0 D A)).fr τ)⁻¹
  set Lop : PolF D (Wc D i).rank (Vc D i).rank → PolF D (Wc D i).rank (Vc D i).rank :=
    fun P => fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < pS D i τ)) Y' P + a • P
    with hLop
  have hder : ∀ w, ψ' w = Lop (ψ w) := by
    intro w
    apply hinj
    funext z
    exact (hψ' w z).unique (hL (ψ w) z)
  intro u hu w'
  obtain ⟨c, g, hg⟩ := GlobalTheory.T.realPoints_act_fock_scalar_linear_substitution D G Pl0 T A Ks R F hG i t u hu
  have h1 : ψ ((R.cV i).ρ u w') = c • fockSubst (pS D i) g (ψ w') := by
    apply hinj
    rw [hψ u hu w', hg, hlin]
  have hcomm : ∀ Q, Lop (fockSubst (pS D i) g Q) = fockSubst (pS D i) g (Lop Q) := by
    intro Q
    simp only [hLop, map_add, map_smul]
    rw [GlobalTheory.T.fockPolynomialSubstitution_commute_targetGlAction]
  have hsm : ∀ x, Lop (c • x) = c • Lop x := by
    intro x
    simp only [hLop, map_smul, smul_add]
    rw [smul_comm a c]
  rw [hder, h1, hder, hg, ← hlin, hsm, hcomm]

end GlobalTheory.LieEquivFock
