import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ActOfMemGfC
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RaisingLoweringOperators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TranslateMemCoefLatFn
import Development.AbelianVarietyTheory.Definitions.Foundations.ForallEventuallyFinLocIff
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairPolynomialFockAllRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RealPointsActFockByRealComponentsBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasDerivAtFockVectorsTargetLieRealPlaceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanConjUnitaryLieAlgebraRealPlaceEqTopStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section

namespace GlobalTheory.HoweIrrCompact

section FockLin
variable {D : D7} {a b : ℕ} (τ : D.what₂.Tau) (ε : Fin a → Bool) (ε' : Fin b → Bool)

theorem fockT_zero : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (0 : Matrix (Fin b) (Fin b) ℂ) = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT]

theorem fockT_add (Y Y' : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (Y + Y') = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y + GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y' := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem fockT_smul (c : ℂ) (Y : Matrix (Fin b) (Fin b) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' (c • Y) = c • GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ ε ε' Y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT, Matrix.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

end FockLin

theorem howe_irr : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)), (∀ ψ ∈ M, (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w')))) → (∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ ψ' : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ w z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t (ψ w)) z) (R.ptP i t (ψ' w) z) 0) → ψ' ∈ M) → M ≠ ⊥ → ∀ φ : ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → φ ∈ M := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hFull i t M hMeq hMlie hM0 φ hφ
  classical
  have hC := hG.core
  obtain ⟨-, -, hinj⟩ := GlobalTheory.CoefActIo.thetaVector_laws (i := i) hC t
  obtain ⟨w, BS, r, hact, hU, hsurj, hε⟩ := GlobalTheory.T.realPoints_act_fock_by_realComponents_basis D G Pl0 T A Ks R F hG hFull i t
  set ρ' : ↥(GinfC (Vc D i)) →* Module.End ℂ (R.cV i).W := (R.cV i).ρ.comp (GinfC (Vc D i)).subtype with hρ'
  have eqv : ∀ ψ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank,
      (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) →
      ∀ (k : ↥(GinfC (Vc D i))) (w' : (R.cV i).W), ψ (ρ' k w') = GlobalTheory.ExportSeries.fockGL (Wc D i).rank w BS (r k) (ψ w') := by
    intro ψ hψ k w'
    apply hinj
    rw [← hact k (ψ w')]
    exact hψ k k.2 w'
  have hirr : ∀ U : Submodule ℂ (R.cV i).W, (∀ k, U.map (ρ' k) ≤ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hUk
    refine (hC.models.cV i).2.2.2.2 U fun h => ?_
    have e := GlobalTheory.AutMult.toInf_mul_toFin (V := Vc D i) h
    have h1 : (R.cV i).ρ h = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
      calc (R.cV i).ρ h = (R.cV i).ρ ((GlobalTheory.AutMult.toInf (Vc D i) h : GA D (Vc D i)) * GlobalTheory.AutMult.toFin (Vc D i) h) := by rw [e]
        _ = ρ' (GlobalTheory.AutMult.toInf (Vc D i) h) := by
          rw [map_mul, (hC.models.cV i).1 _ (GlobalTheory.AutMult.toFin (Vc D i) h).2, mul_one]
          rfl
    rw [h1]
    exact hUk _
  have hlie : ∀ ψ ∈ M, ∀ (τ : D.what₂.Tau) (Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ),
      GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) (fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ)) Z ∘ₗ ψ ∈ M := by
    intro ψ hψ τ
    obtain ⟨κ, hκ⟩ := GlobalTheory.T.hasDerivAt_fockVectors_targetLie_realPlace D G Pl0 T A Ks R F hG hFull i t τ
    have hε' : (R.MW i (sg0 D A)).ε τ = fun j : Fin (Wc D i).rank => decide ((j : ℕ) < w.p τ) := funext (hε τ)
    set fr := (R.MW i (sg0 D A)).fr τ with hfr
    have base : ∀ Y ∈ lieAt (Wc D i) τ,
        GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) ∘ₗ ψ ∈ M := by
      intro Y hY
      have h1 : (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.fockT τ (fun _ : Fin (Vc D i).rank => true) ((R.MW i (sg0 D A)).ε τ) (fr * Y * fr⁻¹) + κ Y • (1 : Module.End ℂ (PolF D (Wc D i).rank (Vc D i).rank))) ∘ₗ ψ ∈ M :=
        hMlie ψ hψ τ Y hY _ fun w' z => by
          simpa using hκ Y hY (ψ w') z
      have h2 : κ Y • ψ ∈ M := M.smul_mem _ hψ
      have h3 := M.sub_mem h1 h2
      convert h3 using 1
      ext x
      simp
    have hsp := GlobalTheory.T.span_conj_unitaryLieAlgebra_realPlace_eq_top D (Wc D i) τ fr ((R.MW i (sg0 D A)).fr_unit τ)
    intro Z
    have hZ : Z ∈ Submodule.span ℂ {Z : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ | ∃ Y ∈ lieAt (Wc D i) τ, Z = fr * Y * fr⁻¹} := by
      rw [hsp]; exact Submodule.mem_top
    rw [← hε']
    induction hZ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Y, hY, rfl⟩ := hx
      exact base Y hY
    | zero =>
      rw [fockT_zero, LinearMap.zero_comp]; exact M.zero_mem
    | add x y _ _ hx hy =>
      rw [fockT_add, LinearMap.add_comp]; exact M.add_mem hx hy
    | smul c x _ hx =>
      rw [fockT_smul, LinearMap.smul_comp]; exact M.smul_mem c hx
  exact GlobalTheory.T.howeDuality_compactPair_polynomialFock_allRealPlaces D (Vc D i).rank (Wc D i).rank w BS ↥(GinfC (Vc D i)) r hU hsurj (R.cV i).W ρ' hirr M
    (fun ψ hψ => eqv ψ (hMeq ψ hψ)) hlie hM0 φ (eqv φ hφ)

end GlobalTheory.HoweIrrCompact
