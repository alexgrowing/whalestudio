import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtensionOfLowSmoothLines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockPolynomialLieDerivativeEquivariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HoweDualityCompactPairRealPlacesIrreducibleStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.HoweGen

theorem cvType_mem_of_stable : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), ∀ (U : Submodule ℂ (PolF D (Wc D i).rank (Vc D i).rank)), (∀ u ∈ GinfC (Vc D i), ∀ P ∈ U, ∀ P' : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t P' = R.ωP i t (u, 1) (R.ptP i t P) → P' ∈ U) → (∀ (τ : D.what₂.Tau) (Y : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ), Y ∈ lieAt (Wc D i) τ → ∀ (P P' : PolF D (Wc D i).rank (Vc D i).rank), (∀ z, HasDerivAt (fun s : ℝ => R.ωP i t (1, oneP R.θ (Wc D i) τ Y s) (R.ptP i t P) z) (R.ptP i t P' z) 0) → P ∈ U → P' ∈ U) → (∀ (x : LowT (R.MW i (sg0 D A))) (w : (R.cV i).W), R.ioP i x w ∈ U) → ∀ (φ : (R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank), (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (φ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (φ w'))) → ∀ w, φ w ∈ U := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t U hstab hlie hio φ hφ w
  have hadd : ∀ a b : PolF D (Wc D i).rank (Vc D i).rank, R.ptP i t (a + b) = R.ptP i t a + R.ptP i t b := by
    intro a b; unfold RealDat.ptP; simp
  have hsmul : ∀ (c : ℂ) (a : PolF D (Wc D i).rank (Vc D i).rank), R.ptP i t (c • a) = c • R.ptP i t a := by
    intro c a; unfold RealDat.ptP; simp
  have hzero : R.ptP i t 0 = 0 := by simpa using hsmul 0 0
  let M : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank) :=
    { carrier := {ψ | (∀ u ∈ GinfC (Vc D i), ∀ w', R.ptP i t (ψ ((R.cV i).ρ u w')) = R.ωP i t (u, 1) (R.ptP i t (ψ w'))) ∧ ∀ w, ψ w ∈ U}
      add_mem' := by
        rintro ψ₁ ψ₂ ⟨h₁, h₁'⟩ ⟨h₂, h₂'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.add_apply, hadd, h₁ u hu w', h₂ u hu w', map_add]
        · simp only [LinearMap.add_apply]; exact U.add_mem (h₁' w) (h₂' w)
      zero_mem' := by
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.zero_apply, hzero, map_zero]
        · simp only [LinearMap.zero_apply]; exact U.zero_mem
      smul_mem' := by
        rintro c ψ ⟨h₁, h₁'⟩
        refine ⟨fun u hu w' => ?_, fun w => ?_⟩
        · simp only [LinearMap.smul_apply, hsmul, h₁ u hu w', map_smul]
        · simp only [LinearMap.smul_apply]; exact U.smul_mem c (h₁' w) }
  have hioM : ∀ x, R.ioP i x ∈ M := fun x =>
    ⟨fun u hu w' => ((hG.core.thP.ioP i t).1 u hu x w').symm, fun w => hio x w⟩
  have hne : M ≠ ⊥ := by
    obtain ⟨v, w₀, -, -, hv⟩ := (hG.core.thP.ioP i t).2.2
    intro hM
    have h0 : R.ioP i (PiTensorProduct.tprod ℂ v) ∈ (⊥ : Submodule ℂ ((R.cV i).W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)) := hM ▸ hioM _
    rw [Submodule.mem_bot] at h0
    apply GlobalTheory.AdTh.IoExtPf.Delta_ne (D := D) i
    rw [← hv, h0]
    rfl
  have hφM : φ ∈ M := GlobalTheory.T.howeDuality_compactPair_realPlaces_irreducible D G Pl0 T A Ks R F hG hF i t M (fun ψ hψ => hψ.1)
    (fun ψ hψ τ Y hY ψ' hd => ⟨GlobalTheory.T.fockPolynomial_lieDerivative_equivariant D G Pl0 T A Ks R F hG hF i t τ Y hY ψ ψ' hψ.1 hd,
      fun w => hlie τ Y hY (ψ w) (ψ' w) (fun z => hd w z) (hψ.2 w)⟩) hne φ hφ
  exact hφM.2 w

end GlobalTheory.HoweGen
