import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockCoefficientEqConstMulLowestKTypeCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarmonicFockVectorsKilledByLoweringAdaptedBasisStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LabelAtRealPlaceEqEmbeddingOverReflexFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesModelHolomorphicPositiveSignsFirstStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairingLowestWeightSchurPolarisationStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsInnerEqFockInnerProductMulNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MixedLaplacianKillsProductOfMinors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramNegTransposeDiag
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HolomorphicLowestType
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

noncomputable section

namespace GlobalTheory.FockCoefReal

theorem l2_self_eq_setIntegral_norm_sq {X : Type} [MeasurableSpace X] (μ : Measure X) (𝓧 : Set X) (f : X → ℂ) :
    l2 μ 𝓧 f f = ((∫ w in 𝓧, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
  show (∫ w in 𝓧, f w * starRingEnd ℂ (f w) ∂μ) = _
  rw [← integral_complex_ofReal]
  congr 1
  funext w
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem fockIp_eq_fock {ι : Type} (P Q : MvPolynomial ι ℂ) : GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp P Q = Formalism.E.fock P Q := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp, Formalism.E.fock, Formalism.A.mfact, starRingEnd_apply]

set_option maxHeartbeats 1000000 in

theorem fock_coef_real : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → ∀ g : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D (Wc D i) ρ)) → ∀ (e e' : ∀ ρ, lowT (R.MW i σ) ρ) (w w' : c.W), l2 μ 𝓧 (ω (1, realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w))) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) = Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * (∏ ρ, ⟪((e' ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ), (R.MW i σ).rep ρ (g ρ) ((e ρ : (R.MW i σ).sm ρ) : (R.MW i σ).H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ * l2 μ 𝓧 f f := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hcv g hg e e' w w'
  obtain ⟨hf0, hfth, hcartV, hvac⟩ := GlobalTheory.T.thetaLiftDatum_isNonzeroFockVacuum R F i t σ s P cμ cη m ω BW f₀ f c io hL μ 𝓧 hcv
  obtain ⟨hCore, -, hEmb, -, -, hW, hBW, -, hPt, hc, hIo⟩ := hL
  have hm := hCore.models
  have hθ : IsInfFam R.θ := hm.inf
  have hlab := GlobalTheory.T.labelAtRealPlace_eq_embedding_over_reflexField D σ s hEmb
  obtain ⟨hHol, hWt, hε⟩ := GlobalTheory.T.discreteSeriesModel_holomorphic_positiveSignsFirst D σ hlab i (R.MW i σ)
  let pt := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) BW f
  have hpt : ptAt R i σ BW f = ⇑pt := rfl
  have hptTh : ∀ Q, IsThetaFunO R.ψ (Vc D i) (Wc D i) (pt Q) := hPt
  have hpq : ∀ τ, pW D i τ + qW D i τ ≤ (Vc D i).rank := fun τ => by
    have e1 := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    have e2 := Formalism.IndefR.FWT.rank_Wc i
    have e3 := r_le_V i
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e1
    simp only [pW, qW]
    omega
  have hpW : ∀ τ, pW D i τ ≤ (Wc D i).rank := fun τ => by
    have e1 := GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW_add_qW i τ
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.pW, GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicLowestType.qW] at e1
    simp only [pW]
    omega
  have hharm := fun τ => GlobalTheory.T.mixed_laplacian_kills_product_of_minors D (Wc D i).rank (Vc D i).rank (pW D i) (qW D i) (aPlAt D i σ) (aMiAt D i σ) hpq τ
  have hkill := GlobalTheory.T.harmonicFockVectors_killed_by_lowering_adaptedBasis D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) (D.sp.V_sig _) (D.sp.W_sig _)
    (R.BV i) (hm.BV i) (pW D i) hε BW hBW f hfth hvac (deltaAtEmb D i σ) hharm
  have hee := GlobalTheory.T.fockCoefficient_eq_const_mul_lowestKTypeCoefficient D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) hHol hWt μ 𝓧 hcv c hc pt hptTh
    (deltaAtEmb D i σ) io hIo hkill
  have hww := GlobalTheory.T.thetaLiftPairing_lowestWeight_schur_polarisation D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hθ hW _ (R.MW i σ) μ 𝓧 hcv c hc pt hptTh
    (deltaAtEmb D i σ) io hIo hee g hg e e' w w'
  have hip := GlobalTheory.FockIsometry.ipO_pureTensorO D R.ψ R.θ (Vc D i) (Wc D i) hW.std hθ (fun _ => 1) (R.BV i)
    (cart (R.MW i σ)) BW (fun _ => (Vc D i).rank) (pW D i) (fun _ => le_rfl) hpW hcartV
    (fun ρ => GlobalTheory.FrameEquiv.isCartanInv_cart_model (R.MW i σ) ρ) (hm.BV i) hBW f hfth hvac μ 𝓧 hcv
    (deltaAtEmb D i σ) (deltaAtEmb D i σ)
  have hΔ : l2 μ 𝓧 (pt (deltaAtEmb D i σ)) (pt (deltaAtEmb D i σ)) =
      Formalism.E.fock (deltaAtEmb D i σ) (deltaAtEmb D i σ) * l2 μ 𝓧 f f := by
    rw [l2_self_eq_setIntegral_norm_sq μ 𝓧 f, ← fockIp_eq_fock]
    exact hip
  rw [hpt, hww, hΔ]
  ring

end GlobalTheory.FockCoefReal

end
