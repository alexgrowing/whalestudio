import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.HeckeCharacterParameters
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockMatrixCoefficientSplitsRealFiniteFactorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuumStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.JointHarmonicsLowestKTypeCoefficientRealStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCharFamIsVacVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.FockCoeffImage

theorem fockCoefficientC : GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts.HarmonicModule → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → FockCoefficientC R F := by
  intro hHM D G _ _ Pl0 T A Ks _ _ _ R F hPM
  intro i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ x hx g hg e e' w w'
  obtain ⟨hne, hth, hcart1, hvac⟩ := GlobalTheory.T.thetaLiftDatum_isNonzeroFockVacuum R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ
  have hreal := GlobalTheory.T.jointHarmonics_lowest_KType_coefficient_real hHM R F hPM i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ g hg e e' w w'
  obtain ⟨hC, -, -, -, -, hW, hON, -, hPt, -, -⟩ := h
  have hinf : IsInfFam R.θ := hC.models.inf
  have hbM : GlobalTheory.AdelicScalar.realElt R.θ (Wc D i) g ∈ GinfC (Wc D i) := by
    refine list_prod_mem fun y hy => ?_
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hy
    exact GlobalTheory.PointAtPlaceHom.atTau_mem _ τ _
  have key := GlobalTheory.T.fockMatrixCoefficient_splits_real_finite_factors D R.ψ R.θ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hinf hW μ 𝓧 hμ (fun _ => 1) (R.BV i)
    (cart (R.MW i σ)) BW hcart1 (fun τ => GlobalTheory.Chain.VacVec.cart_isCartanInv _ τ) (fun _ => (Vc D i).rank) (pW D i)
    (fun τ => hC.models.BV i τ) hON f hth hvac (fun Q => hPt Q) 1 (one_mem _) _ hbM 1 (one_mem _) x hx
    (io (PiTensorProduct.tprod ℂ e) w) (io (PiTensorProduct.tprod ℂ e') w')
  rw [one_mul] at key
  change _ * l2 μ 𝓧 f f = l2 μ 𝓧 (ω (1, GlobalTheory.AdelicScalar.realElt R.θ (Wc D i) g) (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e) w)))
    (ptAt R i σ BW f (io (PiTensorProduct.tprod ℂ e') w')) * _ at key
  rw [hreal] at key
  refine mul_right_cancel₀ hne (key.trans ?_)
  ring

end GlobalTheory.FockCoeffImage
