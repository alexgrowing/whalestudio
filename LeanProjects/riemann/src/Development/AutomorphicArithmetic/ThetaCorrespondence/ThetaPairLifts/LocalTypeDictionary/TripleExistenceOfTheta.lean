import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleExistenceOfTheta
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaNormEqProdLocalFactors
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.FirstOccurrenceThetaLiftNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleExistenceOfThetaStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta
open IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
namespace GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem triEx_holds_alt : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → TriEx := by
  intro hH hP hK hM hL
  obtain ⟨CF1, H1⟩ := _root_.GlobalTheory.T.bottom_theta_norm_eq_prod_local_factors hH hP hK hM hL
  obtain ⟨CF2, H2⟩ := _root_.GlobalTheory.T.first_occurrence_theta_lift_ne_zero hP hK hM hL
  refine ⟨max CF1 CF2, fun ε CF hCF => ?_⟩
  obtain ⟨C1, x1, G1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨C2, x2, G2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max C1 C2, max x1 x2, fun C hC D large₂ he hx hR T Lc μ₀ hμ G W _ i j => ?_⟩
  obtain ⟨A, A', WW, X, hX⟩ := GlobalTheory.RowTest.exists_bottomTri hμ G W i j
  obtain ⟨Pi, p, p', J, hs, ⟨P', hP'⟩, hJ, hI, hI'⟩ :=
    G1 C (le_trans (le_max_left _ _) hC) D large₂ he (le_trans (le_max_left _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  have hN := G2 C (le_trans (le_max_right _ _) hC) D large₂ he (le_trans (le_max_right _ _) hx) hR T Lc μ₀ hμ G W i j A A' WW X hX
  choose lam hlam using hI
  have hinj : ∀ t, Function.Injective (J t) := fun t => by
    refine (hJ t).resolve_left fun h0 => ?_
    obtain ⟨Q, h, hQ⟩ := (hN t).2
    exact hQ (by rw [hI' t Q, h0]; rfl)
  have hlam0 : ∀ t, lam t ≠ 0 := fun t h0 => by
    obtain ⟨Q, h, hQ⟩ := (hN t).1
    exact hQ (by rw [hlam t Q, h0, zero_smul]; rfl)
  have hF : GlobalTheory.ConstRatio.Factor X W.ψ W.θ lam :=
    ⟨hlam0, Pi, p, p', J, hs, hinj, fun t P h => (hX.integrable t).1 P h, hlam, fun t Q _ => hI' t Q,
      P', hP', fun t h => (hX.integrable t).2 P' h⟩
  haveI : Nonempty T := ⟨μ₀⟩
  exact ⟨A, A', WW, X, lam, hX, hF.isConst⟩
end GlobalTheory.SqTop
end
end

section
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triEx_of_howe_duality_real : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → TriEx := by
  first | exact @_root_.GlobalTheory.SqTop.triEx_holds_alt | exact _root_.GlobalTheory.SqTop.triEx_holds_alt | (intros; apply _root_.GlobalTheory.SqTop.triEx_holds_alt <;> assumption)
end
