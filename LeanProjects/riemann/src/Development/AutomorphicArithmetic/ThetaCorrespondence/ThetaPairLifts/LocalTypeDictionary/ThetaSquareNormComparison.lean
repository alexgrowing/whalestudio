import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingFactorStage
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsTiedPairOfStandingHypotheses
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsScalarOfRealStandingData
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.RegConstEqAwayUnitMulFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonvanishingFactorStageStatement

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SqCompare
theorem theta_square_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * lam t := by
  intro hP hK hM
  refine gBig_three (_root_.GlobalTheory.T.exists_tied_theta_pair hP hK hM) (_root_.GlobalTheory.T.theta_real_places_separation hP hK hM) (_root_.GlobalTheory.T.regConst_eq_away_unit_mul_factor hP hK hM) ?_
  intro D T Lc sc G μ₀ C x b hex hreal hcmp W S hstd hN ρ i j X lam hT hX hl
  obtain ⟨ρ₀, hvX, hvT, htied, hreg⟩ := hex W S.B ρ
  obtain ⟨l, hl0, hl1⟩ := hreal W S.B ρ ρ₀ hvX hvT i j
  obtain ⟨κ, hκ, hc⟩ := hcmp W S hstd hN ρ₀ htied i j X lam hT hX hl
  refine ⟨fun t => l * κ t, fun t => ?_, fun t c' _ hc' => ?_⟩
  · obtain ⟨h0, ζ, hζ, he⟩ := hκ t
    refine ⟨mul_ne_zero hl0 h0, ζ, hζ, ?_⟩
    show l * κ t = _ * (l * κ μ₀)
    rw [he]; ring
  · obtain ⟨c₀, h₀⟩ := hreg i j t
    have h1 := (hl1 t c' c₀ hc' h₀).2
    have h2 := hc t c₀ h₀
    show c' = l * κ t * lam t
    rw [h1, h2]; ring
end GlobalTheory.SqCompare
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_square_norm_comparison : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) → NumbersIn D.what₂.embLL S μ₀ → ∀ (ρ : RealMatch W) (i j : Fin D.R.m) (X : TriG G i j) (lam : T → ℂ),
    TopGrid W i j X → IsStageC W i j (pp D j) (qq D j) X → Factor X W.ψ W.θ lam →
    ∃ κ : T → ℂ, (∀ t, κ t ≠ 0 ∧ ∃ ζ : D.what₂.LL, GlobalTheory.Square.IsAwayUnit (Qn G t) ζ ∧ κ t = D.what₂.embLL ζ * κ μ₀) ∧
      ∀ (t : T) (c' : ℂ), SquareNonzero W S.B ρ t i j → IsSquareConst W S.B ρ t i j c' → c' = κ t * lam t := by
  first | exact @_root_.GlobalTheory.SqCompare.theta_square_comparison | exact _root_.GlobalTheory.SqCompare.theta_square_comparison | (intros; apply _root_.GlobalTheory.SqCompare.theta_square_comparison <;> assumption)
end
