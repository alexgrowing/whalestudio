import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedRepExistsRightTranslation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldFv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedLocalInducedSpaceIsoStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitaryMatrixSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.IndLineGL
open scoped GlobalTheory.IndLineGL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.induced_rep_exists_right_translation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ)
    (α β : kˣ →* ℂˣ), IsSmoothChar α → IsSmoothChar β →
    ∃ ρ : Representation ℂ (GL (Fin (a + a')) k) (GlobalTheory.KSplit.indSp a a' α β),
      (∀ g f x, ((ρ g f : GlobalTheory.KSplit.indSp a a' α β) : GL (Fin (a + a')) k → ℂ) x = (f : GL (Fin (a + a')) k → ℂ) (x * g)) ∧
      IsSmooth ρ ∧ Nonempty (ρ.Equiv (prod₂ (detRep (Fin a) α) (detRep (Fin a') β))) := by
  first | exact @GlobalTheory.KSplit.indSp_rightTr_equiv_prod₂ | exact GlobalTheory.KSplit.indSp_rightTr_equiv_prod₂ | (intros; apply GlobalTheory.KSplit.indSp_rightTr_equiv_prod₂ <;> assumption)
