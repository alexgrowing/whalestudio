import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigAFirst
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
theorem _root_.GlobalTheory.T.seesaw_identity_config_a_first : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W),
      IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (v : Pl F) (t : E →ₐ[F] Fv F v),
      ∃ (c : GL (Fin (b + 2 + a')) (Fv F v)) (e : (Σ i : Fin 3, Fin (blk3 (b + a') i)) ≃ Fin (b + 2 + a'))
        (ξ₁ ξ₂ : (Fv F v)ˣ →* ℂˣ),
        (∀ h ∈ UAt σ G.W (evFin F v), GlobalTheory.KSplit.locMat t c h ∈ unipRad (Fv F v) e → h ∈ unip σ G.W H') ∧
        ∀ (l : Levi (Fv F v) (fun i : Fin 3 => Fin (blk3 (b + a') i))), ∀ h ∈ UAt σ G.W (evFin F v),
          GlobalTheory.KSplit.locMat t c h = leviEmb (Fv F v) e l →
          ∃ (s : (AE F E)ˣ) (h₁ : UA σ G₁.W.J), IsLevi H' s h₁ h ∧ h₁ ∈ UAt σ G₁.W (evFin F v) ∧
            GlobalTheory.KSplit.locMat t (1 : GL (Fin (b + a')) (Fv F v)) h₁ = l 1 ∧
            (X.α s : ℂ) * (((absE F E s : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) =
              ((ξ₁ (Matrix.GeneralLinearGroup.det (l 0)) * ξ₂ (Matrix.GeneralLinearGroup.det (l 2)) : ℂˣ) : ℂ) := by
  first | exact @GlobalTheory.PlaneCoordAt.coord | exact GlobalTheory.PlaneCoordAt.coord | (intros; apply GlobalTheory.PlaneCoordAt.coord <;> assumption)
