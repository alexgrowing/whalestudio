import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataExistsBlockSplitting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterExponentListStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryMaximalCompactLocalConjStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.LeviBlockExponent
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pol_data_exists_block_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M,
    ∀ B₀ : GL (Fin (a + a')) (Fv F B.v₁), ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsSmoothChar (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ (m : ℕ) (T : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ))
        (x : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ))),
        (∀ j, IsIntertw σ (c • G.W.J.map σ) B.τ₁ B₀ (pairInd (Fv F B.v₁) b hb χ) (T j)) ∧
        (fun y => G.M.I om Φ ((toGAd hσ G.W.J hc).symm y)) = ∑ j, T j (x j) := by
  first | exact @GlobalTheory.ThK.ThetaKV.theta_sum_intertw | exact GlobalTheory.ThK.ThetaKV.theta_sum_intertw | (intros; apply GlobalTheory.ThK.ThetaKV.theta_sum_intertw <;> assumption)
