import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolDataSoExistsBlockSplitting
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pol_data_so_exists_block_splitting : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∀ B₀ : GL (Fin (a + a')) (Fv F B.v₁), ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsUnram (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ (m : ℕ) (T : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ))
        (x : Fin m → IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ))),
        (∀ j, IsIntertw σ (c • G.W.J.map σ) B.τ₁ B₀ (pairInd (Fv F B.v₁) b hb χ) (T j)) ∧
        (fun y => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm y)) = ∑ j, T j (x j) := by
  first | exact @GlobalTheory.ThetaAtGood.thetaIntegral_eq_sum_intertw | exact GlobalTheory.ThetaAtGood.thetaIntegral_eq_sum_intertw | (intros; apply GlobalTheory.ThetaAtGood.thetaIntegral_eq_sum_intertw <;> assumption)
