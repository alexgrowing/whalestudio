import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriplePolynomialLocalFunctionals
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
theorem _root_.GlobalTheory.T.triple_polynomial_local_functionals : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c → ∀ Φ ∈ GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁,
    ∃ (m : ℕ) (L : Fin m → ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] (GAd σ (c • G.W.J.map σ) → ℂ))
      (φ : Fin m → (Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ),
      (∀ i, φ i ∈ G.M'.SoLoc B.ψ B.τ₁) ∧
      (∀ i, ∀ g ∈ UAt σ G.V' (evFin F B.v₁), ∀ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁,
        ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' (g, 1)) φ₀ φ₁ → L i φ₁ = L i φ₀) ∧
      (∀ i, ∀ x : GLoc σ (c • G.W.J.map σ) B.v₁, ∀ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁,
        ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
        Acts (evFin F B.v₁) (om' (1, (toGAd hσ G.W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • G.W.J.map σ) B.v₁ x))) φ₀ φ₁ →
          L i φ₁ = fun y => L i φ₀ (y * GlobalTheory.AdelicU.emb σ (c • G.W.J.map σ) B.v₁ x)) ∧
      (fun y => G.M'.I om' Φ ((toGAd hσ G.W.J hc).symm y)) = ∑ i, L i (φ i) := by
  first | exact @GlobalTheory.ThetaGlobalHalf.thetaIntegral_eq_sum_local | exact GlobalTheory.ThetaGlobalHalf.thetaIntegral_eq_sum_local | (intros; apply GlobalTheory.ThetaGlobalHalf.thetaIntegral_eq_sum_local <;> assumption)
