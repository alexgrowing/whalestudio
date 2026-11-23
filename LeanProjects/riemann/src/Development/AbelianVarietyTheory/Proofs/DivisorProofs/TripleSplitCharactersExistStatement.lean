import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleSplitCharactersExist
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
theorem _root_.GlobalTheory.T.triple_split_characters_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), GlobalTheory.ThK.KP → IsTriple B G X om om' →
    ∀ (c : E) (hc : c ≠ 0), σ c = -c →
    ∃ (b : Fin 2 → ℕ) (hb : b 0 + b 1 = a + a') (χ : Fin 2 → (Fv F B.v₁)ˣ →* ℂˣ),
      ((b 0 = a ∧ b 1 = a') ∨ (b 0 = a' ∧ b 1 = a)) ∧ (∀ j, IsUnram (χ j)) ∧ (∀ j y, ‖((χ j y : ℂˣ) : ℂ)‖ = 1) ∧
      ∃ P : ((Fin a' × Fin (a + a') → Fv F B.v₁) → ℂ) →ₗ[ℂ] IndSp (pairPlace b hb) (ofChar (pairChar (Fv F B.v₁) b χ)),
        (∀ ξ, ∃ φ ∈ G.M'.SoLoc B.ψ B.τ₁, P φ = ξ) ∧
        (∀ φ ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁), P φ = 0 →
          φ ∈ Submodule.span ℂ {z | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁,
            ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), Acts (evFin F B.v₁) (om' (g, 1)) φ₀ φ₁ ∧ z = φ₁ - φ₀}) ∧
        ∀ (g : GL (Fin (a + a')) (Fv F B.v₁)) (x : GLoc σ (c • G.W.J.map σ) B.v₁),
          IsCompAt σ (c • G.W.J.map σ) B.τ₁ 1 g x → ∀ φ₀ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ φ₁ ∈ G.M'.SoLoc B.ψ B.τ₁,
            Acts (evFin F B.v₁) (om' (1, (toGAd hσ G.W.J hc).symm (GlobalTheory.AdelicU.emb σ (c • G.W.J.map σ) B.v₁ x))) φ₀ φ₁ ∧
            P φ₁ = pairInd (Fv F B.v₁) b hb χ g (P φ₀) := by
  first | exact @GlobalTheory.ThetaAtGoodLocal.localHalf | exact GlobalTheory.ThetaAtGoodLocal.localHalf | (intros; apply GlobalTheory.ThetaAtGoodLocal.localHalf <;> assumption)
