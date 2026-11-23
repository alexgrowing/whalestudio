import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedLinearModelAtBasePlace
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_linear_model_at_base_place : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∃ (χW : (Fv F B.v₁)ˣ →* ℂˣ) (ε : Bool) (C : GL (Fin (a + a')) (Fv F B.v₁)), IsUnram χW ∧
      (∀ y, ‖((χW y : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ h ∈ UAt σ G.W (evFin F B.v₁), ∀ g M : GL (Fin (a + a')) (Fv F B.v₁),
        (mat h).map (piW B.τ₁) = g.1 →
        M.1 = C.1 * (if ε then ((g⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).1)ᵀ else g.1) * (C⁻¹ : GL (Fin (a + a')) (Fv F B.v₁)).1 →
        ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om' (1, h)) φ φ₁ ∧
          ι φ₁ = ((χW (GlobalTheory.SplitFlip.gdet M) : ℂ) * GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet M) ((a' : ℂ) / 2)) •
            fun Y => ι φ (Y * M.1) := by
  first | exact @GlobalTheory.WRightChar.unitaryW_char | exact GlobalTheory.WRightChar.unitaryW_char | (intros; apply GlobalTheory.WRightChar.unitaryW_char <;> assumption)
