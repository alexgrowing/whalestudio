import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterBasePlaceLift
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
theorem _root_.GlobalTheory.T.unramified_character_base_place_lift : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∃ ν₀ : (Fv F B.v₁)ˣ →* ℂˣ, IsUnram ν₀ ∧ (∀ y, ‖((ν₀ y : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ g₀ : GL (Fin a') (Fv F B.v₁), ∃ g ∈ UAt σ G.V' (evFin F B.v₁),
        ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ) := by
  first | exact @GlobalTheory.VPrimeActGood.vact | exact GlobalTheory.VPrimeActGood.vact | (intros; apply GlobalTheory.VPrimeActGood.vact <;> assumption)
