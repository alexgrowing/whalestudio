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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteMapsSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearFunctionalTripleAtGoodPlace
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open GlobalTheory.LFun

namespace GlobalTheory.VPrimeActGood

theorem vact : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' →
    ∃ ν₀ : (Fv F B.v₁)ˣ →* ℂˣ, IsUnram ν₀ ∧ (∀ y, ‖((ν₀ y : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι → ∀ g₀ : GL (Fin a') (Fv F B.v₁), ∃ g ∈ UAt σ G.V' (evFin F B.v₁),
        ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F B.v₁),
          Acts (evFin F B.v₁) (om' (g, 1)) φ φ₁ ∧ ι φ₁ = GlobalTheory.FullRankCoinv.lact ν₀ g₀ (ι φ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT
  have hP : GlobalTheory.FunPr.Hypotheses₂ := hKP.base
  have hv : X.Good B.v₁ := hT.chars.good
  have hvT : B.v₁ ∉ X.T := hv.1
  obtain ⟨-, -, hrα⟩ := GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.α hT.chars.heckeα B.v₁ B.τ₁
  obtain ⟨-, -, hrβ⟩ := GlobalTheory.T.splitPlaceCharacterComponent_smooth_unitary_conductor F E X.β hT.chars.heckeβ B.v₁ B.τ₁
  have hw : splitPrime B.τ₁ ∉ above E (X.T : Set (Pl F)) := by
    show ¬ (splitPrime B.τ₁).under (𝓞 F) ∈ (X.T : Set (Pl F))
    rw [splitPrime_under]
    exact hvT
  have uα := hrα.2 (hT.chars.unrα _ hw)
  have uβ := hrβ.2 (hT.chars.unrβ _ hw)
  refine ⟨chrW X.ν B.τ₁, ?_, ?_, ?_⟩
  · intro x hx
    show chrW (X.α / X.β) B.τ₁ x = 1
    rw [GlobalTheory.KSplit.chrW_div, MonoidHom.div_apply, uα x hx, uβ x hx, div_one]
  · intro y
    simp only [chrW, locChar, MonoidHom.coe_comp, Function.comp_apply]
    first | exact Circle.norm_coe _ | exact Circle.abs_coe _ | simp
  · intro ι hι g₀
    exact (GlobalTheory.T.local_linear_functional_triple_at_good_place hP F E σ B a a' G X om om' hT B.v₁ hv B.τ₁ ι hι).2.2.1 g₀

end GlobalTheory.VPrimeActGood
