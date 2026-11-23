import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyTwoNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.PairVac

theorem eventually_unrAt_of_isHecke {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (χ : Chr F E) (hχ : IsHecke F E χ) :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, UnrAt χ w := by
  obtain ⟨H, hloc, -⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ hcm χ hχ
  refine (GlobalTheory.HeckeSplit.eventually_unrAt H.1 H.2.1).mono fun w hw x hx => ?_
  rw [← hloc w x]
  exact ((GlobalTheory.HeckeSplit.unrAt_iff E H w).1 hw) x hx

theorem eventually_unrAt_chiX : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
      ∀ᶠ v in Filter.cofinite, ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χX w := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have h := eventually_unrAt_of_isHecke σ hP.base.cm χX hP.hX
  rw [Filter.eventually_cofinite] at h ⊢
  refine (h.image fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)).subset ?_
  intro v hv
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨w, hw, hu⟩ := hv
  exact ⟨w, hu, hw⟩

end GlobalTheory.PairVac

end
