import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstTermZeroAllLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCompactOpenLift

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKWitt

theorem exists_ratU_to_plane : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ w : Fin d → E, w ≠ 0 → form σ W.J w w = 0 → ∃ γ ∈ ratU σ W.J, mat γ *ᵥ incV F w = incV F H'.x := by
  intro _ F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H _ V₁ M₁ e _ _ _ w hw0 hw
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.IndLine.LeviK.sigma_sigma hP.base
  have hsk : ∀ i j, σ (W.J j i) = -W.J i j := hP.skew.skew
  have hd : W.J.det ≠ 0 := GlobalTheory.ThK.DescB.Nondeg.det_ne_zero_of_cartan B W hP.skew.cartan
  have hx0 : H'.x ≠ 0 := fun h0 => by
    have := hH'.xy
    rw [h0] at this
    simp [form] at this
  obtain ⟨T, hT, hTx⟩ := GlobalTheory.LineCuspAll.exists_isom hσ hsk hd hw0 hx0 hw hH'.xx
  obtain ⟨γ, hγ, hm⟩ := GlobalTheory.LineCuspAll.exists_ratU hd (GlobalTheory.LineCuspAll.gram_of_isom hT)
  exact ⟨γ, hγ, by rw [hm, ← GlobalTheory.ThKLineCusp.incV_mulVec, hTx]⟩

end GlobalTheory.ThKWitt
