import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneModularCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviSectionMultiplicative
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar

noncomputable section

namespace GlobalTheory.LeviRatPlane

open Matrix

theorem levi_rat_of_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      ∀ γ ∈ ratPts σ (c₀ • W.J.map σ), ∀ (t : (AE F E)ˣ) (m : UA σ W.J) (h₁ : UA σ W₁.J), IsLevi (W₁ := W₁) H t 1 m →
        γ = GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ m * GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc₀ (M h₁) →
        (∃ s : Eˣ, t = Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom s) ∧ h₁ ∈ ratU σ W₁.J := by
  intro F E _ _ _ _ _ σ hcm hσ n n₁ W W₁ H hskew hn hxx hyy hxy horth hgram c₀ hc₀ hND₁ hND M hM γ hγ t m h₁ hm hγe
  have hdet : W₁.J.det ≠ 0 := by
    intro h0
    apply hND₁.2
    rw [det_smul, show (W₁.J.map σ).det = σ W₁.J.det from (RingHom.map_det (σ : E →+* E) _).symm, h0, map_zero, mul_zero]
  subst hn
  obtain ⟨L, hL, -, -, -, -, -⟩ := GlobalTheory.LeviSplit.exists_proj hσ W W₁ H hskew hxx hyy hxy horth hgram hdet
  have hl : IsLevi (W₁ := W₁) H t h₁ (m * M h₁) := by
    simpa using GlobalTheory.LeviHom.isLevi_mul H hm (hM h₁)
  have hr : m * M h₁ ∈ ratU σ W.J := by
    rw [← GlobalTheory.ThK.GLTwo.toGAd_mem_ratPts hσ W.J hc₀, map_mul, ← hγe]
    exact hγ
  refine ⟨?_, GlobalTheory.LeviSplit.rat_of_isLevi hL hl hr⟩
  obtain ⟨G, hG⟩ := Subgroup.mem_subgroupOf.1 hr
  have hmat : mat (m * M h₁) = incM F G.1 := (congrArg Units.val hG).symm
  have hx := hl.1
  rw [hmat, GlobalTheory.LeviSplit.incM_mulVec] at hx
  obtain ⟨k, hk⟩ : ∃ k, H.x k ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : H.x = 0 := funext hc
    rw [h0] at hxy
    simp [form] at hxy
  set f : E →+* AE F E := inclR (F := F) (E := E) (AF F) with hf
  have hinj : Function.Injective f := GlobalTheory.AutFunCompare.inclA_injective
  set a : E := (G.1 *ᵥ H.x) k / H.x k with ha
  have hk' : f ((G.1 *ᵥ H.x) k) = t.1 * f (H.x k) := congrFun hx k
  have hxa : (G.1 *ᵥ H.x) k = a * H.x k := by rw [ha, div_mul_cancel₀ _ hk]
  have hu : IsUnit (f (H.x k)) := (IsUnit.mk0 _ hk).map f
  have ht : t.1 = f a := by
    rw [hxa, map_mul] at hk'
    exact hu.mul_left_inj.1 hk'.symm
  have ha0 : a ≠ 0 := by
    intro h0
    rw [h0, map_zero] at ht
    have : (1 : AE F E) = 0 := by
      rw [← Units.mul_inv t, ht, zero_mul]
    exact one_ne_zero (hinj (by rw [map_one, map_zero]; exact this))
  exact ⟨Units.mk0 a ha0, Units.ext (by simpa using ht)⟩

end GlobalTheory.LeviRatPlane
