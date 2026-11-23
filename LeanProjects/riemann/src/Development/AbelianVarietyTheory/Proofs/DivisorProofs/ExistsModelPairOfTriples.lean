import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.MidPair

theorem exists_midPair : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (X : Chars F E) (om : Rep σ G.V G.W)
    (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∃ (M₂ : Model σ G.V G₁.W) (om₂ : Rep σ G.V G₁.W),
      IsPair B M₂ X.β (X.β / X.α) om₂ (b + 2 - G.p) G.p (b + a' - (G₁.p + G₁.q)) (G₁.p + G₁.q) := by
  intro hK F E _ _ _ _ _ σ B b a' G G₁ X om om' om₁ om₁' hT hT₁
  obtain ⟨M₂, hM₂⟩ := GlobalTheory.ModelEx.model_exists F E σ B hT.base (b + 2) (b + a') G.V G₁.W _ _ _ _ hT.geo.hV hT₁.geo.hW
  have hW : IsHecke F E (X.β / X.α) := by
    refine ⟨Continuous.div' hT.chars.heckeβ.1 hT.chars.heckeα.1, fun x => ?_⟩
    rw [MonoidHom.div_apply, hT.chars.heckeβ.2 x, hT.chars.heckeα.2 x, div_one]
  have resW : ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range (X.β / X.α) (b + a') := by
    intro t
    have h1 := hT₁.chars.resβ t
    have h2 := hT₁.chars.resα t
    rw [MonoidHom.div_apply, Circle.coe_div, h1, h2]
    split_ifs
    · simp
    · rw [pow_add, div_eq_mul_inv, ← inv_pow, inv_neg_one]
  obtain ⟨om₂, hw⟩ := GlobalTheory.WeilExGen.exists_isWeil hK.base F E σ B hT.base (b + 2) (b + a') G.V G₁.W _ _ _ _ hT.geo.hV hT₁.geo.hW M₂ hM₂
    X.β (X.β / X.α) hT.chars.heckeβ hW hT.chars.resβ resW
  exact ⟨M₂, om₂, ⟨hT.base, hT.geo.hV, hT₁.geo.hW, hM₂, hT.chars.heckeβ, hW, hT.chars.resβ, resW, hw⟩⟩

end GlobalTheory.ThK.MidPair
