import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensHomTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroBC

theorem preimage_surj : ∀ (R₀ R₁ : Type) [CommRing R₀] [CommRing R₁] [Algebra R₀ R₁] (q : R₁ →ₐ[R₀] R₀), (∀ y y', q y = 0 → q y' = 0 → y * y' = 0) → ∀ (X₀ X₁ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (s₁ : X₁ ⟶ Sp R₁) (pr : X₁ ⟶ X₀), IsPullback pr s₁ s₀ (spMap (algebraMap R₀ R₁)) → ∀ U : X₁.Opens, ∃ V : X₀.Opens, pr ⁻¹ᵁ V = U := by
  intro R₀ R₁ _ _ _ q hq X₀ X₁ s₀ s₁ pr hp U
  have hqs : Function.Surjective (q : R₁ →+* R₀) := fun x ↦ ⟨algebraMap R₀ R₁ x, q.commutes x⟩
  have hid : spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁) = 𝟙 (Sp R₀) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have : (q : R₁ →+* R₀).comp (algebraMap R₀ R₁) = RingHom.id R₀ := RingHom.ext fun x ↦ q.commutes x
    rw [this]
    exact Spec.map_id _
  let σ : X₀ ⟶ X₁ := hp.lift (𝟙 X₀) (s₀ ≫ spMap (q : R₁ →+* R₀)) (by rw [Category.id_comp, Category.assoc, hid, Category.comp_id])
  have hσ : σ ≫ pr = 𝟙 X₀ := hp.lift_fst _ _ _
  have hσ2 : σ ≫ s₁ = s₀ ≫ spMap (q : R₁ →+* R₀) := hp.lift_snd _ _ _
  have hout : IsPullback (σ ≫ pr) s₀ s₀ (spMap (q : R₁ →+* R₀) ≫ spMap (algebraMap R₀ R₁)) := by
    rw [hσ, hid]; exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have hleft : IsPullback σ s₀ s₁ (spMap (q : R₁ →+* R₀)) := IsPullback.of_right hout hσ2 hp
  have hk2 : RingHom.ker (q : R₁ →+* R₀) ^ 2 = 0 := by
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    rw [Ideal.mem_bot]
    exact hq a b (RingHom.mem_ker.1 ha) (RingHom.mem_ker.1 hb)
  have hsurj : Surjective σ := surjective_of_isPullback_sqZero hk2 hqs rfl hleft
  refine ⟨σ ⁻¹ᵁ U, ?_⟩
  ext x
  obtain ⟨y, rfl⟩ := hsurj.surj x
  have e : pr (σ y) = y := by
    have := congrArg (fun f : X₀ ⟶ X₀ ↦ f y) hσ
    simpa only [Scheme.Hom.comp_apply] using this.trans (by simp)
  change σ (pr (σ y)) ∈ U ↔ σ y ∈ U
  rw [e]

end GlobalTheory.SqZeroBC
