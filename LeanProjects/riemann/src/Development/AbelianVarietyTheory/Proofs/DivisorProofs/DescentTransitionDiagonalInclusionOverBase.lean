import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDescentOfEqualisedProperCoverNormalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem descend_transition_diag_over : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R) (f : X ⟶ S), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ j, e j ≫ f = pullback.snd _ _) → ∀ (V : J → J → U.left.Opens) (τ : ∀ i j, (V i j).toScheme ⟶ U.left), (∀ (i j : J) (a : ↥(pullback U.hom π)), pullback.fst U.hom π a ∈ V i j ↔ e i a ∈ Set.range (e j)) → (∀ (i j : J) (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ (V i j).toScheme), a ≫ e i = b ≫ e j → v ≫ (V i j).ι = a ≫ pullback.fst _ _ → v ≫ τ i j = b ≫ pullback.fst _ _) → (∀ i, τ i i = (V i i).ι) ∧ (∀ i j, τ i j ≫ U.hom = (V i j).ι ≫ U.hom) := by
  intro R _ _ _ _ S X π f hprop hsurj hint U hU J e he hef V τ hV hτ

  have hsq : ∀ O : U.left.Opens, IsPullback (pullback.fst U.hom π ∣_ O)
      ((pullback.fst U.hom π ⁻¹ᵁ O).ι ≫ pullback.snd U.hom π) (O.ι ≫ U.hom) π := fun O =>
    (IsPullback.paste_horiz (isPullback_morphismRestrict (pullback.fst U.hom π) O).flip
      (IsPullback.of_hasPullback U.hom π).flip).flip
  have huniq : ∀ (O : U.left.Opens) (W : Scheme.{0}) (g₁ g₂ : O.toScheme ⟶ W),
      (pullback.fst U.hom π ∣_ O) ≫ g₁ = (pullback.fst U.hom π ∣_ O) ≫ g₂ → g₁ = g₂ :=
    fun O W g₁ g₂ h => GlobalTheory.MorDescent.uniq R S O.toScheme _ π (O.ι ≫ U.hom) _ _ hprop hsurj hint
      inferInstance (hsq O) W g₁ g₂ h
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · apply huniq (V i i)
    have := hτ i i _ (pullback.fst U.hom π ⁻¹ᵁ V i i).ι (pullback.fst U.hom π ⁻¹ᵁ V i i).ι
      (pullback.fst U.hom π ∣_ V i i) rfl (morphismRestrict_ι _ _)
    rw [this, morphismRestrict_ι]
  · apply huniq (V i j)
    set Z := pullback.fst U.hom π ⁻¹ᵁ V i j
    have hr : Set.range (Z.ι ≫ e i) ⊆ Set.range (e j) := by
      rintro _ ⟨z, rfl⟩
      have hz : pullback.fst U.hom π (Z.ι z) ∈ V i j := by
        have h0 : Z.ι z = z.1 := Scheme.Opens.ι_apply _ _
        rw [h0]; exact z.2
      exact (hV i j (Z.ι z)).1 hz
    set b := IsOpenImmersion.lift (e j) (Z.ι ≫ e i) hr
    have hb : b ≫ e j = Z.ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
    have h1 := hτ i j _ Z.ι b (pullback.fst U.hom π ∣_ V i j) hb.symm (morphismRestrict_ι _ _)
    have hbs : b ≫ pullback.snd U.hom π = Z.ι ≫ pullback.snd U.hom π := by
      calc b ≫ pullback.snd U.hom π = b ≫ e j ≫ f := by rw [hef]
        _ = Z.ι ≫ e i ≫ f := by rw [← Category.assoc, hb, Category.assoc]
        _ = Z.ι ≫ pullback.snd U.hom π := by rw [hef]
    rw [← Category.assoc, h1, Category.assoc, pullback.condition, ← Category.assoc, hbs,
      Category.assoc, ← pullback.condition, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]

end GlobalTheory.Mum
