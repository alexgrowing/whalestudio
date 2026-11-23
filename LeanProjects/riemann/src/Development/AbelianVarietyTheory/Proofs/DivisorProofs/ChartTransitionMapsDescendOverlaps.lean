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

theorem chart_transition_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (S X : Scheme.{0}) (π : S ⟶ Sp R), IsProper π → Surjective π → IsIntegral S → ∀ (U : Over (Sp R)), Flat U.hom → ∀ (J : Type) (e : J → (pullback U.hom π ⟶ X)), (∀ j, IsOpenImmersion (e j)) → (∀ (i j : J) (T : Scheme.{0}) (w₁ w₂ h₁ : T ⟶ pullback U.hom π), w₁ ≫ pullback.fst _ _ = w₂ ≫ pullback.fst _ _ → h₁ ≫ e j = w₁ ≫ e i → ∃ h₂ : T ⟶ pullback U.hom π, h₂ ≫ e j = w₂ ≫ e i ∧ h₂ ≫ pullback.fst _ _ = h₁ ≫ pullback.fst _ _) → ∀ (i j : J) (V : U.left.Opens), (∀ a : ↥(pullback U.hom π), pullback.fst U.hom π a ∈ V ↔ e i a ∈ Set.range (e j)) → ∃ τ : V.toScheme ⟶ U.left, ∀ (T : Scheme.{0}) (a b : T ⟶ pullback U.hom π) (v : T ⟶ V.toScheme), a ≫ e i = b ≫ e j → v ≫ V.ι = a ≫ pullback.fst _ _ → v ≫ τ = b ≫ pullback.fst _ _ := by
  intro R _ _ _ _ S X π hπ hs hS U hU J e he hkey i j V hV
  have hpb0 : IsPullback (pullback.fst U.hom π ∣_ V) (pullback.fst U.hom π ⁻¹ᵁ V).ι V.ι
      (pullback.fst U.hom π) := isPullback_morphismRestrict _ _
  have hpb : IsPullback (pullback.fst U.hom π ∣_ V)
      ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ pullback.snd U.hom π) (V.ι ≫ U.hom) π :=
    hpb0.paste_vert (IsPullback.of_hasPullback U.hom π)
  have hflat : Flat (V.ι ≫ U.hom) := inferInstance
  have hrange : Set.range ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i).base ⊆ Set.range (e j).base := by
    rintro _ ⟨z, rfl⟩
    have hz : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ pullback.fst U.hom π ⁻¹ᵁ V := by
      have h0 : (pullback.fst U.hom π ⁻¹ᵁ V).ι z ∈ Set.range (pullback.fst U.hom π ⁻¹ᵁ V).ι := ⟨z, rfl⟩
      rwa [Scheme.Opens.range_ι] at h0
    simpa using (hV _).1 hz
  let hZ := IsOpenImmersion.lift (e j) ((pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i) hrange
  have hZe : hZ ≫ e j = (pullback.fst U.hom π ⁻¹ᵁ V).ι ≫ e i := IsOpenImmersion.lift_fac _ _ _
  let p' := pullback.fst U.hom π ∣_ V
  have heq : pullback.fst p' p' ≫ (hZ ≫ pullback.fst U.hom π) =
      pullback.snd p' p' ≫ (hZ ≫ pullback.fst U.hom π) := by
    obtain ⟨h₂, h₂e, h₂p⟩ := hkey i j (pullback p' p') (pullback.fst p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι)
      (pullback.snd p' p' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι) (pullback.fst p' p' ≫ hZ)
      (by simp only [Category.assoc, ← morphismRestrict_ι]; rw [pullback.condition_assoc])
      (by simp only [Category.assoc, hZe])
    have : h₂ = pullback.snd p' p' ≫ hZ := by
      rw [← cancel_mono (e j), h₂e]; simp only [Category.assoc, hZe]
    subst this
    simpa only [Category.assoc] using h₂p.symm
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.T.exists_descent_of_equalised_proper_cover_normal R S V.toScheme (pullback.fst U.hom π ⁻¹ᵁ V).toScheme U.left π
    (V.ι ≫ U.hom) p' _ hπ hs hS hflat hpb _ heq
  refine ⟨τ, fun T a b v hab hv => ?_⟩
  let a' := hpb0.lift v a hv
  have ha'1 : a' ≫ p' = v := hpb0.lift_fst _ _ _
  have ha'2 : a' ≫ (pullback.fst U.hom π ⁻¹ᵁ V).ι = a := hpb0.lift_snd _ _ _
  have ha'3 : a' ≫ hZ = b := by
    rw [← cancel_mono (e j), Category.assoc, hZe, ← Category.assoc, ha'2, hab]
  rw [← ha'1, Category.assoc, hτ, ← Category.assoc, ha'3]

end GlobalTheory.Mum
