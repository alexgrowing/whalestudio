import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OverExtOfPoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
noncomputable section

namespace GlobalTheory.Desc

theorem exists_desc_specStalk : ∀ (R : Type) [CommRing R] [IsDomain R] (f : R), f ≠ 0 → ∀ (x : Sp R)
    (S₁ B Z B₀ B₁ : Scheme.{0}) (ξ' : S₁ ⟶ Spec ((Sp R).presheaf.stalk x)), Flat ξ' → Surjective ξ' →
    QuasiCompact ξ' → ∀ (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R), Flat pB → IsSeparated pZ →
    ∀ (φ₀ : B₀ ⟶ B) (q₀ : B₀ ⟶ Sp (Localization.Away f)) (u₀ : B₀ ⟶ Z) (φ₁ : B₁ ⟶ B) (q₁ : B₁ ⟶ S₁)
      (u₁ : B₁ ⟶ Z), IsPullback φ₀ q₀ pB (awayMap f) → IsPullback φ₁ q₁ pB (ξ' ≫ (Sp R).fromSpecStalk x) →
    u₁ ≫ pZ = φ₁ ≫ pB →
    (∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t₁ : T ⟶ B₁), t₀ ≫ φ₀ = t₁ ≫ φ₁ → t₀ ≫ u₀ = t₁ ≫ u₁) →
    ∃ u : Limits.pullback pB ((Sp R).fromSpecStalk x) ⟶ Z, u ≫ pZ = Limits.pullback.fst _ _ ≫ pB ∧
      ∀ (T : Scheme.{0}) (t₀ : T ⟶ B₀) (t : T ⟶ Limits.pullback pB ((Sp R).fromSpecStalk x)),
        t₀ ≫ φ₀ = t ≫ Limits.pullback.fst _ _ → t₀ ≫ u₀ = t ≫ u := by
  intro R _ _ f hf x S₁ B Z B₀ B₁ ξ' hξf hξs hξq pB pZ hpB hpZ φ₀ q₀ u₀ φ₁ q₁ u₁ h₀ h₁ hu₁ H
  have hs : Flat ((Sp R).fromSpecStalk x) := GenericExt.flat_fromSpecStalk _ x
  let π : B₁ ⟶ pullback pB ((Sp R).fromSpecStalk x) :=
    pullback.lift φ₁ (q₁ ≫ ξ') (by rw [h₁.w, Category.assoc])
  have hπ₁ : π ≫ pullback.fst _ _ = φ₁ := pullback.lift_fst _ _ _
  have hπ₂ : π ≫ pullback.snd _ _ = q₁ ≫ ξ' := pullback.lift_snd _ _ _
  have hsq : IsPullback π q₁ (pullback.snd pB ((Sp R).fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ₂ (IsPullback.of_hasPullback pB ((Sp R).fromSpecStalk x))
    rw [hπ₁]; exact h₁
  have : Flat π := MorphismProperty.of_isPullback hsq.flip hξf
  have : Surjective π := MorphismProperty.of_isPullback hsq.flip hξs
  have : QuasiCompact π := MorphismProperty.of_isPullback hsq.flip hξq
  have : Flat φ₁ := by rw [← hπ₁]; infer_instance
  have key : pullback.fst π π ≫ u₁ = pullback.snd π π ≫ u₁ := by
    let g : pullback π π ⟶ Sp R := pullback.fst π π ≫ φ₁ ≫ pB
    have hg : Flat g := inferInstance
    have hφ : pullback.fst π π ≫ φ₁ = pullback.snd π π ≫ φ₁ := by
      rw [← hπ₁, pullback.condition_assoc]
    have hAf : IsSchemeTheoreticallyDominant (awayMap f) :=
      schDom_spec_map _ (IsLocalization.injective (Localization.Away f)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hf))
    have hdom : IsSchemeTheoreticallyDominant (pullback.fst g (awayMap f)) :=
      IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback g (awayMap f)).flip
    refine ext_of_schDom pZ ?_ (pullback.fst g (awayMap f)) ?_
    · simp only [Category.assoc, hu₁]; exact (reassoc_of% hφ) pB
    · let t₀ : pullback g (awayMap f) ⟶ B₀ :=
        h₀.lift (pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁) (pullback.snd g (awayMap f))
          (by simpa [g] using pullback.condition (f := g) (g := awayMap f))
      have ht₀ : t₀ ≫ φ₀ = pullback.fst g (awayMap f) ≫ pullback.fst π π ≫ φ₁ := h₀.lift_fst _ _ _
      have e₁ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.fst π π) (by rw [ht₀, Category.assoc])
      have e₂ := H _ t₀ (pullback.fst g (awayMap f) ≫ pullback.snd π π) (by rw [ht₀, Category.assoc, hφ])
      simp only [Category.assoc] at e₁ e₂
      rw [← e₁, ← e₂]
  have hE : EffectiveEpi π := by
    set_option synthInstance.maxHeartbeats 400000 in infer_instance
  let u := EffectiveEpi.desc π u₁ (fun a b hab => by
    have := congrArg (pullback.lift a b hab ≫ ·) key
    simpa only [pullback.lift_fst_assoc, pullback.lift_snd_assoc] using this)
  have hu : π ≫ u = u₁ := EffectiveEpi.fac _ _ _
  have : Epi π := Flat.epi_of_flat_of_surjective π
  refine ⟨u, ?_, ?_⟩
  · rw [← cancel_epi π, reassoc_of% hu, hu₁, reassoc_of% hπ₁]
  · intro T t₀ t ht
    have : Epi (pullback.fst t π) := Flat.epi_of_flat_of_surjective _
    rw [← cancel_epi (pullback.fst t π), pullback.condition_assoc, hu]
    have := H _ (pullback.fst t π ≫ t₀) (pullback.snd t π) (by
      rw [Category.assoc, ht, pullback.condition_assoc, hπ₁])
    simpa only [Category.assoc] using this

end GlobalTheory.Desc
