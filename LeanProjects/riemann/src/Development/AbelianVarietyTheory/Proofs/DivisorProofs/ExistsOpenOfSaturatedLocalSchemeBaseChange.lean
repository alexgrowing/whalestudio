import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_open_of_saturated_stalkBaseChange : ∀ (S S₁ P : Scheme.{0}) (p : P ⟶ S) (x : S) (ξ' : S₁ ⟶ Spec (S.presheaf.stalk x)) (ξ : S₁ ⟶ S), ξ' ≫ S.fromSpecStalk x = ξ → Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ O : Set ↥(Limits.pullback p ξ), IsOpen O → (∀ w w' : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w = Limits.pullback.fst p ξ w' → w ∈ O → w' ∈ O) → ∃ V : P.Opens, ∀ w : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w ∈ V ↔ w ∈ O := by
  intro S S₁ P p x ξ' ξ hξ hfl hsu hqc O hO hsat
  subst hξ
  obtain ⟨π, hπ, hπ2⟩ : ∃ π : pullback p (ξ' ≫ S.fromSpecStalk x) ⟶ pullback p (S.fromSpecStalk x),
      π ≫ pullback.fst p (S.fromSpecStalk x) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) ∧
      π ≫ pullback.snd p (S.fromSpecStalk x) = pullback.snd p (ξ' ≫ S.fromSpecStalk x) ≫ ξ' :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ') (by rw [Category.assoc]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback π (pullback.snd p (ξ' ≫ S.fromSpecStalk x)) (pullback.snd p (S.fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ2 (IsPullback.of_hasPullback p (S.fromSpecStalk x))
    rw [hπ]
    exact IsPullback.of_hasPullback p (ξ' ≫ S.fromSpecStalk x)
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) hsq.flip hfl
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hsu
  have : QuasiCompact π := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hqc
  have hq := Flat.isQuotientMap_of_surjective π
  have hc : ∀ w, pullback.fst p (S.fromSpecStalk x) (π w) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) w := by
    intro w; rw [← Scheme.Hom.comp_apply, hπ]
  have hpre : π ⁻¹' (π '' O) = O := by
    ext w; constructor
    · rintro ⟨w', hw', he⟩
      exact hsat w' w (by rw [← hc, ← hc, he]) hw'
    · intro hw; exact ⟨w, hw, rfl⟩
  have hopen : IsOpen (π '' O) := by
    rw [← hq.isOpen_preimage, hpre]; exact hO
  have hemb := IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecStalk x))
  obtain ⟨t, ht, hte⟩ := hemb.isInducing.isOpen_iff.1 hopen
  refine ⟨⟨t, ht⟩, fun w => ?_⟩
  change _ ∈ t ↔ _
  rw [← hc, ← Set.mem_preimage, hte, ← Set.mem_preimage, hpre]

end GlobalTheory.Desc
