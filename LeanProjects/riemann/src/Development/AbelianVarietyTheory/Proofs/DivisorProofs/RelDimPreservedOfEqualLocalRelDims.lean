import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualCon

instance isZariskiLocalAtTarget_smoothDim (n : ℕ) : IsZariskiLocalAtTarget (@SmoothOfRelativeDimension n) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@SmoothOfRelativeDimension n)
    (Q := RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n))

theorem smoothDim_restrict_pullback {S T X : Scheme.{0}} (b : X ⟶ S) (t : T ⟶ S) (U : S.Opens) {n : ℕ}
    (h : SmoothOfRelativeDimension n (pullback.snd b U.ι)) :
    SmoothOfRelativeDimension n (pullback.snd b t ∣_ (t ⁻¹ᵁ U)) := by
  have big := (isPullback_morphismRestrict (pullback.snd b t) (t ⁻¹ᵁ U)).flip.paste_horiz
    (IsPullback.of_hasPullback b t)
  rw [← morphismRestrict_ι t U] at big
  have hc : ((pullback.snd b t ⁻¹ᵁ (t ⁻¹ᵁ U)).ι ≫ pullback.fst b t) ≫ b =
      (pullback.snd b t ∣_ (t ⁻¹ᵁ U) ≫ t ∣_ U) ≫ U.ι := by
    simp only [Category.assoc, pullback.condition, morphismRestrict_ι, morphismRestrict_ι_assoc]
  have sq := IsPullback.of_right (h₁₁ := pullback.lift _ _ hc) (by rw [pullback.lift_fst]; exact big)
    (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback b U.ι)
  exact (smoothOfRelativeDimension_isStableUnderBaseChange n).of_isPullback sq h

theorem dimLe_of_local : ∀ (S : Scheme.{0}) (A B : Over S), Surjective A.hom → ∀ (Ix : Type) (V : Ix → S.Opens) (g : Ix → ℕ), (∀ s : S, ∃ i, s ∈ V i) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd A.hom (V i).ι)) → (∀ i, SmoothOfRelativeDimension (g i) (pullback.snd B.hom (V i).ι)) → DimLe A B := by
  intro S A B hs Ix V g hV hA hB n T t hn
  have hcov : iSup (fun i => t ⁻¹ᵁ V i) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨i, hi⟩ := hV (t y)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := @SmoothOfRelativeDimension n) _ hcov fun i => ?_
  by_cases hne : ∃ y, y ∈ t ⁻¹ᵁ V i
  · obtain ⟨y, hy⟩ := hne
    have : Surjective (pullback.snd A.hom t) := by haveI := hs; infer_instance
    obtain ⟨x, hx⟩ := (pullback.snd A.hom t).surjective y
    have h1 : SmoothOfRelativeDimension n (pullback.snd A.hom t ∣_ (t ⁻¹ᵁ V i)) :=
      IsZariskiLocalAtTarget.restrict hn _
    have h2 := smoothDim_restrict_pullback A.hom t (V i) (hA i)
    have e : n = g i := ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2
      ⟨x, by rw [Scheme.Hom.mem_preimage, hx]; exact hy⟩
    rw [e]
    exact smoothDim_restrict_pullback B.hom t (V i) (hB i)
  · push_neg at hne
    exact ⟨fun x => (hne _ x.2).elim⟩

end GlobalTheory.DualCon
