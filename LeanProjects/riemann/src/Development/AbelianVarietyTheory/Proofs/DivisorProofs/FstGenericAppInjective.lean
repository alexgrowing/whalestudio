import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioEqRefl
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fst_generic_app_injective {R : Type} [CommRing R] [IsDomain R] {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    (W : X.Opens) : Function.Injective ((pullback.fst p (jK R)).app W).hom := by
  have : IsDominant (jK R) := by
    refine ⟨?_⟩
    change DenseRange (PrimeSpectrum.comap (algebraMap R (FractionRing R)))
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))]
    exact bot_le
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have : IsSchemeTheoreticallyDominant (pullback.fst p (jK R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback p (jK R)).flip
  exact (pullback.fst p (jK R)).app_injective W

theorem SecRatioEq.of_comp {X Y Z : Scheme.{0}} (L : LB X) {k k' : ℕ} (f : Z ⟶ Y)
    (hf : ∀ W : Y.Opens, Function.Injective (f.app W).hom) (u v : Y ⟶ X) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k')
    (h : SecRatioEq L (f ≫ u) (f ≫ v) s₁ s₂ t₁ t₂) : SecRatioEq L u v s₁ s₂ t₁ t₂ := by
  intro i i'
  apply hf
  have key : ∀ {U V : Y.Opens} (e : U ≤ V) (a : Γ(Y, V)),
      (f.app U).hom ((Y.presheaf.map (homOfLE e).op).hom a) =
        (Z.presheaf.map (homOfLE (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ V from fun _ hx => e hx)).op).hom ((f.app V).hom a) := by
    intro U V e a
    exact congrArg (fun φ => φ.hom a) (f.naturality (homOfLE e).op)
  rw [map_mul, map_mul, key, key, key, key]
  exact h i i'

theorem secRatioEq_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (k k' : ℕ) (s₁ s₂ : H0 U.LG.L k) (t₁ t₂ : H0 U.LG.L k') (φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ t₁ t₂ → ∀ g : G ⟶ G, (Over.pullback (jK R)).map g = φ → SecRatioEq U.LG.L g.left (𝟙 G.left) s₁ s₂ t₁ t₂ := by
  intro R _ _ _ _ D A G _ _ _ U k k' s₁ s₂ t₁ t₂ φ h g hg
  subst hg
  have := U.smooth
  refine SecRatioEq.of_comp _ (pullback.fst G.hom (jK R)) (fst_generic_app_injective G.hom) _ _ _ _ _ _ ?_
  have e : ((Over.pullback (jK R)).map g).left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ g.left :=
    pullback.lift_fst _ _ _
  rw [Category.comp_id, ← e]
  exact h

end GlobalTheory.Mum
