import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPullbackDvrTorsionPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationGenericFibreEqSiegelFibrePullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointSiegelFibreEqLevelSectionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointOfPairExistsTorsionInjectiveUpToEquiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoTraitUniformisationsMatchingDataStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj.Pair

theorem exists_ext {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    (hf : Function.Injective f) :
    ∃ j : AlgebraicClosure (FractionRing R) →+* AlgebraicClosure (FractionRing V), Ext f j := by
  let g : R →+* AlgebraicClosure (FractionRing V) :=
    (algebraMap (FractionRing V) _).comp ((algebraMap V (FractionRing V)).comp f)
  have hg : Function.Injective g :=
    (algebraMap (FractionRing V) (AlgebraicClosure (FractionRing V))).injective.comp
      ((IsFractionRing.injective V (FractionRing V)).comp hf)
  letI : Algebra (FractionRing R) (AlgebraicClosure (FractionRing V)) := (IsFractionRing.lift hg).toAlgebra
  refine ⟨(IsAlgClosed.lift : AlgebraicClosure (FractionRing R) →ₐ[FractionRing R]
    AlgebraicClosure (FractionRing V)).toRingHom, fun r => ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap]
  rfl

theorem sq {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (f : R →+* V)
    {F₀ F : Type} [Field F₀] [Algebra (FractionRing R) F₀] [Field F] [Algebra (FractionRing V) F]
    (j : F₀ →+* F) (hj : Ext f j) (κ : Sp (FractionRing V) ⟶ Sp (FractionRing R))
    (hκ : κ ≫ jK R = jK V ≫ spMap f) :
    spMap j ≫ jFK (R := R) F₀ = jFK (R := V) F ≫ κ := by
  haveI : Mono (jK R) :=
    haveI := IsPreimmersion.of_isLocalization (R := CommRingCat.of R) (S := CommRingCat.of (FractionRing R))
      (nonZeroDivisors R)
    inferInstanceAs (Mono (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))))
  rw [← cancel_mono (jK R), Category.assoc, Category.assoc, hκ]
  simp only [jFK, jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext r
  exact hj r

end GlobalTheory.TInj.Pair

theorem GlobalTheory.TInj.pull_pair_match : ∀ {X : Scheme.{0}} {g n : ℕ} {B : Type} [CommRing B] {ζ : B} {sX : X ⟶ Sp B} (c : SiegPre g n ζ sX), IsUnit ζ → 1 ≤ n → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (J : Ideal R), AdmBase R J → ∀ (D₀ : DegData R J) (A₀ : PolAV (Sp (FractionRing R))) (G₀ : Over (Sp R)) [GrpObj G₀] [IsCommMonObj G₀] (U₀ : Unif J D₀ A₀ G₀), IsSemiAbelian G₀ → ∀ (y₀ : Sp (FractionRing R) ⟶ X) (α₀ : A₀.A.left ⟶ c.A.left), OverPt c A₀ y₀ α₀ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → J.map f₁ ≤ maximalIdeal V → J.map f₂ ≤ maximalIdeal V → ∀ κ₁ κ₂ : Sp (FractionRing V) ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK V ≫ spMap f₁ → κ₂ ≫ jK R = jK V ≫ spMap f₂ → κ₁ ≫ y₀ = κ₂ ≫ y₀ → ∃ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ D₀.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ D₀.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ : D₁.toPre.X ≃+ D₂.toPre.X), Ext f₁ j₁ ∧ Ext f₂ j₂ ∧ Match D₁.toPre D₂.toPre b φ (AlgebraicClosure (FractionRing V)) ∧ (∀ p₀ : QkPt D₀.toPre (AlgebraicClosure (FractionRing R)) n, ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) n) (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) n), p₁.y = hD₁.xe.symm p₀.y ∧ Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ QImg b φ p₁ p₂) := by
  intro X g n B _ ζ sX c hζ hn R _ _ _ J hJ D₀ A₀ G₀ _ _ U₀ hG₀ y₀ α₀ hO V _ _ _ _ hV f₁ f₂ hf₁ hf₂ hJ₁ hJ₂
    κ₁ κ₂ hκ₁ hκ₂ hy
  obtain ⟨D₁, hD₁, A₁, U₁, hG₁, hU₁, tr₁⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₁ hf₁ hJ₁
  obtain ⟨D₂, hD₂, A₂, U₂, hG₂, hU₂, tr₂⟩ := GlobalTheory.T.uniformisation_pullback_dvr_torsionPoints R J hJ D₀ A₀ G₀ U₀ hG₀ V hV f₂ hf₂ hJ₂
  obtain ⟨α₁, hO₁, hα₁⟩ := GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₁ D₁ hD₁ A₁ U₁ hU₁ y₀ α₀ hO κ₁ hκ₁
  obtain ⟨α₂, hO₂, hα₂⟩ := GlobalTheory.T.uniformisation_genericFibre_eq_siegelFibre_pullback c R V J (maximalIdeal V) D₀ A₀ G₀ U₀ f₂ D₂ hD₂ A₂ U₂ hU₂ y₀ α₀ hO κ₂ hκ₂
  rw [← hy] at hO₂
  obtain ⟨b, φ, hM, hQ⟩ := GlobalTheory.T.two_trait_uniformisations_matching_data c V hV D₁ A₁ _ U₁ D₂ A₂ _ U₂ hG₁ hG₂ (κ₁ ≫ y₀) α₁ α₂ hO₁ hO₂
  obtain ⟨j₁, hj₁⟩ := GlobalTheory.TInj.Pair.exists_ext f₁ hf₁
  obtain ⟨j₂, hj₂⟩ := GlobalTheory.TInj.Pair.exists_ext f₂ hf₂
  refine ⟨D₁, D₂, hD₁, hD₂, j₁, j₂, b, φ, hj₁, hj₂, hM, fun p₀ => ?_⟩
  obtain ⟨x₀, hx₀, hpow⟩ := (GlobalTheory.T.torsionPointOfPair_exists_torsion_injective_upToEquiv R J hJ D₀ A₀ G₀ U₀ hG₀ (AlgebraicClosure (FractionRing R)) n hn).1 p₀
  obtain ⟨l, hl⟩ := GlobalTheory.T.torsionPoint_siegelFibre_eq_levelSection c hζ A₀.A y₀ α₀ hO.1 (AlgebraicClosure (FractionRing R))
    (jFK (R := R) (AlgebraicClosure (FractionRing R))) x₀ hpow
  obtain ⟨p₁, x₁, hy₁, hT₁, hq₁, hc₁⟩ := tr₁ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₁ hj₁ n hn p₀ x₀ hx₀
  obtain ⟨p₂, x₂, hy₂, hT₂, hq₂, hc₂⟩ := tr₂ (AlgebraicClosure (FractionRing R)) (AlgebraicClosure (FractionRing V))
    j₂ hj₂ n hn p₀ x₀ hx₀
  have e₁ := hα₁ _ x₁.left (spMap j₁ ≫ x₀.left) (hc₁.trans (Category.assoc _ _ _).symm)
  have e₂ := hα₂ _ x₂.left (spMap j₂ ≫ x₀.left) (hc₂.trans (Category.assoc _ _ _).symm)
  have s₁ := GlobalTheory.TInj.Pair.sq f₁ j₁ hj₁ κ₁ hκ₁
  have s₂ := GlobalTheory.TInj.Pair.sq f₂ j₂ hj₂ κ₂ hκ₂
  have key : x₁.left ≫ α₁ = x₂.left ≫ α₂ := by
    rw [e₁, e₂, Category.assoc, Category.assoc, hl, ← Category.assoc, ← Category.assoc (spMap j₂), s₁, s₂,
      Category.assoc, Category.assoc, ← Category.assoc κ₁, ← Category.assoc κ₂, hy]
  exact ⟨p₁, p₂, hy₁, hT₁, hy₂, hT₂, hQ n hn p₁ p₂ x₁ x₂ hq₁ hq₂ key⟩
