import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AlphaPMultiplicativeCharacterEqOneStatement

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj

namespace GlobalTheory.AlphaPair

def unitsOfΓ {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A] [Algebra Ω A] :
    Γ((overAt s A).left, ⊤)ˣ →* Aˣ :=
  Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom

theorem unitsOfΓ_injective {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) (A : Type) [CommRing A]
    [Algebra Ω A] : Function.Injective (unitsOfΓ s A) :=
  Units.map_injective (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1

theorem unitsOfΓ_natural {S : Scheme.{0}} {Ω : Type} [Field Ω] (s : Sp Ω ⟶ S) {A B : Type} [CommRing A]
    [Algebra Ω A] [CommRing B] [Algebra Ω B] (f : A →ₐ[Ω] B) (ζ : Γ((overAt s A).left, ⊤)ˣ) :
    unitsOfΓ s B (Units.map (homAt s f).left.appTop.hom.toMonoidHom ζ) = Units.map (f : A →* B) (unitsOfΓ s A ζ) := by
  have h₁ := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (f : A →+* B))
  exact Units.ext (congrArg (fun φ => φ.hom ζ.val) h₁)

theorem cubWeil_alpha_rational : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (g : Fam s G), IsAlpha p s G g → ∀ x : overAt s Ω ⟶ G, x ^ p = 1 → ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) 1 := by
  intro Ω _ p _ _ S s G _ _ L c g hg x hx
  classical
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  have hex : ∀ (A : Type) [CommRing A] [Algebra Ω A] (a : A), ∃ ζ : Γ((overAt s A).left, ⊤)ˣ,
      a ^ p = 0 → CubWeil c p (g A a) (homAt s (Algebra.ofId Ω A) ≫ x) ζ := by
    intro A _ _ a
    by_cases ha : a ^ p = 0
    · obtain ⟨ζ, hζ, -⟩ := UU.existsUnique_cubWeil c (hg.pow_eq_one hp ha)
        (y := homAt s (Algebra.ofId Ω A) ≫ x) (by rw [← MonObj.comp_pow, hx, MonObj.comp_one])
      exact ⟨ζ, fun _ => hζ⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose ζ hζ using hex
  intro A _ _ a ha
  have key := GlobalTheory.T.alphaP_multiplicativeCharacter_eq_one Ω p (fun A _ _ a => unitsOfΓ s A (ζ A a)) ?_ ?_ A a ha
  · have : ζ A a = 1 := unitsOfΓ_injective s A (key.trans (map_one _).symm)
    exact this ▸ hζ A a ha
  · intro A B _ _ _ _ f a ha
    beta_reduce
    have hb : f a ^ p = 0 := by rw [← map_pow, ha, map_zero]
    have h₁ := (hζ A a ha).comp (homAt s f)
    rw [← hg.1 A B f a ha, ← Category.assoc, hom_comp, Subsingleton.elim (f.comp (Algebra.ofId Ω A)) (Algebra.ofId Ω B)] at h₁
    rw [(hζ B (f a) hb).unique h₁, unitsOfΓ_natural]
  · intro A _ _ a a' ha ha'
    beta_reduce
    have hs : (a + a') ^ p = 0 := by
      rcases subsingleton_or_nontrivial A with _ | _
      · exact Subsingleton.elim _ _
      · haveI : CharP A p := charP_of_injective_algebraMap (algebraMap Ω A).injective p
        rw [add_pow_char, ha, ha', add_zero]
    have h₁ := (hζ A a ha).mul_left (hζ A a' ha')
    rw [← hg.2 A a a' ha ha'] at h₁
    rw [(hζ A (a + a') hs).unique h₁, map_mul]

end GlobalTheory.AlphaPair
end
