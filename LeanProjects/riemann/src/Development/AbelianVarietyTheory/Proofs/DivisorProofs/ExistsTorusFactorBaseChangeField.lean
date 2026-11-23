import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SplitTorusToAbelianVarietyConst
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem isMonHom_of_comp_mono_torus {C : Type*} [Category C] [CartesianMonoidalCategory C] {M N P : C}
    [MonObj M] [MonObj N] [MonObj P] (e : M ⟶ N) (i : N ⟶ P) [Mono i] [IsMonHom i] [IsMonHom (e ≫ i)] :
    IsMonHom e := by
  constructor
  · rw [← cancel_mono i, Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · rw [← cancel_mono i, Category.assoc, Category.assoc, IsMonHom.mul_hom, IsMonHom.mul_hom,
      ← Category.assoc, ← tensorHom_comp_tensorHom]

theorem exists_torus_factor : ∀ (k k' : Type) [CommRing k] [CommRing k'], IsField k' → ∀ (ρ : k →+* k') (G₀ : Over (Sp k)) [GrpObj G₀] (G'₀ : Over (Sp k')) [GrpObj G'₀] (β₀ : G'₀.left ⟶ G₀.left), IsGrpPullback G'₀ G₀ (spMap ρ) β₀ → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] (Q₀ : GlobalTheory.UU.TQ G₀ X) (Q'₀ : GlobalTheory.UU.TQ G'₀ X'), ∃ (i₁ : splitTorus (Sp k') X ⟶ G'₀) (e : splitTorus (Sp k') X ⟶ splitTorus (Sp k') X'), IsMonHom e ∧ e ≫ Q'₀.i = i₁ ∧ GlobalTheory.UU.TorusCompat (spMap ρ) β₀ i₁ Q₀.i := by
  intro k k' _ _ hk' ρ G₀ _ G'₀ _ β₀ hβ₀ X X' _ _ _ _ Q₀ Q'₀
  letI : Field k' := hk'.toField
  obtain ⟨i₁, h₁, -⟩ := GlobalTheory.UU.existsUnique_torusCompat hβ₀.1 Q₀.i
  haveI := Q₀.i_hom
  haveI := Q'₀.i_hom
  haveI := Q'₀.q_hom
  haveI hi₁ : IsMonHom i₁ := GlobalTheory.UU.TorusCompat.isMonHom hβ₀ h₁
  haveI : IsProper Q'₀.B.hom := Q'₀.isAb.proper
  have hc : i₁ ≫ Q'₀.q = toUnit _ ≫ η[Q'₀.B] := by
    have h := GlobalTheory.TorusConst.eq_const (K := k') X (i₁ ≫ Q'₀.q)
    rw [IsMonHom.one_hom] at h
    exact h
  let e := Q'₀.isKernel.lift i₁ (toUnit _) hc
  have he : e ≫ Q'₀.i = i₁ := Q'₀.isKernel.lift_fst _ _ hc
  haveI : Mono Q'₀.i := by
    haveI : Mono (η[Q'₀.B]) := ⟨fun a b _ => toUnit_unique a b⟩
    exact Q'₀.isKernel.mono_fst_of_mono
  haveI : IsMonHom (e ≫ Q'₀.i) := he ▸ hi₁
  exact ⟨i₁, e, isMonHom_of_comp_mono_torus e Q'₀.i, he, h₁⟩

end GlobalTheory.Mum
