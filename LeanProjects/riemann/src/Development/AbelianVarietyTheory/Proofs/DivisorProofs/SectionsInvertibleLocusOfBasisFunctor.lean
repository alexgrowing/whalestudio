import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCocycleCoboundaryCommaLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueCommaOfBasis
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh.Desc

theorem sec_of_basis_unit : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → F.obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp F u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (T : C) (e : F.obj T) (s : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), IsUnit (mp F u e) → s t' (u ≫ G.map a) = mp F (G.map a) (s t u)) → ∃ x : ∀ S, (T ⟶ S) → F.obj S, Desc.IsSec F (fun S u ↦ IsUnit (mp F u e)) x ∧ ∀ t (u : T ⟶ G.obj t), IsUnit (mp F u e) → x (G.obj t) u = s t u := by
  intro R _ C _ C' _ F G _ _ H hcov hdir T e s hs
  have uniq : ∀ (S : C) (y : F.obj S), (∀ t (w : S ⟶ G.obj t), mp F w y = 0) → y = 0 := by
    intro S y hy
    obtain ⟨n, b, hb, hb'⟩ := hcov S
    refine sep_std H hb y fun S'' u' ⟨i, hi⟩ ↦ ?_
    obtain ⟨t, v, w, rfl⟩ := hb' i S'' u' hi
    rw [mp_comp, hy t v, map_zero]
  have hex : ∀ S (u : T ⟶ S), ∃ y : F.obj S, IsUnit (mp F u e) →
      ∀ t (w : S ⟶ G.obj t), mp F w y = s t (u ≫ w) := by
    intro S u
    by_cases h : IsUnit (mp F u e)
    · obtain ⟨y, hy⟩ := glue_comma_of_basis F G H hcov hdir S (fun t w ↦ s t (u ≫ w))
        fun t t' w a ↦ by
          rw [← Category.assoc]
          exact hs t t' (u ≫ w) a (isUnit_comp w h)
      exact ⟨y, fun _ ↦ hy⟩
    · exact ⟨0, fun h' ↦ absurd h' h⟩
  choose x hx using hex
  refine ⟨x, fun S S' u ψ hu ↦ sub_eq_zero.1 (uniq S' _ fun t w ↦ ?_), fun t u hu ↦ ?_⟩
  · rw [map_sub, hx S' (u ≫ ψ) (isUnit_comp ψ hu) t w, ← mp_comp, hx S u hu t (ψ ≫ w),
      Category.assoc, sub_self]
  · have := hx (G.obj t) u hu t (𝟙 _)
    rwa [mp_id, Category.comp_id] at this

end GlobalTheory.CatCoh.Desc
