import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsDomainAndIsIntegrallyClosedLocalizationOfIsInv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

theorem exists_action_of_isPullback {Γ : Type} [Group Γ] {X X' Y Y' : Scheme.{0}}
    (ρ : Γ →* Aut X) {π : X ⟶ X'} {φ : Y ⟶ Y'} {p : Y ⟶ X} {p' : Y' ⟶ X'}
    (hπ : ∀ g, (ρ g).hom ≫ π = π) (H : IsPullback p φ π p') :
    ∃ τ : Γ →* Aut Y, ∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ p = p ≫ (ρ g).hom := by
  have hc : ∀ g : Γ, (p ≫ (ρ g).hom) ≫ π = φ ≫ p' := fun g => by
    rw [Category.assoc, hπ g, H.w]
  let e : Γ → (Y ⟶ Y) := fun g => H.lift (p ≫ (ρ g).hom) φ (hc g)
  have e_p : ∀ g, e g ≫ p = p ≫ (ρ g).hom := fun g => H.lift_fst _ _ _
  have e_φ : ∀ g, e g ≫ φ = φ := fun g => H.lift_snd _ _ _
  have e_one : e 1 = 𝟙 Y := H.hom_ext
    (by rw [e_p, map_one]; exact (Category.comp_id p).trans (Category.id_comp p).symm)
    (by rw [e_φ, Category.id_comp])
  have e_mul : ∀ g h, e (g * h) = e h ≫ e g := fun g h => H.hom_ext
    (by
      rw [e_p, Category.assoc, e_p, ← Category.assoc, e_p, Category.assoc, map_mul]
      rfl)
    (by rw [e_φ, Category.assoc, e_φ, e_φ])
  let τf : Γ → Aut Y := fun g =>
    { hom := e g
      inv := e g⁻¹
      hom_inv_id := by rw [← e_mul, inv_mul_cancel, e_one]
      inv_hom_id := by rw [← e_mul, mul_inv_cancel, e_one] }
  refine ⟨{ toFun := τf, map_one' := ?_, map_mul' := ?_ }, fun g => ⟨e_φ g, e_p g⟩⟩
  · exact Iso.ext e_one
  · intro g h
    exact Iso.ext (e_mul g h)

theorem quotient_flat_baseChange :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (X X' Y Y' : Scheme.{0}) (ρ : Γ →* Aut X) (π : X ⟶ X') (φ : Y ⟶ Y') (p : Y ⟶ X) (p' : Y' ⟶ X'), (IsAffineHom π ∧ (∀ g, (ρ g).hom ≫ π = π) ∧ ∀ V : X'.Opens, Function.Injective (π.app V).hom ∧ ∀ f : Γ(X, π ⁻¹ᵁ V), (∀ g (h : π ⁻¹ᵁ V ≤ (ρ g).hom ⁻¹ᵁ (π ⁻¹ᵁ V)), ((ρ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (π.app V).hom) → IsPullback φ p p' π → Flat p' → (∃ τ : Γ →* Aut Y, ∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ p = p ≫ (ρ g).hom) ∧ ∀ τ : Γ →* Aut Y, (∀ g, (τ g).hom ≫ φ = φ ∧ (τ g).hom ≫ p = p ≫ (ρ g).hom) → (IsAffineHom φ ∧ (∀ g, (τ g).hom ≫ φ = φ) ∧ ∀ V : Y'.Opens, Function.Injective (φ.app V).hom ∧ ∀ f : Γ(Y, φ ⁻¹ᵁ V), (∀ g (h : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ (φ ⁻¹ᵁ V)), ((τ g).hom.appLE _ _ h).hom f = f) → f ∈ Set.range (φ.app V).hom) := by
  intro Γ _ _ X X' Y Y' ρ π φ p p' hq H hflat
  obtain ⟨hπa, hπ, hV⟩ := hq
  refine ⟨exists_action_of_isPullback ρ hπ H.flip, fun τ hτ => ?_⟩
  have hQ : IsAffineQuotient ρ π :=
    { comp_eq := hπ
      isAffineHom := hπa
      app_injective := fun W => (hV W).1
      mem_range_app := fun W s hs => (hV W).2 s (by
        unfold IsInvariantSection at hs
        intro g h
        obtain ⟨_, e⟩ := hs g
        exact e) }
  haveI := hflat
  have hB := hQ.of_isPullback H.flip (fun g => (hτ g).2) (fun g => (hτ g).1)
  exact ⟨hB.isAffineHom, hB.comp_eq, fun V => ⟨hB.app_injective V, fun f hf => hB.mem_range_app V f (by
    unfold IsInvariantSection
    intro g
    have hle : φ ⁻¹ᵁ V ≤ (τ g).hom ⁻¹ᵁ φ ⁻¹ᵁ V := by
      rw [← Scheme.Hom.comp_preimage, (hτ g).1]
    exact ⟨hle, hf g hle⟩)⟩⟩

end GlobalTheory
