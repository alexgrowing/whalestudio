import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsQkPullEquiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsMonHomIffOfIsGrpPullback

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.PointDescent

theorem exists_lift {X I G H : Type*} [AddGroup X] [Group G] [Group H] (b : I → X)
    (hb : AddSubgroup.closure (Set.range b) = ⊤) (a : X → G) (ha : ∀ y z, a (y + z) = a y * a z) (β : H →* G)
    (hβ : Function.Injective β) (x₀ : I → H) (hx : ∀ k, a (b k) = β (x₀ k)) :
    ∃ c₀ : X → H, (∀ y z, c₀ (y + z) = c₀ y * c₀ z) ∧ ∀ y, a y = β (c₀ y) := by
  have h0 : a 0 = 1 := by
    have := ha 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have key : ∀ y, ∃ x, a y = β x := fun y => by
    have hy : y ∈ AddSubgroup.closure (Set.range b) := hb ▸ AddSubgroup.mem_top y
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact ⟨_, hx k⟩
    | zero => exact ⟨1, by rw [h0, map_one]⟩
    | add y z _ _ hy hz =>
      obtain ⟨u, hu⟩ := hy
      obtain ⟨v, hv⟩ := hz
      exact ⟨u * v, by rw [ha, hu, hv, map_mul]⟩
    | neg y _ hy =>
      obtain ⟨u, hu⟩ := hy
      refine ⟨u⁻¹, ?_⟩
      rw [map_inv, ← hu, eq_inv_iff_mul_eq_one, ← ha, neg_add_cancel, h0]
  choose c₀ hc using key
  exact ⟨c₀, fun y z => hβ (by rw [map_mul, ← hc, ← hc, ← hc, ha]), hc⟩

theorem exists_descent {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} [Epi f]
    {Φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f Φ) {X I : Type*} [AddGroup X] (b : I → X)
    (hb : AddSubgroup.closure (Set.range b) = ⊤) (c : X → (𝟙_ (Over S') ⟶ G')) (hc : ∀ y z, c (y + z) = c y * c z)
    (x₀ : I → (𝟙_ (Over S) ⟶ G)) (hx : ∀ k, (c (b k)).left ≫ Φ = f ≫ (x₀ k).left) :
    ∃ c₀ : X → (𝟙_ (Over S) ⟶ G), (∀ y z, c₀ (y + z) = c₀ y * c₀ z) ∧ ∀ y, (c y).left ≫ Φ = f ≫ (c₀ y).left := by
  let ρ : Over.mk ((𝟙_ (Over S')).hom ≫ f) ⟶ 𝟙_ (Over S) :=
    Over.homMk f ((Category.comp_id f).trans (Category.id_comp f).symm)
  obtain ⟨c₀, h₁, h₂⟩ := exists_lift b hb (fun y => pushHom h (𝟙_ (Over S')) (c y))
    (fun y z => by rw [hc, map_mul]) (preHom (G := G) ρ)
    (fun u v huv => Over.OverMorphism.ext ((cancel_epi f).1 (congrArg (fun q => q.left) huv))) x₀
    (fun k => Over.OverMorphism.ext (hx k))
  exact ⟨c₀, h₁, fun y => congrArg (fun q => q.left) (h₂ y)⟩

theorem additive_points_descend : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (P₀ : PolAV (Sp K₀)) (P : PolAV (Sp K)) (Φ : P.A.left ⟶ P₀.A.left), IsGrpPullback P.A P₀.A (spMap i) Φ → ∀ (X : Type) [AddCommGroup X] (I : Type) (b : I → X), AddSubgroup.closure (Set.range b) = ⊤ → ∀ c : X → (𝟙_ (Over (Sp K)) ⟶ P.A), (∀ y z, c (y + z) = padd P.A (c y) (c z)) → ∀ x₀ : I → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ k, (c (b k)).left ≫ Φ = spMap i ≫ (x₀ k).left) → ∃ c₀ : X → (𝟙_ (Over (Sp K₀)) ⟶ P₀.A), (∀ y z, c₀ (y + z) = padd P₀.A (c₀ y) (c₀ z)) ∧ ∀ y, (c y).left ≫ Φ = spMap i ≫ (c₀ y).left := by
  intro K₀ K _ _ i P₀ P Φ h X _ I b hb c hc x₀ hx
  have := FieldBaseChange.flat_spMap i
  have := FieldBaseChange.surjective_spMap i
  have : Epi (spMap i) := Flat.epi_of_flat_of_surjective _
  exact exists_descent h b hb c hc x₀ hx

end GlobalTheory.PointDescent
