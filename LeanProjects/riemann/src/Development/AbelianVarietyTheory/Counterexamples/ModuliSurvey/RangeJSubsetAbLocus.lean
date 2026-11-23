import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible

noncomputable section

namespace GlobalTheory.ModelScope

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem extends_of_not_subset (Y : Model Xo c β) (U : Y.X.Opens) (hU : ¬ Set.range Y.j ⊆ (U : Set Y.X))
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) : Y.Extends U σ := by
  refine ⟨U.ι ≫ (show Y.X ⟶ Y.t.G.left from (η[Y.t.G]).left), ?_, fun j' hj => (hU ?_).elim⟩
  · have h : (show Y.X ⟶ Y.t.G.left from (η[Y.t.G]).left) ≫ Y.t.G.hom = 𝟙 _ := Over.w (η[Y.t.G])
    rw [Category.assoc, h, Category.comp_id]
  · rintro _ ⟨x, rfl⟩
    rw [← hj]
    exact (j' x).2

theorem range_j_subset_abLocus (Y : Model Xo c β) : Set.range Y.j ⊆ abLocus Y.t.G := by
  rintro _ ⟨x, rfl⟩
  have h : Y.jQ x ∈ pullback.fst Y.s (spMap β) ⁻¹' abLocus Y.t.G := by
    rw [Y.ab_gen]; exact ⟨x, rfl⟩
  exact h

theorem extends_iff_of_subset (Y : Model Xo c β) (U : Y.X.Opens) (hU : Set.range Y.j ⊆ (U : Set Y.X))
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) :
    Y.Extends U σ ↔ ∃ (j' : Xo.XF c ⟶ U.toScheme) (σ' : U.toScheme ⟶ Y.t.G.left),
      j' ≫ U.ι = Y.j ∧ σ' ≫ Y.t.G.hom = U.ι ∧ j' ≫ σ' = σ.left ≫ Y.m.φ := by
  have hU' : Set.range Y.j ⊆ Set.range U.ι := by rwa [Scheme.Opens.range_ι]
  constructor
  · rintro ⟨σ', h₁, h₂⟩
    exact ⟨IsOpenImmersion.lift U.ι Y.j hU', σ', IsOpenImmersion.lift_fac _ _ _, h₁,
      h₂ _ (IsOpenImmersion.lift_fac _ _ _)⟩
  · rintro ⟨j', σ', h₀, h₁, h₂⟩
    refine ⟨σ', h₁, fun j'' h => ?_⟩
    obtain rfl : j'' = j' := by rw [← cancel_mono U.ι, h, h₀]
    exact h₂

end GlobalTheory.ModelScope
