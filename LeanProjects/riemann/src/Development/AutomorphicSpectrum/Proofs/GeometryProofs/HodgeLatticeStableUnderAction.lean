import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem hodgeAt_stable : ∀ (E : Type) [Field E] [NumberField E] (Ω Vs : Type) [Field Ω] [AddCommGroup Vs] [Module Ω Vs]
    (ρ : 𝓞 E →+* Module.End Ω Vs) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (R : Subring Ω) (g N : ℕ) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs)
    (HL : Submodule R (Vs × Module.Dual Ω Vs)),
    (∀ a y, (ρH a y).1 = ρ a y.1) → HodgeAt ρH HL ℓ t →
    (∀ i, t i ∈ HL) ∧ (∀ a, ∀ h ∈ HL, ρH a h ∈ HL) ∧ ∀ a i, ρ a (ℓ i) ∈ Submodule.span R (Set.range ℓ) := by
  intro E _ _ Ω Vs _ _ _ ρ ρH R g N ℓ t HL h1 h
  obtain ⟨⟨-, -, hX⟩, hmap, -⟩ := h
  have key : ∀ (c : 𝓞 E) (i : Fin N), ρH c (t i) ∈ HL := by
    intro c i
    rw [hX, ← (RingOfIntegers.basis E).sum_repr c, map_sum, LinearMap.sum_apply]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_zsmul, LinearMap.smul_apply]
    exact zsmul_mem (Submodule.subset_span (Set.mem_range.2 ⟨(i, k), rfl⟩)) _
  have stable : ∀ a, ∀ y ∈ HL, ρH a y ∈ HL := by
    intro a y hy
    rw [hX] at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨q, rfl⟩ := hx
      rw [← Module.End.mul_apply, ← map_mul]
      exact key _ _
    | zero => simp
    | add x y _ _ hx hy =>
      rw [map_add]
      exact add_mem hx hy
    | smul r x _ hx =>
      have e : ρH a (r • x) = r • ρH a x := map_smul (ρH a) (r : Ω) x
      rw [e]
      exact HL.smul_mem r hx
  refine ⟨fun i => ?_, stable, fun a i => ?_⟩
  · simpa using key 1 i
  · have hi : ℓ i ∈ HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) :=
      hmap ▸ Submodule.subset_span ⟨i, rfl⟩
    obtain ⟨y, hy, e⟩ := hi
    rw [← hmap]
    refine ⟨ρH a y, stable a y hy, ?_⟩
    have e' : y.1 = ℓ i := e
    change (ρH a y).1 = _
    rw [h1, e']

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
