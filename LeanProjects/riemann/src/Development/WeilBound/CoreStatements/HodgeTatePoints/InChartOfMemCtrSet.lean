import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem mem_ctrSet_of {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} {x : κ → Ω}
    {X' : Scheme.{0}} {Ω' : Type} [Field Ω'] {ξ' : Spec (CommRingCat.of Ω') ⟶ X'} {i : Ω →+* Ω'} {p' : Cpt ξ'}
    (c : κ) (hc : x c ≠ 0) (ho : ∀ r : o, i (algebraMap o Ω r) ∈ regAt ξ' p')
    (hx : ∀ j, i (x j / x c) ∈ regAt ξ' p') : p' ∈ ctrSet o x i ξ' := by
  refine ⟨c, hc, fun a ha => ?_⟩
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    exact hx j
  | algebraMap r => exact ho r
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz

theorem join_charts : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ κ' : Type) (x : κ → Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (w : κ' → Ω') (M' : PModel o (joinCo i x w)), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → ∀ p' : Cpt M'.ξ, p' ∈ ctrSet o x i M'.ξ ∧ ∃ l, InChart M'.ξ w l p' := by
  intro o _ Ω _ _ κ κ' x Ω' _ _ i w M' hi p'
  obtain ⟨⟨c, l⟩, hc⟩ := M'.tie.cover p'
  have h0 : i (x c) * w l ≠ 0 := hc.1
  have h1 := left_ne_zero_of_mul h0
  have h2 := right_ne_zero_of_mul h0
  refine ⟨mem_ctrSet_of c ((map_ne_zero i).1 h1) (fun r => ?_) fun j => ?_, l, h2, fun j => ?_⟩
  · rw [hi]
    exact (M'.tie.ring (c, l) hc.1 _).1 (Subalgebra.algebraMap_mem _ r) p' hc
  · have := hc.2 (j, l)
    simp only [joinCo] at this
    rwa [mul_div_mul_right _ _ h2, ← map_div₀] at this
  · have := hc.2 (c, j)
    simp only [joinCo] at this
    rwa [mul_div_mul_left _ _ h1] at this

end PositivityTheory.HtPt.Mb
