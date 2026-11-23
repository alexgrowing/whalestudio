import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem exists_comp_eq_of_ker_le {F : Type} [Field F] {U X Y : Type} [AddCommGroup U] [Module F U]
    [AddCommGroup X] [Module F X] [AddCommGroup Y] [Module F Y] (p : U →ₗ[F] X) (f : U →ₗ[F] Y)
    (h : LinearMap.ker p ≤ LinearMap.ker f) : ∃ k : X →ₗ[F] Y, ∀ u, k (p u) = f u := by
  obtain ⟨k, hk⟩ := LinearMap.exists_extend
    (((LinearMap.ker p).liftQ f h) ∘ₗ p.quotKerEquivRange.symm.toLinearMap)
  refine ⟨k, fun u => ?_⟩
  have := LinearMap.congr_fun hk ⟨p u, LinearMap.mem_range_self p u⟩
  simpa using this

theorem exists_nilRad_extend {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (A W : Submodule F V) (h' : Module.End F W) (hh : h' ∈ nilRad (A.comap W.subtype)) :
    ∃ L : Module.End F V, L ∈ nilRad A ∧ ∀ x : W, L x = h' x := by
  obtain ⟨k, hk⟩ := exists_comp_eq_of_ker_le (A.mkQ ∘ₗ W.subtype)
    (LinearMap.codRestrict A (W.subtype ∘ₗ h') (fun x => hh.1 x)) (by
      intro x hx
      have hx' : (x : V) ∈ A := by simpa using hx
      have := hh.2 x hx'
      rw [LinearMap.mem_ker]
      ext
      simp [this])
  refine ⟨A.subtype ∘ₗ k ∘ₗ A.mkQ, ⟨fun x => by simp, fun x hx => ?_⟩, fun x => ?_⟩
  · have : A.mkQ x = 0 := by simpa using hx
    simp only [LinearMap.comp_apply, this, map_zero]
  · have := congrArg Subtype.val (hk x)
    simpa using this

theorem sum_restrict_eq_zero_of_mixed (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (h1 : W ⊓ A ≠ ⊥) (h2 : ¬ W ≤ A) (φ : Module.End F W → ℂ) (hφ : IsPrimitive φ) :
    ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W},
      φ ((g + h.1).restrict h.2.2) = 0 := by
  classical
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (Module.End F W) := Finite.of_injective _ DFunLike.coe_injective
  set A' : Submodule F W := A.comap W.subtype with hA'
  have hb : A' ≠ ⊥ := by
    intro h
    apply h1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.1⟩ : W) ∈ A' := hx.2
    rw [h, Submodule.mem_bot] at this
    simpa using congrArg Subtype.val this
  have ht : A' ≠ ⊤ := by
    intro h
    apply h2
    intro x hx
    have : (⟨x, hx⟩ : W) ∈ A' := h ▸ Submodule.mem_top
    exact this
  let S := {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}
  haveI : Fintype S := Fintype.ofFinite _
  haveI : Fintype (nilRad A') := Fintype.ofFinite _
  have inner : ∀ h : S, ∑ h' : nilRad A', φ ((g + h.1).restrict h.2.2 + h'.1) = 0 := by
    intro h
    have := hφ A' hb ht ((g + h.1).restrict h.2.2) (by
      intro x hx
      have hx' : (x : V) ∈ A := hx
      change (g + h.1) x ∈ A
      rw [LinearMap.add_apply]
      exact A.add_mem (hg _ hx') (h.2.1.1 _))
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype] at this
    exact this
  have shift : ∀ h' : nilRad A', ∑ h : S, φ ((g + h.1).restrict h.2.2 + h'.1) =
      ∑ h : S, φ ((g + h.1).restrict h.2.2) := by
    intro h'
    obtain ⟨L, hL, hLW⟩ := exists_nilRad_extend A W h'.1 h'.2
    let T : S → S := fun h => ⟨h.1 + L, ⟨fun x => A.add_mem (h.2.1.1 x) (hL.1 x), fun x hx => by
      rw [LinearMap.add_apply, h.2.1.2 x hx, hL.2 x hx, add_zero]⟩, fun x hx => by
        rw [← add_assoc, LinearMap.add_apply, hLW ⟨x, hx⟩]
        exact W.add_mem (h.2.2 x hx) (h'.1 ⟨x, hx⟩).2⟩
    have hT : Function.Bijective T := by
      apply Finite.injective_iff_bijective.mp
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (add_right_cancel this)
    refine Fintype.sum_bijective T hT _ _ fun h => ?_
    congr 1
    ext x
    change (g + h.1) x + (h'.1 x : V) = (g + (h.1 + L)) x
    rw [← add_assoc, LinearMap.add_apply (g + h.1), hLW x]
  have tot : ∑ h' : nilRad A', ∑ h : S, φ ((g + h.1).restrict h.2.2 + h'.1) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun h _ => inner h
  simp only [shift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_eq_zero] at tot
  haveI : Nonempty (nilRad A') := ⟨⟨0, fun x => A'.zero_mem, fun x _ => rfl⟩⟩
  rw [finsum_eq_sum_of_fintype]
  rcases tot with h | h
  · exact absurd h (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  · exact h

end GlobalTheory.CuspGL
