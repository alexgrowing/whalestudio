import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL

namespace GlobalTheory.CuspGL

theorem psi_of_finrank_eq_zero {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s)
    (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V)
    (h : Module.finrank F V = 0) : psi s V g = 0 := by
  have hsub : Subsingleton V := Module.finrank_zero_iff.mp h
  have h1 : LinearMap.charpoly g = 1 := by
    apply (LinearMap.charpoly_monic g).natDegree_eq_zero.mp
    rw [LinearMap.charpoly_natDegree, h]
  have h0 : s 1 = 0 := by
    have := hs 1 1 monic_one monic_one
    rw [one_mul] at this
    linear_combination -this
  have : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} :=
    ⟨fun W => W.2.1 (Subsingleton.elim _ _)⟩
  rw [psi_eq, h1, h0, finsum_of_isEmpty, sub_zero]

theorem coe_aeval_restrict_apply {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    (g : Module.End F V) (W : Submodule F V) (hW : ∀ x ∈ W, g x ∈ W) (p : F[X]) (x : W) :
    ((aeval (g.restrict hW : Module.End F W) p x : W) : V) = aeval g p x := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp [Module.algebraMap_end_apply]
  | add p q hp hq => simp [hp, hq]
  | monomial n a ih =>
    rw [pow_succ, ← mul_assoc, map_mul, map_mul (aeval g), aeval_X, aeval_X,
      Module.End.mul_apply, Module.End.mul_apply, ih]
    rfl

theorem finrank_eq_zero_of_irreducible_charpoly {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (g : Module.End F V) (hg : Irreducible (LinearMap.charpoly g))
    (W : Submodule F V) (hne : W ≠ ⊤) (hW : ∀ x ∈ W, g x ∈ W) : Module.finrank F W = 0 := by
  by_contra h0
  have hnt : Nontrivial W := Module.nontrivial_of_finrank_pos (R := F) (Nat.pos_of_ne_zero h0)
  set f : Module.End F W := g.restrict hW with hf
  have hz : aeval f (LinearMap.charpoly g) = 0 := by
    ext x
    rw [hf, coe_aeval_restrict_apply, LinearMap.aeval_self_charpoly]
    simp
  have hd : minpoly F f ∣ LinearMap.charpoly g := minpoly.dvd F f hz
  have hnu : ¬ IsUnit (minpoly F f) := minpoly.not_isUnit F f
  have hd' : LinearMap.charpoly g ∣ minpoly F f := ((hg.dvd_iff.mp hd).resolve_left hnu).dvd
  have hd'' : LinearMap.charpoly g ∣ LinearMap.charpoly f := hd'.trans (LinearMap.minpoly_dvd_charpoly f)
  have hle := natDegree_le_of_dvd hd'' (LinearMap.charpoly_monic f).ne_zero
  rw [LinearMap.charpoly_natDegree, LinearMap.charpoly_natDegree] at hle
  have := Submodule.finrank_lt hne
  omega

theorem psi_of_irreducible_charpoly : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → ∀ g : Module.End F V, Irreducible (LinearMap.charpoly g) → psi s V g = s (LinearMap.charpoly g) := by
  intro F _ _ V _ _ _ s hs g hg
  rw [psi_eq, finsum_eq_zero_of_forall_eq_zero, sub_zero]
  intro W
  exact psi_of_finrank_eq_zero s hs _ _ (finrank_eq_zero_of_irreducible_charpoly g hg W.1 W.2.1 W.2.2)

end GlobalTheory.CuspGL
