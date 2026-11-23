import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSymm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem exists_ringHom_lift_of_formallySmooth (R B E C : Type) [CommRing R] [CommRing B]
    [CommRing E] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B]
    (φ : B →+* C) (ψ : R →+* E) (π : E →+* C) (hπ : Function.Surjective π)
    (hn : IsNilpotent (RingHom.ker π)) (hc : ∀ r, π (ψ r) = φ (algebraMap R B r)) :
    ∃ l : B →+* E, (∀ b, π (l b) = φ b) ∧ ∀ r, l (algebraMap R B r) = ψ r := by
  letI : Algebra R E := ψ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  let f : B →ₐ[R] C := { φ with commutes' := fun _ => rfl }
  let g : E →ₐ[R] C := { π with commutes' := fun r => hc r }
  refine ⟨(Algebra.FormallySmooth.liftOfSurjective f g hπ hn).toRingHom, fun b => ?_, fun r => ?_⟩
  · exact Algebra.FormallySmooth.liftOfSurjective_apply f g hπ hn b
  · exact (Algebra.FormallySmooth.liftOfSurjective f g hπ hn).commutes r

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct ContDiff in

theorem _root_.GlobalTheory.KS.exists_derivation_extend_of_formallySmooth :
    ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B] (φ : B →+* C) (D : R → C), (∀ a b, D (a + b) = D a + D b) → (∀ a b, D (a * b) = φ (algebraMap R B a) * D b + φ (algebraMap R B b) * D a) → ∃ d : B → C, (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = φ a * d b + φ b * d a) ∧ ∀ r, d (algebraMap R B r) = D r := by
  intro R B C _ _ _ _ _ φ D hadd hmul
  have h0 : D 0 = 0 := by
    have := hadd 0 0
    simpa using this
  have h1 : D 1 = 0 := by
    have h11 := hmul 1 1
    have e : (1 : R) * 1 = 1 := mul_one 1
    rw [e, map_one, map_one, _root_.one_mul] at h11
    linear_combination -h11
  let ψ : R →+* TrivSqZeroExt C C :=
    { toFun := fun r => TrivSqZeroExt.inl (φ (algebraMap R B r)) + TrivSqZeroExt.inr (D r)
      map_one' := by ext <;> simp [h1]
      map_mul' := fun a b => by ext <;> simp [hmul] <;> ring
      map_zero' := by ext <;> simp [h0]
      map_add' := fun a b => by ext <;> simp [hadd] }
  letI : Algebra R (TrivSqZeroExt C C) := ψ.toAlgebra
  letI : Algebra R C := (φ.comp (algebraMap R B)).toAlgebra
  let g : TrivSqZeroExt C C →ₐ[R] C :=
    { (TrivSqZeroExt.fstHom C C C).toRingHom with
      commutes' := fun r => by
        show (ψ r).fst = φ (algebraMap R B r)
        simp [ψ] }
  let f : B →ₐ[R] C :=
    { φ with
      commutes' := fun r => rfl }
  have hg : Function.Surjective g := fun c => ⟨TrivSqZeroExt.inl c, by simp [g]⟩
  have hker : IsNilpotent (RingHom.ker g) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Submodule.zero_eq_bot, eq_bot_iff]
    refine Ideal.mul_le.mpr fun x hx y hy => ?_
    rw [RingHom.mem_ker] at hx hy
    change x.fst = 0 at hx
    change y.fst = 0 at hy
    rw [Ideal.mem_bot]
    ext <;> simp [hx, hy]
  let L := Algebra.FormallySmooth.liftOfSurjective f g hg hker
  refine ⟨fun b => (L b).snd, fun a b => ?_, fun a b => ?_, fun r => ?_⟩
  · simp
  · have hfa : (L a).fst = φ a := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker a
    have hfb : (L b).fst = φ b := Algebra.FormallySmooth.liftOfSurjective_apply f g hg hker b
    simp [hfa, hfb]
    ring
  · show (L (algebraMap R B r)).snd = D r
    rw [L.commutes r]
    show (ψ r).snd = D r
    simp [ψ]

end GlobalTheory.KS
