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

theorem eq_zero_of_line_subset_discrete {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (v : Fin g → ℂ) (hv : ∀ t : ℂ, t • v ∈ Λ) : v = 0 := by
  by_contra h
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hinj : Function.Injective (fun t : ℂ => (⟨t • v, hv t⟩ : Λ)) := by
    intro s t hst
    exact smul_left_injective ℂ h (congrArg Subtype.val hst)
  have : Countable ℂ := hinj.countable
  have : Countable ℝ := Complex.ofReal_injective.countable
  exact not_countable this

theorem linear_eq_of_ex_eq {g : ℕ} {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} (u : HolUnif A L g)
    (F F' : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (h : ∀ z, u.ex (F z) = u.ex (F' z)) : F = F' := by
  have hd := u.discrete
  have hm : ∀ z, F z - F' z ∈ u.Λ := by
    intro z
    rw [← u.ker]
    have h1 := u.ex_add (F z - F' z) (F' z)
    rw [sub_add_cancel, h z] at h1
    exact (mul_eq_right.mp h1.symm)
  refine LinearMap.ext fun z => sub_eq_zero.mp (eq_zero_of_line_subset_discrete u.Λ _ fun t => ?_)
  have := hm (t • z)
  rwa [map_smul, map_smul, ← smul_sub] at this

theorem exists_linear_lift_action : ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → (∀ (f : P₀.A ⟶ P₀.A) (F F' : (Fin P₀.g → ℂ) →ₗ[ℂ] (Fin P₀.g → ℂ)), (∀ z, u.ex (F z) = u.ex z ≫ f) → (∀ z, u.ex (F' z) = u.ex z ≫ f) → F = F') ∧ ∀ (O : Type) [CommRing O] (act : OAct O P₀.A), ∃ F : O →+* Module.End ℂ (Fin P₀.g → ℂ), ∀ a z, u.ex (F a z) = u.ex z ≫ act.act a := by
  intro P₀ u Hm χ hu
  refine ⟨fun f F F' h h' => linear_eq_of_ex_eq u F F' fun z => (h z).trans (h' z).symm, ?_⟩
  intro O _ act
  choose F hF using fun a => hu.endo (act.act a) (act.hom a)
  have hone : F 1 = (1 : Module.End ℂ (Fin P₀.g → ℂ)) :=
    linear_eq_of_ex_eq u _ _ fun z => by rw [hF, act.one, Category.comp_id]; rfl
  have hmul : ∀ a b, F (a * b) = (F a : Module.End ℂ (Fin P₀.g → ℂ)) * F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, mul_comm a b, act.mul, Module.End.mul_apply, hF, hF, Category.assoc]
  have hadd : ∀ a b, F (a + b) = F a + F b := fun a b =>
    linear_eq_of_ex_eq u _ _ fun z => by
      rw [hF, act.add, LinearMap.add_apply, u.ex_add, hF, hF, MonObj.comp_mul]
  exact ⟨RingHom.mk' ⟨⟨F, hone⟩, hmul⟩ hadd, hF⟩

end GlobalTheory.KS
