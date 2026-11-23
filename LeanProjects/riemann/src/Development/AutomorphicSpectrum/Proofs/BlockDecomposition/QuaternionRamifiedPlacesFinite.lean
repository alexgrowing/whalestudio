import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import GroundTheory.AutomorphicForms.HermitianNormLocal

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem exists_isotropic_of_sq_sub_mul_sq {F K : Type} [Field F] [Field K] [Algebra F K] {d β : F} {x y : K}
    (h : x ^ 2 - algebraMap F K d * y ^ 2 = algebraMap F K β) :
    ∃ q : Q d β K, qn q = 0 ∧ q ≠ 0 := by
  refine ⟨⟨x, y, 1, 0⟩, ?_, fun hq => ?_⟩
  · simp only [qn]
    rw [← h]
    ring
  · exact one_ne_zero (congrArg QuaternionAlgebra.imJ hq : (1 : K) = 0)

theorem finite_anisotropic_places {F : Type} [Field F] [NumberField F] (d β : F)
    (hd : ∀ r : F, r ^ 2 ≠ d) (hβ : β ≠ 0) :
    {u : Pl F | ∀ x : Q d β (Kp u), qn x = 0 → x = 0}.Finite := by
  have hB := GroundTheory.Automorphic.eventually_exists_sq_sub_mul_sq hd hβ
  rw [Filter.eventually_cofinite] at hB
  refine ((Set.finite_univ (α := InfinitePlace F)).image Sum.inl |>.union (hB.image Sum.inr)).subset ?_
  rintro (w | v) hu
  · exact Or.inl ⟨w, Set.mem_univ _, rfl⟩
  · refine Or.inr ⟨v, ?_, rfl⟩
    rintro ⟨x, y, hxy⟩
    obtain ⟨q, hq0, hq⟩ := exists_isotropic_of_sq_sub_mul_sq (F := F) (K := Kp (Sum.inr v : Pl F))
      (d := d) (β := β) (x := x) (y := y) hxy
    exact hq (hu q hq0)

end GlobalTheory.CompanionTheory.PlaneSA
