import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuadraticStarStructure
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR

theorem Et.norm_facts : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), ((∀ s : A.K, A.NL (algebraMap A.K A.L s) = s ^ 2) ∧ (∀ y y' : A.L, A.NL (y * y') = A.NL y * A.NL y') ∧ (∀ t : unitary A.L, A.NL (t : A.L) = 1) ∧ (∀ y : A.L, IsUnit (A.NL y) → IsUnit y) ∧ (∀ y : A.L, IsUnit y → IsUnit (A.NL y))) := by
  intro F E _ _ _ _ _ A
  obtain ⟨⟨b⟩, hinj, hN, -, -⟩ := Et.quadratic_structure F E A
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro s
    simp only [Et.NL]
    rw [Algebra.norm_algebraMap_of_basis b]
    simp
  · intro y y'
    simp only [Et.NL]
    exact map_mul (Algebra.norm A.K) y y'
  · intro t
    apply hinj
    rw [hN, map_one]
    exact t.prop.2
  · intro y hy
    have h := hy.map (algebraMap A.K A.L)
    rw [hN] at h
    exact isUnit_of_mul_isUnit_left h
  · intro y hy
    exact hy.map (Algebra.norm A.K)

end GlobalTheory.JR
