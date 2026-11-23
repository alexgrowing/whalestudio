import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

def FSCoord.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (P : MvPolynomial (Fin (N + 1)) A)
    (hP : P ∈ ProjSpace.grading A N n) (x : (self A N).complexPoints ρ) (j : Fin (N + 1))
    (hj : x.1.rep j ≠ 0),
      fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj)
          (isBasisOn_frame (A := A) j n) ((self A N).evalGlobalSection (twistN A N n) x (polySection hP)) *
        x.1.rep j ^ n = evalAt ρ x.1.rep P

def FSIndex.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ)
    (j : Fin (N + 1)) (hj : x.1.rep j ≠ 0) (s : (self A N).Fibre (twistN A N n) x),
      fsFibreNorm n ρ x s =
        ‖fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj)
            (isBasisOn_frame (A := A) j n) s‖ * ‖x.1.rep j‖ ^ n / norm2 x.1.rep ^ n

lemma pointQ_rep_ne_zero : pointQ.1.rep 0 ≠ 0 := by
  obtain ⟨a, ha⟩ := Projectivization.exists_smul_eq_mk_rep ℂ (Pi.single (0 : Fin 2) (1 : ℂ) : Fin 2 → ℂ)
    (by simp [funext_iff, Pi.single_apply])
  change (basePoint 1).rep 0 ≠ 0
  rw [basePoint, ← ha]
  simp [Units.smul_def]

example : (self (𝓞 ℚ) 1).H0 (twistN (𝓞 ℚ) 1 1) := polySection (ProjSpace.X_mem (A := 𝓞 ℚ) 0)

example : ℂ :=
  fibreEquivComplex ((self (𝓞 ℚ) 1).evalAtPoint pointQ) (point_mem_stdOpen pointQ pointQ_rep_ne_zero)
    (isBasisOn_frame (A := 𝓞 ℚ) 0 1)
    ((self (𝓞 ℚ) 1).evalGlobalSection (twistN (𝓞 ℚ) 1 1) pointQ (polySection (ProjSpace.X_mem (A := 𝓞 ℚ) 0)))

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
