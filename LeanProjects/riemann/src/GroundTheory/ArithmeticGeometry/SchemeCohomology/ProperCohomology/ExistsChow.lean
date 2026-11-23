import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowMulti
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ChowSegre
set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

noncomputable section

theorem exists_chow' {A : Type u} [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] [IrreducibleSpace X] :
    ∃ (N : ℕ) (X' : Scheme.{u}) (i : X' ⟶ projectiveSpace A N) (π : X' ⟶ X) (U : X.Opens),
      IsClosedImmersion i ∧ i ≫ ProjSpace.toSpecBase A N = π ≫ (X ↘ Spec (.of A)) ∧
      genericPoint X ∈ U ∧ IsIso (π ∣_ U) := by
  obtain ⟨k, n, X', q, π, U, hq, hqπ, hU, hπ⟩ := exists_chow_multiProj (A := A) X
  refine ⟨ProjSpace.multiProjDim k n, X', q ≫ ProjSpace.multiProjEmb A k n, π, U,
    inferInstance, ?_, hU, hπ⟩
  rw [Category.assoc, ProjSpace.multiProjEmb_toSpecBase, hqπ]

theorem exists_chow {A : Type u} [CommRing A] [IsNoetherianRing A] (X : Scheme.{u})
    [X.Over (Spec (.of A))] [IsProper (X ↘ Spec (.of A))] [IrreducibleSpace X] :
    ∃ (N : ℕ) (X' : Scheme.{u}) (i : X' ⟶ projectiveSpace A N) (π : X' ⟶ X) (U : X.Opens),
      IsClosedImmersion i ∧ i ≫ ProjSpace.toSpecBase A N = π ≫ (X ↘ Spec (.of A)) ∧
      (U : Set X).Nonempty ∧ IsIso (π ∣_ U) := by
  obtain ⟨N, X', i, π, U, hi, hiπ, hU, hπ⟩ := exists_chow' (A := A) X
  exact ⟨N, X', i, π, U, hi, hiπ, ⟨_, hU⟩, hπ⟩

end

end GroundTheory.Arith.SchemeCoh
