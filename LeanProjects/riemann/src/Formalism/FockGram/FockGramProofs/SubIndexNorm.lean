import Formalism.FockGram.StatementLat

open Matrix Module

namespace Formalism.E

theorem indexEqNormDet : SubIndexNorm := by
  intro S M ι _ _ _ _ _ _ _ b N bN
  classical
  haveI : Module.Free S M := Module.Free.of_basis b
  haveI : Module.Finite S M := Module.Finite.of_basis b
  haveI : Module.Free ℤ M := Module.Free.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  haveI : Module.Finite ℤ M := Module.Finite.of_basis ((Module.Free.chooseBasis ℤ S).smulTower b)
  let e0 : M ≃ₗ[S] N := b.equiv bN (Equiv.refl ι)
  let f : M →ₗ[S] M := N.subtype ∘ₗ e0.toLinearMap
  have hS : b.det (fun i => (bN i : M)) = LinearMap.det f := by
    rw [Basis.det_apply, ← LinearMap.det_toMatrix b]
    congr 1
    ext x y
    rw [Basis.toMatrix_apply, LinearMap.toMatrix_apply]
    simp [f, e0]
  let N' : Submodule ℤ M := N.restrictScalars ℤ
  let e : M ≃ₗ[ℤ] N' := (e0.trans (Submodule.restrictScalarsEquiv ℤ S M N).symm).restrictScalars ℤ
  have h1 := Submodule.natAbs_det_equiv N' e
  have hcard : Nat.card (M ⧸ N') = Nat.card (M ⧸ N) :=
    Nat.card_congr (Submodule.Quotient.restrictScalarsEquiv ℤ N).toEquiv
  rw [← hcard, ← h1, hS, ← LinearMap.det_restrictScalars]
  congr 2

end Formalism.E
