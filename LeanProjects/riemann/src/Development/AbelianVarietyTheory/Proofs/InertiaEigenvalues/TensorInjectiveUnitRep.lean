import Mathlib
import Development.AbelianVarietyTheory.Statements.WeilDeligneCrystalline.ColmezLT
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormLtOneOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AwayOfInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.BKReal GlobalTheory.Prism Formalism.BasicNotions.Examples₂.LB GlobalTheory.MemLoc GlobalTheory.AinfK GlobalTheory.AcrisK GlobalTheory.DiscEval GroundTheory.LocalField.FormalGroup
open scoped Formalism.Per

namespace GlobalTheory.SepSection

section
variable {Q K₀ : Type} (K B : Type) [Field Q] [Field K₀] [Field K] [CommRing B] [Algebra Q K₀] [Algebra Q K]
    [Algebra K₀ K] [IsScalarTower Q K₀ K] [Algebra Q B] [Algebra K₀ B] [IsScalarTower Q K₀ B]

noncomputable def push : K₀ ⊗[Q] K₀ →ₐ[Q] K ⊗[Q] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom Q K₀ K) (IsScalarTower.toAlgHom Q K₀ B)

variable (Q K₀) in

noncomputable def toBal : K ⊗[Q] B →ₐ[Q] K ⊗[K₀] B :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (R := K₀) (S := Q) (A := K) (B := B))
    ((Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := B)).restrictScalars Q)
    (fun _ _ => Commute.all _ _)

variable {K B}

noncomputable def sec (ε : K ⊗[Q] B)
    (hε : ∀ c : K₀, ((1 : K) ⊗ₜ[Q] algebraMap K₀ B c) * ε = (algebraMap K₀ K c ⊗ₜ[Q] (1 : B)) * ε) :
    K ⊗[K₀] B →ₗ[K] K ⊗[Q] B :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun a =>
        { toFun := fun b => ε * (a ⊗ₜ[Q] b)
          map_add' := fun x y => by rw [TensorProduct.tmul_add, mul_add]
          map_smul' := fun c b => by
            have h1 : a ⊗ₜ[Q] (c • b) = ((1 : K) ⊗ₜ[Q] algebraMap K₀ B c) * (a ⊗ₜ[Q] b) := by
              rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
            have h2 : ∀ y : K ⊗[Q] B, c • y = (algebraMap K₀ K c ⊗ₜ[Q] (1 : B)) * y := fun y => by
              rw [Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply]
            rw [RingHom.id_apply, h2, h1, ← mul_assoc, ← mul_assoc, ← hε, mul_comm ε] }
      map_add' := fun x y => by
        ext b
        simp [TensorProduct.add_tmul, mul_add]
      map_smul' := fun k a => by
        ext b
        simp only [LinearMap.coe_mk, AddHom.coe_mk, RingHom.id_apply, LinearMap.smul_apply]
        rw [← TensorProduct.smul_tmul', mul_smul_comm] }

noncomputable def toFin : K ⊗[Q] B ≃ₗ[K] (Fin 1 → K) ⊗[Q] B :=
  TensorProduct.AlgebraTensorModule.congr (LinearEquiv.funUnique (Fin 1) K K).symm (LinearEquiv.refl Q B)

end

end GlobalTheory.SepSection
