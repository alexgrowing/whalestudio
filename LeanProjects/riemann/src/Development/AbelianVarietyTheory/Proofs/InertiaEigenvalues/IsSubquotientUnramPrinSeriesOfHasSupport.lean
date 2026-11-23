import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotCrysAtOfMono0
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv

noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix
open scoped TensorProduct

namespace GlobalTheory.PermPrin

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def permGL {n : ℕ} (σ : Equiv.Perm (Fin n)) : GL (Fin n) k :=
  ⟨σ.toPEquiv.toMatrix, σ.symm.toPEquiv.toMatrix, by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm], by
    rw [PEquiv.toMatrix_toPEquiv_mul]; ext i j; simp [PEquiv.toMatrix_apply, Matrix.one_apply, eq_comm]⟩

theorem permGL_conj_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) k) (i j : Fin n) :
    ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      (g : Matrix (Fin n) (Fin n) k) (σ i) (σ j) := by
  have : ((permGL σ * g * (permGL σ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      σ.toPEquiv.toMatrix * (g : Matrix (Fin n) (Fin n) k) * σ.symm.toPEquiv.toMatrix := rfl
  rw [this, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
  simp

theorem constEquiv_piTensor_detRep {n : ℕ} (χ : Fin n → kˣ →* ℂˣ) (L : ∀ _ : Fin n, GL (Fin 1) k)
    (t : ⨂[ℂ] _ : Fin n, ℂ) :
    PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ (piTensor (fun a => detRep (Fin 1) (χ a)) L t) =
      (∏ a, (χ a (GeneralLinearGroup.det (L a)) : ℂ)) * PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ t := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod r x =>
    simp only [map_smul, piTensor_tprod, PiTensorProduct.constantBaseRingEquiv_tprod, detRep, ofChar_apply,
      detChar_apply, Finset.prod_mul_distrib, smul_eq_mul]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

theorem isSubquotient_multiProd_prinSeries {n : ℕ} (e : (Σ _ : Fin n, Fin 1) ≃ Fin n)
    (χ : Fin n → kˣ →* ℂˣ) :
    IsSubquotient (multiProd e fun a => detRep (Fin 1) (χ a)) (prinSeries χ) := by
  let f : Fin n ≃ Fin n := (Equiv.sigmaUnique (Fin n) fun _ => Fin 1).symm.trans e
  let σ : Equiv.Perm (Fin n) := f.symm
  let P : GL (Fin n) k := permGL σ
  have hf : ∀ a (i : Fin 1), e ⟨a, i⟩ = f a := fun a i => by
    rw [Subsingleton.elim i 0]; rfl
  have hq : ∀ p : parab k (points (Fin n)), P * (p : GL (Fin n) k) * P⁻¹ ∈ parab k e := fun p => by
    refine mem_parab_iff.2 fun a b i j hab => ?_
    rw [hf, hf, permGL_conj_apply]
    simpa [σ] using mem_parab_iff.1 p.2 a b () () hab
  let κ := (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ).toLinearEquiv
  let Ψ : IndSp e (piTensor fun a => detRep (Fin 1) (χ a)) →ₗ[ℂ]
      IndSp (points (Fin n)) ((ofChar (torusChar χ)).comp (leviTorus k (Fin n)).symm.toMonoidHom) :=
    { toFun := fun F => ⟨⟨fun g => κ (F.1.1 (P * g)), fun p g => by
          let q : parab k e := ⟨P * p * P⁻¹, hq p⟩
          have e1 : P * ((p : GL (Fin n) k) * g) = (q : GL (Fin n) k) * (P * g) := by
            simp only [q, mul_assoc, inv_mul_cancel_left]
          have hdet : ∀ a, GeneralLinearGroup.det (leviProj k e q a) =
              GeneralLinearGroup.det (leviProj k (points (Fin n)) p a) := fun a => by
            ext
            simp only [GeneralLinearGroup.val_det_apply, det_unique]
            rw [leviProj_apply, leviProj_apply, hf]
            show ((P * p * P⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) (f a) (f a) = _
            rw [permGL_conj_apply]
            simp [σ]
          have hd : deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) =
              deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) := by
            rw [deltaHalf_apply, deltaHalf_apply]
            refine Finset.prod_congr rfl fun a _ => ?_
            rw [hdet, modExp_fin _ (fun _ => by simp), modExp_fin _ (fun _ => by simp)]
          beta_reduce
          rw [e1, parInd_law]
          generalize F.1.1 (P * g) = t
          show κ ((deltaHalf k (fun _ : Fin n => Fin 1) (leviProj k e q) : ℂ) •
              piTensor (fun a => detRep (Fin 1) (χ a)) (leviProj k e q) t) =
            (deltaHalf k (fun _ : Fin n => Unit) (leviProj k (points (Fin n)) p) : ℂ) •
              ofChar (torusChar χ) ((leviTorus k (Fin n)).symm (leviProj k (points (Fin n)) p)) (κ t)
          rw [map_smul, hd, ofChar_apply, torusChar_apply]
          congr 1
          refine (constEquiv_piTensor_detRep χ _ t).trans ?_
          rw [Units.coe_prod]
          congr 1
          exact Finset.prod_congr rfl fun a _ => by rw [hdet]; rfl⟩,
        MultiIrr.mem_smooth_of_eventually _ ((MultiIrr.eventually_of_smooth F).mono fun u hu x => by
          show κ (F.1.1 (P * (x * u))) = κ (F.1.1 (P * x))
          rw [← mul_assoc, hu])⟩
      map_add' := fun F G => Subtype.ext (Subtype.ext (funext fun x => map_add κ _ _))
      map_smul' := fun c F => Subtype.ext (Subtype.ext (funext fun x => map_smul κ _ _)) }
  refine .of_injective ⟨Ψ, fun g => LinearMap.ext fun F => Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    fun F F' h => ?_
  · show κ (F.1.1 (P * x * g)) = κ (F.1.1 (P * (x * g)))
    rw [mul_assoc]
  · refine Subtype.ext (Subtype.ext (funext fun x => κ.injective ?_))
    have h1 : κ (F.1.1 (P * (P⁻¹ * x))) = κ (F'.1.1 (P * (P⁻¹ * x))) :=
      congrFun (congrArg (fun φ => φ.1.1) h) (P⁻¹ * x)
    simpa only [← mul_assoc, mul_inv_cancel, one_mul] using h1

end GlobalTheory.PermPrin

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory
