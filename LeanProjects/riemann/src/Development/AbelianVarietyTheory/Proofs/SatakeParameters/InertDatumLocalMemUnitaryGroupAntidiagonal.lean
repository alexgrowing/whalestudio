import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteOfTrivOutside
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem unitary_conj_by_inverse_pair_preserves_form {K : Type} [CommRing K] (σ : K →+* K) {n : ℕ}
    (P Q M J : Matrix (Fin n) (Fin n) K) (hPQ : P * Q = 1) (hM2 : Formalism.UG.cT σ M * M = 1)
    (hJ : Formalism.UG.cT σ P * P = J) : Formalism.UG.cT σ (Q * M * P) * J * (Q * M * P) = J := by
  have hQP : Formalism.UG.cT σ Q * Formalism.UG.cT σ P = 1 := by rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  subst hJ
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT σ P * Formalism.UG.cT σ M * (Formalism.UG.cT σ Q * Formalism.UG.cT σ P) * (P * Q) * M * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * P := by
        rw [hQP, hPQ, Matrix.mul_one, Matrix.mul_one, Matrix.mul_assoc (Formalism.UG.cT σ P), hM2, Matrix.mul_one]

open Formalism.UG in
theorem inertLoc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by

  have hcomm : ∀ a : AL L, compAt L v (conjAL L a) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
        (compAt L v a) := by
    intro a
    induction a using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [compAt, conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
    | add a b ha hb => simp only [map_add, ha, hb]
  set f : AL L →+* w.adicCompletion L := (Dv.e : _ →+* w.adicCompletion L).comp (compAt L v) with hf
  have hfc : ∀ a, f (conjAL L a) = Dv.σw (f a) := by
    intro a; simp only [hf, RingHom.comp_apply, hcomm]; exact Dv.comm _
  set A : Matrix (Fin n) (Fin n) (AL L) := ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) with hA
  have hx : A * conjT (conjAL L) A = 1 := x.2
  set M : Matrix (Fin n) (Fin n) (w.adicCompletion L) := A.map f with hM
  have hMc : (conjT (conjAL L) A).map f = cT Dv.σw M := by
    ext i j; simp [conjT, cT, hM, hfc]
  have hM1 : M * cT Dv.σw M = 1 := by
    rw [← hMc, hM, ← Matrix.map_mul, hx, Matrix.map_one f (map_zero f) (map_one f)]
  have hM2 : cT Dv.σw M * M = 1 := mul_eq_one_comm.mp hM1
  have hloc : ((Dv.loc x : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) =
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) * M *
        (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) := by
    simp only [Formalism.AUTREP.InertDatum.loc, Units.val_mul, hM, hA, hf]
    congr 2
  have hPQ : (Dv.P : Matrix (Fin n) (Fin n) (w.adicCompletion L)) *
      ((Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key := unitary_conj_by_inverse_pair_preserves_form Dv.σw _ _ M _ hPQ hM2 Dv.Panti
  rw [← hloc] at key
  exact key

end GlobalTheory
