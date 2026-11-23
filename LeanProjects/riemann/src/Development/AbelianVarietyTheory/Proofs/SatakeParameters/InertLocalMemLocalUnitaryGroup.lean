import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsCharacterEigenvectorOfCommutingRepresentat
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosetsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosetsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.UG

namespace GlobalTheory.InertLocUnitary

open TensorProduct

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : ReciprocityTheory.Aut.AL L) :
    ReciprocityTheory.Aut.compAt L v (ReciprocityTheory.Aut.conjAL L a) =
      Formalism.UG.sigR (IsCMField.complexConj L).toAlgHom (v.adicCompletion (maximalRealSubfield L))
        (ReciprocityTheory.Aut.compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp [ReciprocityTheory.Aut.compAt, ReciprocityTheory.Aut.conjAL, Formalism.UG.sigR, Algebra.TensorProduct.map_tmul]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem loc_mem_GU (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x ∈ GU Dv.σw n := by
  set ψ : ReciprocityTheory.Aut.AL L →+* w.adicCompletion L :=
    (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L).comp
      (ReciprocityTheory.Aut.compAt L v) with hψ
  have hcomm : ∀ a, Dv.σw (ψ a) = ψ (ReciprocityTheory.Aut.conjAL L a) := by
    intro a
    simp only [hψ, RingHom.comp_apply, RingHom.coe_coe]
    rw [compAt_conjAL, Dv.comm]
  set M : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L) := (x.1 : GL (Fin n) (ReciprocityTheory.Aut.AL L)).val with hM
  have hx : M * ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M = 1 := x.2
  set X : Matrix (Fin n) (Fin n) (w.adicCompletion L) := M.map ψ with hX
  have hXval : ((Formalism.UG.bc (n := Fin n) (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (ReciprocityTheory.Aut.compAt L v) (x : GL (Fin n) (ReciprocityTheory.Aut.AL L))) :
        GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = X := by
    ext i j; rfl
  have hcTX : Formalism.UG.cT Dv.σw X = (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL L) M).map ψ := by
    ext i j
    simp [Formalism.UG.cT, ReciprocityTheory.Aut.conjT, hX, hcomm]
  have hXX : X * Formalism.UG.cT Dv.σw X = 1 := by
    rw [hcTX, hX, ← Matrix.map_mul, hx, Matrix.map_one _ (map_zero ψ) (map_one ψ)]
  have hXX' : Formalism.UG.cT Dv.σw X * X = 1 := mul_eq_one_comm.mp hXX
  set P : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P : GL (Fin n) (w.adicCompletion L)).val with hP
  set Q : Matrix (Fin n) (Fin n) (w.adicCompletion L) := (Dv.P⁻¹ : GL (Fin n) (w.adicCompletion L)).val with hQ
  have hPQ : P * Q = 1 := by rw [hP, hQ, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hJ : Formalism.UG.cT Dv.σw P * P = Formalism.UG.antiJ (w.adicCompletion L) n := Dv.Panti
  show Formalism.UG.cT Dv.σw (((Dv.loc x : GL (Fin n) _)) : Matrix _ _ _) * Formalism.UG.antiJ (w.adicCompletion L) n *
      ((Dv.loc x : GL (Fin n) _) : Matrix _ _ _) = Formalism.UG.antiJ (w.adicCompletion L) n
  have hloc : ((Dv.loc x : GL (Fin n) _) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) = Q * X * P := by
    simp only [InertDatum.loc, Units.val_mul, hXval, hQ, hP]
  have cQP : Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P = 1 := by
    rw [← Formalism.UG.cT_mul, hPQ, Formalism.UG.cT_one]
  rw [hloc, ← hJ, Formalism.UG.cT_mul, Formalism.UG.cT_mul]
  calc _ = Formalism.UG.cT Dv.σw P * Formalism.UG.cT Dv.σw X * (Formalism.UG.cT Dv.σw Q * Formalism.UG.cT Dv.σw P) * (P * Q) * X * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT Dv.σw P * P := by
        rw [cQP, hPQ, Matrix.mul_one, Matrix.mul_one]
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc (Formalism.UG.cT Dv.σw X), hXX', Matrix.one_mul]

end GlobalTheory.InertLocUnitary

theorem GlobalTheory.InertLocUnitary.main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w), ∀ x : GAf L n, Dv.loc x ∈ GU Dv.σw n :=
  fun L _ _ _ n v w Dv x => GlobalTheory.InertLocUnitary.loc_mem_GU L n v w Dv x
