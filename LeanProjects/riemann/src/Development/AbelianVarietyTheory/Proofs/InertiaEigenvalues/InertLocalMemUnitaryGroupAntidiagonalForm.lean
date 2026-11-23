import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteInertHeckeSupportCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertSatakeParametersEqOfIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemMaxCompactOfTrivOutsideLocalIntegral
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDoubleCosetsDefiniteUnitaryMaximalLevelStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocalUnitary

theorem compAt_conjAL (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (a : AL L) :
    compAt L v (conjAL L a) = Formalism.UG.sigR (↑(IsCMField.complexConj L))
      (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) v) (compAt L v a) := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [compAt, conjAL, Formalism.UG.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem cT_mul {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m]
    (M N : Matrix m m A) : Formalism.UG.cT σ (M * N) = Formalism.UG.cT σ N * Formalism.UG.cT σ M := by
  unfold Formalism.UG.cT
  rw [Matrix.map_mul, Matrix.transpose_mul]

theorem cT_one {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m] :
    Formalism.UG.cT σ (1 : Matrix m m A) = 1 := by
  unfold Formalism.UG.cT
  simp

theorem cT_conj_form {A : Type} [CommRing A] (σ : A →+* A) {m : Type} [Fintype m] [DecidableEq m]
    (Pm Pi X : Matrix m m A) (h1 : Pm * Pi = 1) (hX : Formalism.UG.cT σ X * X = 1) :
    Formalism.UG.cT σ (Pi * X * Pm) * (Formalism.UG.cT σ Pm * Pm) * (Pi * X * Pm) = Formalism.UG.cT σ Pm * Pm := by
  have h2 : Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm = 1 := by
    rw [← cT_mul, h1, cT_one]
  rw [cT_mul, cT_mul]
  calc _ = Formalism.UG.cT σ Pm * (Formalism.UG.cT σ X * ((Formalism.UG.cT σ Pi * Formalism.UG.cT σ Pm) * ((Pm * Pi) * X))) * Pm := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ Pm * Pm := by
        rw [h1, h2, Matrix.one_mul, Matrix.one_mul, hX, Matrix.mul_one]

theorem mem_UJ_iff {A : Type} [CommRing A] {m : Type} [Fintype m] [DecidableEq m] (σ : A →+* A)
    (J : Matrix m m A) (g : GL m A) : g ∈ Formalism.UG.UJ σ J ↔ Formalism.UG.cT σ (g : Matrix m m A) * J * g = J := Iff.rfl

theorem loc_mem_GU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n), Dv.loc x ∈ Formalism.UG.GU Dv.σw n := by
  intro L _ _ _ n v w Dv x
  let φ : AL L →+* HeightOneSpectrum.adicCompletion L w :=
    (Dv.e : _ →+* HeightOneSpectrum.adicCompletion L w).comp (compAt L v)
  have hφ : ∀ a : AL L, φ (conjAL L a) = Dv.σw (φ a) := by
    intro a
    simp only [φ, RingHom.comp_apply, RingHom.coe_coe, compAt_conjAL, Dv.comm]
  have hx : ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ReciprocityTheory.Aut.conjT (conjAL L) (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := x.2
  have hconj : φ.mapMatrix (ReciprocityTheory.Aut.conjT (conjAL L)
      ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) =
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, ReciprocityTheory.Aut.conjT, Formalism.UG.cT,
      Matrix.transpose_apply, hφ]
  have hX : φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      Formalism.UG.cT Dv.σw (φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L))) = 1 := by
    rw [← hconj, ← map_mul, hx, map_one]
  have hX' := mul_eq_one_comm.mp hX
  have hloc : ((Dv.loc x : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
      Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) =
      ((Dv.P⁻¹ : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) *
      φ.mapMatrix ((x.1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((Dv.P : GL (Fin n) (HeightOneSpectrum.adicCompletion L w)) :
        Matrix (Fin n) (Fin n) (HeightOneSpectrum.adicCompletion L w)) := by
    rw [Formalism.AUTREP.InertDatum.loc, Units.val_mul, Units.val_mul]
    congr 2
  rw [mem_UJ_iff, hloc, ← Dv.Panti]
  exact cT_conj_form Dv.σw _ _ _ (by simp) hX'

end GlobalTheory.LocalUnitary
