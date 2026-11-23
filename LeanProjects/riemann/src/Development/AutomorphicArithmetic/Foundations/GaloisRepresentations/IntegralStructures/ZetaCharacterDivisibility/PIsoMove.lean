import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

theorem UpperTheory.Gal.Int.Div.isoMove_of :
    IsoMove := by
  intro Γ k _ _ a d r r' ρ ⟨u, hu⟩
  set U : Matrix (Fin a) (Fin a) k := (u : Matrix (Fin a) (Fin a) k) with hUdef
  set V : Matrix (Fin a) (Fin a) k := ((u⁻¹ : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) with hVdef
  have hVU : V * U = 1 := by
    simp only [hUdef, hVdef]
    exact Units.inv_mul u
  have hUV : U * V = 1 := by
    simp only [hUdef, hVdef]
    exact Units.mul_inv u
  have hr' : ∀ x, (r' x : Matrix (Fin a) (Fin a) k) = U * (r x : Matrix (Fin a) (Fin a) k) * V := by
    intro x
    rw [hu x]
    rfl
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).1 ⟨u⁻¹, rfl⟩
  constructor
  · rintro ⟨A, hA, h⟩
    refine ⟨A * V, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_left_of_isUnit_det V A hVdet, hA]
    · rw [hr' g, ← Matrix.mul_assoc, h g]
      calc A * (r g : Matrix (Fin a) (Fin a) k) * V
          = A * (1 * (r g : Matrix (Fin a) (Fin a) k)) * V := by rw [Matrix.one_mul]
        _ = A * V * (U * (r g : Matrix (Fin a) (Fin a) k) * V) := by
            rw [← hVU]; simp only [Matrix.mul_assoc]
  · rintro ⟨m, B, hB, h⟩
    have hk : ∀ X Y : Matrix (Fin a) (Fin a) k,
        Matrix.kronecker (X * Y) (1 : Matrix (Fin m) (Fin m) k)
          = Matrix.kronecker X (1 : Matrix (Fin m) (Fin m) k) * Matrix.kronecker Y (1 : Matrix (Fin m) (Fin m) k) := by
      intro X Y
      have := Matrix.mul_kronecker_mul X Y (1 : Matrix (Fin m) (Fin m) k) (1 : Matrix (Fin m) (Fin m) k)
      simpa using this
    have h1 : Matrix.kronecker (1 : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) = 1 :=
      Matrix.one_kronecker_one
    set P := Matrix.kronecker U (1 : Matrix (Fin m) (Fin m) k) with hP
    set Q := Matrix.kronecker V (1 : Matrix (Fin m) (Fin m) k) with hQ
    have hQP : Q * P = 1 := by rw [hQ, hP, ← hk, hVU, h1]
    have hPQ : P * Q = 1 := by rw [hQ, hP, ← hk, hUV, h1]
    have hPdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩
    refine ⟨m, P * B, ?_, fun g => ?_⟩
    · rw [Matrix.rank_mul_eq_right_of_isUnit_det P B hPdet, hB]
    · have hc : Matrix.kronecker (U * (r g : Matrix (Fin a) (Fin a) k) * V) (1 : Matrix (Fin m) (Fin m) k)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q := by
        rw [hk, hk]
      rw [hr' g, hc]
      calc P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * Q * (P * B)
          = P * Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * ((Q * P) * B) := by
            simp only [Matrix.mul_assoc]
        _ = P * (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k) * B) := by
            rw [hQP, Matrix.one_mul, Matrix.mul_assoc]
        _ = P * B * (ρ g : Matrix (Fin d) (Fin d) k) := by
            rw [h g, Matrix.mul_assoc]
