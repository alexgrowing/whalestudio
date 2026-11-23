import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

namespace GlobalTheory.Unf.FB

variable {D : D7} {σ : ℕ}

theorem mul_mul_mul_of_gram {a b c e n : Type*} [Fintype b] [Fintype c] [Fintype e] {R : Type*} [Semiring R]
    {A : Matrix a b R} {G : Matrix b c R} {M : Matrix c e R} {C : Matrix a e R} (h : A * G * M = C)
    (N : Matrix e n R) : A * (G * (M * N)) = C * N := by
  rw [← h]; simp only [Matrix.mul_assoc]

def selFirst (D : D7) (σ : ℕ) : Matrix (Fin σ) (Fin (σ + 1)) D.host.E :=
  Matrix.of fun i j => if j = i.castSucc then 1 else 0

def lastE (D : D7) (σ : ℕ) : Fin (σ + 1) → D.host.E := Pi.single (Fin.last σ) 1

def besselRationalBasePointMatrix (B : BesLev D σ) : Matrix (Fin B.V.rank) (Fin (σ + 1)) D.host.E :=
  B.d.e * selFirst D σ + B.d.i₀ * vecMulVec (vecB B.o B.ζ) (lastE D σ)

theorem ell_succ_eq : ell D (σ + 1) = fun i => incA D (lastE D σ i) := by
  funext i
  by_cases h : i = Fin.last σ
  · subst h
    show (if (Fin.last σ).1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ (Fin.last σ))
    rw [if_pos (by rw [Fin.val_last]), lastE, Pi.single_eq_same, map_one]
  · have h' : ¬ (i.1 + 1 = σ + 1) := fun h' => h (Fin.ext (by rw [Fin.val_last]; omega))
    show (if i.1 + 1 = σ + 1 then (1 : AE D) else 0) = incA D (lastE D σ i)
    rw [if_neg h', lastE, Pi.single_eq_of_ne h, map_zero]

theorem zl_eq_rat (B : BesLev D σ) : zl B = rat (vecMulVec B.ζ (lastE D σ)) := by
  funext i j
  simp [zl, zEll, rat, ratV, vecMulVec, ell_succ_eq]

theorem rat_x0Rat (B : BesLev D σ) : rat (besselRationalBasePointMatrix B) = x0 B := by
  have hne : ∀ x : Fin σ, (Fin.last σ = x.castSucc) ↔ False := fun x => iff_false_intro (Fin.castSucc_lt_last x).ne'
  funext k j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.j0, mulVec, dotProduct, ratV,
      vecB, hne]
  · simp [besselRationalBasePointMatrix, x0, xLast, rat, selFirst, lastE, Matrix.mul_apply, vecMulVec, HypDec.jX, mulVec, dotProduct, ratV,
      vecB]

theorem gram_x0Rat (B : BesLev D σ) :
    (besselRationalBasePointMatrix B)ᴴ * B.V.gram * besselRationalBasePointMatrix B =
      (vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ) := by
  have hXX := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.ee
  have h0X := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.i₀e
  have hX0 : B.d.eᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hX0' := mul_mul_mul_of_gram (n := Fin (σ + 1)) hX0
  have h00 := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.d.iso
  have hBB := mul_mul_mul_of_gram (n := Fin (σ + 1)) B.o.isoB
  have hz : vecMulVec (vecB B.o B.ζ) (lastE D σ) = B.o.iB * vecMulVec B.ζ (lastE D σ) := by
    rw [vecB, mul_vecMulVec]
  rw [besselRationalBasePointMatrix, hz]
  simp only [conjTranspose_add, conjTranspose_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc, hXX, h0X, hX0',
    h00, hBB, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]

theorem gramSkew_x0Rat (B : BesLev D σ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.V (rat (besselRationalBasePointMatrix B) : Mx D B.V.rank (σ + 1)) = GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew B.L (zl B) := by
  rw [zl_eq_rat, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew, gram_rat _ (gram_x0Rat B), gram_rat B.L rfl]

theorem linearIndependent_x0Rat (B : BesLev D σ) : LinearIndependent D.host.E (besselRationalBasePointMatrix B).transpose := by
  refine Fintype.linearIndependent_iff.2 ?_
  intro g hg
  have hv : besselRationalBasePointMatrix B *ᵥ g = 0 := by
    funext k
    have := congrFun hg k
    simpa [Finset.sum_apply, mulVec, dotProduct, mul_comm] using this
  have h0 : B.d.e'ᴴ * B.V.gram * B.d.i₀ = 0 := by
    have := congrArg conjTranspose B.d.i₀e'
    rwa [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, gram_conjTranspose, conjTranspose_zero,
      ← Matrix.mul_assoc] at this
  have hq : (B.d.e'ᴴ * B.V.gram) * besselRationalBasePointMatrix B = selFirst D σ := by
    rw [besselRationalBasePointMatrix, Matrix.mul_add, ← Matrix.mul_assoc, B.d.e'e, Matrix.one_mul, ← Matrix.mul_assoc, h0, Matrix.zero_mul,
      add_zero]
  have h1 : selFirst D σ *ᵥ g = 0 := by rw [← hq, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  have h2 : ((vecMulVec B.ζ (lastE D σ))ᴴ * B.L.gram * vecMulVec B.ζ (lastE D σ)) *ᵥ g = 0 := by
    rw [← gram_x0Rat B, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · have h3 := congrFun h2 (Fin.last σ)
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, vecMulVec_mulVec, conjTranspose_vecMulVec, vecMulVec_mulVec]
      at h3
    simp [lastE, mulVec_smul] at h3
    rcases h3 with h3 | h3
    · exact h3
    · exact absurd h3 B.line.2
  · have := congrFun h1 i
    simpa [selFirst, mulVec, dotProduct] using this

theorem exists_rationalOrbit_point_eq_besselBasePoint : ∀ (D : D7) (σ : ℕ) (B : BesLev D σ), ∃ x ∈ orb B, (rat x : Mx D B.V.rank (σ + 1)) = x0 B :=
  fun _ _ B => ⟨besselRationalBasePointMatrix B, ⟨linearIndependent_x0Rat B, gramSkew_x0Rat B⟩, rat_x0Rat B⟩

end GlobalTheory.Unf.FB

end
