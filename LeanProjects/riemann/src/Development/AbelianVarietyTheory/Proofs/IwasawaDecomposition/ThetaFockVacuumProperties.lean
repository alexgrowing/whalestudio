import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FibExtMarked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockPolynomialVectorsInjectiveNonzeroVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaVectorNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsFockVacAtOfIsThetaAt

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts

namespace GlobalTheory.OneMapRef.VecP

open scoped ComplexOrder in

theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨ε, hε, hB, -⟩ := h
  have hε1 : ∀ a, ε a = 1 := fun a =>
    ((hε a).resolve_right fun h' => absurd h'.2 (not_le.mpr a.2)).1
  have hB1 : Bᴴ * G * B = 1 := by simpa [hε1] using hB
  have hBC : B * (Bᴴ * G) = 1 := mul_eq_one_comm.mp hB1
  have hGB : G * B = (Bᴴ * G)ᴴ := by
    calc G * B = (B * (Bᴴ * G))ᴴ * (G * B) := by rw [hBC, conjTranspose_one, Matrix.one_mul]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G * B) := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ := by rw [hB1, Matrix.mul_one]
  have hG : G = (Bᴴ * G)ᴴ * (Bᴴ * G) := by
    calc G = G * (B * (Bᴴ * G)) := by rw [hBC, Matrix.mul_one]
      _ = G * B * (Bᴴ * G) := by rw [Matrix.mul_assoc]
      _ = (Bᴴ * G)ᴴ * (Bᴴ * G) := by rw [hGB]
  have hinj : Function.Injective (Bᴴ * G).mulVec := by
    intro v w hvw
    have h2 := congrArg (fun x => B *ᵥ x) hvw
    simpa only [Matrix.mulVec_mulVec, hBC, Matrix.one_mulVec] using h2
  unfold IsCartanInv
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _ hinj

end GlobalTheory.OneMapRef.VecP
