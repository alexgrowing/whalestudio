import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplTupBijective
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMinorsMemInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasInfExpDiv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped TensorProduct

open scoped ComplexOrder

namespace GlobalTheory.DefiniteFrame

theorem cT_conj_eq {m p : Type} (M : Matrix m p ℂ) :
    Formalism.UG.cT (starRingEnd ℂ) M = M.conjTranspose := by
  ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]

theorem Jpq_zero (n : ℕ) : Formalism.UG.Jpq n 0 = 1 := by
  ext i j
  rcases i with i | i
  · rcases j with j | j
    · simp [Formalism.UG.Jpq, Matrix.one_apply]
    · exact j.elim0
  · exact i.elim0

theorem posSemidef_of_hasSignature {n : ℕ} {G : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.UG.HasSignature G n 0) : G.PosSemidef := by
  obtain ⟨e, P, hP⟩ := h
  rw [cT_conj_eq, Jpq_zero] at hP
  set Q : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ := P.inv
  have hPQ : P.val * Q = 1 := by
    exact P.val_inv
  have hR : G.reindex e e = Q.conjTranspose * 1 * Q := by
    rw [← hP]
    calc G.reindex e e = (P.val * Q).conjTranspose * G.reindex e e * (P.val * Q) := by
          rw [hPQ]; simp
      _ = Q.conjTranspose * (P.val.conjTranspose * G.reindex e e * P.val) * Q := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
  have hpsd : (G.reindex e e).PosSemidef := by
    rw [hR]; exact Matrix.PosSemidef.one.conjTranspose_mul_mul_same Q
  have h2 := hpsd.submatrix e
  have : (G.reindex e e).submatrix e e = G := by
    ext i j; simp
  rwa [this] at h2

end GlobalTheory.DefiniteFrame

open Matrix in

theorem GlobalTheory.DefiniteFrame.frame_signs_pos : ∀ (D : D7) (V : HSp D) (F : GlobalTheory.ChainFr.Fr V) (τ : D.what₂.Tau),
    Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 → ∀ j, F.ε τ j = true := by
  intro D V F τ hs j
  have hG := GlobalTheory.DefiniteFrame.posSemidef_of_hasSignature hs
  have hu : IsUnit (F.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).mp (F.fr_unit τ)
  have hJ : Formalism.REAL.Jm (F.ε τ) = ((F.fr τ)⁻¹).conjTranspose * gramAt D V τ * (F.fr τ)⁻¹ := by
    rw [← F.fr_gram τ, Matrix.conjTranspose_nonsing_inv]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul (F.fr τ)ᴴ (by rw [Matrix.det_conjTranspose]; exact hu.star), Matrix.one_mul]
  have hpsd : (Formalism.REAL.Jm (F.ε τ)).PosSemidef := by
    rw [hJ]; exact hG.conjTranspose_mul_mul_same _
  have hd := hpsd.diag_nonneg (i := j)
  by_contra hne
  simp only [Bool.not_eq_true] at hne
  simp [Formalism.REAL.Jm, hne] at hd
  norm_num at hd
