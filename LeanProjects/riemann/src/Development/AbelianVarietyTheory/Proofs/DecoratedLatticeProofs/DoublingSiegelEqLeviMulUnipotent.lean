import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixSDblDecZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP
open GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw

open Matrix

noncomputable section

namespace GlobalTheory.Core.Rk.SWLaw

variable {D : D7}

def stkRows {R : Type} {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) R) : Matrix (Fin (a + a)) (Fin k) R :=
  (Matrix.fromRows X Y).submatrix finSumFinEquiv.symm id

theorem stkRows_mul {R : Type} [CommRing R] {a k l : ℕ} (X Y : Matrix (Fin a) (Fin k) R) (B : Matrix (Fin k) (Fin l) R) :
    stkRows X Y * B = stkRows (X * B) (Y * B) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [stkRows, Matrix.mul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp [Matrix.mul_apply]

theorem keepsDiag_mul_stkRows {R : Type} [CommRing R] {n k : ℕ} {M : Matrix (Fin (n + n)) (Fin (n + n)) R}
    (h : KeepsDiag finSumFinEquiv M) (X : Matrix (Fin n) (Fin k) R) :
    M * stkRows X X = stkRows (leviMat finSumFinEquiv M * X) (leviMat finSumFinEquiv M * X) := by
  have hk := (keepsDiag_iff finSumFinEquiv).1 h
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [Matrix.mul_apply, stkRows, Matrix.submatrix_apply, id]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Fintype.sum_sum_type, Equiv.symm_apply_apply, Matrix.fromRows_apply_inl, Matrix.fromRows_apply_inr]
  rw [← Finset.sum_add_distrib]
  rcases s with a | a
  · simp only [Matrix.fromRows_apply_inl, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, add_mul]
  · simp only [Matrix.fromRows_apply_inr, Matrix.mul_apply, leviMat, Matrix.add_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂, Matrix.of_apply, Matrix.submatrix_apply, ← add_mul, ← hk]

theorem rat_stackRows {a k : ℕ} (X Y : Matrix (Fin a) (Fin k) D.host.E) :
    rat (stackRows X Y) = stkRows (rat X) (rat Y) := by
  ext i j
  obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
  simp only [rat, stackRows, stkRows, Matrix.map_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, id]
  rcases s with s | s <;> simp

theorem dblDec_jX (A : HSp D) : (dblDec A).jX = stkRows (giA A) (giA A) := rat_stackRows _ _

theorem siegel_mt_jX (A : HSp D) {g : GA D (dblSp A)} (hg : g ∈ siegel A) :
    mt (dblSp A) g ⬝ (dblDec A).jX =
      (dblDec A).jX ⬝ (gA A ⬝ leviMat finSumFinEquiv (mt (dblSp A) g) ⬝ giA A) := by
  have hk : KeepsDiag finSumFinEquiv (mt (dblSp A) g) := mem_siegelOf.1 hg
  rw [dblDec_jX, keepsDiag_mul_stkRows hk, stkRows_mul]
  simp only [← Matrix.mul_assoc, giA_mul_gA, Matrix.one_mul]

set_option maxHeartbeats 1000000 in

theorem siegel_eq_levi_nC : ∀ (D : D7) (A : HSp D) (p : siegel A), ∃ (a : GL (Fin A.rank) (AE D)) (c : skewA D A.rank),
    (p : GA D (dblSp A)) = (dblDec A).levi a * (dblDec A).nC c := by
  intro D A p
  obtain ⟨p, hp⟩ := p
  obtain ⟨α, hα⟩ : ∃ α : Mx D A.rank A.rank, mt (dblSp A) p ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α := ⟨_, siegel_mt_jX A hp⟩
  obtain ⟨α', hα'⟩ : ∃ α' : Mx D A.rank A.rank, mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX = (dblDec A).jX ⬝ α' :=
    ⟨_, siegel_mt_jX A (inv_mem hp)⟩
  have e1 : α ⬝ α' = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α ⬝ α') := by
      calc (dblDec A).jX = mt (dblSp A) (p * p⁻¹) ⬝ (dblDec A).jX := by
            rw [mul_inv_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p ⬝ (mt (dblSp A) p⁻¹ ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α ⬝ α') := by rw [hα', ← Matrix.mul_assoc, hα, Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have e2 : α' ⬝ α = 1 := by
    have h : (dblDec A).jX = (dblDec A).jX ⬝ (α' ⬝ α) := by
      calc (dblDec A).jX = mt (dblSp A) (p⁻¹ * p) ⬝ (dblDec A).jX := by
            rw [inv_mul_cancel, GlobalTheory.MixModel.mt_one, Matrix.one_mul]
        _ = mt (dblSp A) p⁻¹ ⬝ (mt (dblSp A) p ⬝ (dblDec A).jX) := by
            rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc]
        _ = (dblDec A).jX ⬝ (α' ⬝ α) := by rw [hα, ← Matrix.mul_assoc, hα', Matrix.mul_assoc]
    have h2 := congrArg (HMul.hMul (dblDec A).pX) h
    rwa [← Matrix.mul_assoc, (dblDec A).pX_jX, Matrix.one_mul, eq_comm] at h2
  have u := GlobalTheory.MixModel.mt_unitary (dblSp A) p

  have h1 : adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 1 := by
    calc adj α ⬝ ((dblDec A).pY ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (mt (dblSp A) p ⬝ (dblDec A).jX) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) := by
          rw [hα, (dblDec A).pY_eq, adj_mul]; simp only [Matrix.mul_assoc]
      _ = adj (dblDec A).jX ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 1 := by rw [u, (dblDec A).gram_XY]
  have hG : adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY)) = 0 := by
    calc adj (mt (dblSp A) p ⬝ (dblDec A).jY) ⬝ (gA (dblSp A) ⬝ (mt (dblSp A) p ⬝ (dblDec A).jY))
        = adj (dblDec A).jY ⬝ ((adj (mt (dblSp A) p) ⬝ (gA (dblSp A) ⬝ mt (dblSp A) p)) ⬝ (dblDec A).jY) := by
          rw [adj_mul]; simp only [Matrix.mul_assoc]
      _ = 0 := by rw [u, (dblDec A).gram_YY]
  generalize hYdef : mt (dblSp A) p ⬝ (dblDec A).jY = Y at h1 hG
  have hpY : (dblDec A).pY ⬝ Y = adj α' := by
    calc (dblDec A).pY ⬝ Y = (adj α' ⬝ adj α) ⬝ ((dblDec A).pY ⬝ Y) := by
          rw [← adj_mul, e1, adj_one, Matrix.one_mul]
      _ = adj α' := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have h0 : (dblDec A).j0 ⬝ (dblDec A).p0 = 0 :=
    Matrix.ext fun i j => by rw [Matrix.mul_apply]; exact Finset.sum_eq_zero fun k _ => Fin.elim0 k
  generalize hu : (dblDec A).pX ⬝ Y = w
  have hY : Y = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
    calc Y = ((dblDec A).jX ⬝ (dblDec A).pX + (dblDec A).j0 ⬝ (dblDec A).p0 + (dblDec A).jY ⬝ (dblDec A).pY) ⬝ Y := by
          rw [(dblDec A).sum_eq_one, Matrix.one_mul]
      _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ w := by
          rw [h0, add_zero, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hpY, hu, add_comm]
  have hskew : adj (α' ⬝ w) = -(α' ⬝ w) := by
    rw [hY] at hG
    simp only [adj_add, adj_mul, adj_adj, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
      cancel₃ (dblDec A).gram_YY, cancel₃ (dblDec A).gram_YX, cancel₃ (dblDec A).gram_XY, cancel₃ (dblDec A).gram_XX,
      Matrix.zero_mul, Matrix.mul_zero, Matrix.one_mul, zero_add, add_zero] at hG
    rw [adj_mul, eq_neg_iff_add_eq_zero]
    exact hG
  let a : GL (Fin A.rank) (AE D) := ⟨α, α', e1, e2⟩
  refine ⟨a, ⟨α' ⬝ w, mem_skewA.2 hskew⟩, (dblDec A).ga_ext ?_ ?_ ?_⟩
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jX, (dblDec A).levi_jX, hα]
  · exact Matrix.ext fun _ j => Fin.elim0 j
  · rw [GlobalTheory.MixModel.mt_mul, Matrix.mul_assoc, (dblDec A).nC_jY, Matrix.mul_add, (dblDec A).levi_jY,
      ← Matrix.mul_assoc, (dblDec A).levi_jX, hYdef, hY]
    show _ = (dblDec A).jY ⬝ adj α' + (dblDec A).jX ⬝ α ⬝ (α' ⬝ w)
    rw [Matrix.mul_assoc (dblDec A).jX, ← Matrix.mul_assoc α, e1, Matrix.one_mul]

end GlobalTheory.Core.Rk.SWLaw
