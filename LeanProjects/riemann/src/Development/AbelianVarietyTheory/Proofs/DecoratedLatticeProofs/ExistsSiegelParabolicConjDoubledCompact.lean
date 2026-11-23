import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BaseChangeTensorConjugationInvolutiveOfInvolution
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsHalfData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsLatticeFrameBcEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulStkRowsZeroDiag
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MapUnitsInvEqScal
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramUnimodular
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ConjElt

theorem compInf_sigR_comm {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : NumberField.InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem compInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : NumberField.InfinitePlace F) (y : E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR w.Completion y := by
  simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem sq_real_of_majorant {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (a b : GL (Fin n) (AF F ⊗[F] E)) (ha : IsMajorantFrame σ J a)
    (hbw : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a) (w : NumberField.InfinitePlace F) :
    (((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1) *
      ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1)).map
        (compInf F E w) = 1 := by
  obtain ⟨s, hs⟩ := ha w
  rw [← hbw w] at hs
  have h1 : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ).map (compInf F E w) =
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) b).1 :=
    Matrix.ext fun i j => compInf_sigR_comm σ w _
  have h2 : (J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))).map (compInf F E w) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) w.Completion J :=
    Matrix.ext fun i j => compInf_inclR_eq w _
  have hH : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1).map
      (compInf F E w) = Matrix.diagonal fun i => if s i = true then 1 else -1 := by
    rw [← hs, Matrix.map_mul, Matrix.map_mul, h1, h2]
    rfl
  rw [Matrix.map_mul, hH, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem gram_blk_mul {R : Type} [CommRing R] (c : R →+* R) {n : ℕ} (b J : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) * dblGram finSumFinEquiv J * (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) * M := by
  have h : Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * Formalism.UG.cT c (blkMat finSumFinEquiv b b) := by
    rw [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  have h2 : Formalism.UG.cT c (blkMat finSumFinEquiv b b) * dblGram finSumFinEquiv J * blkMat finSumFinEquiv b b =
      dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) := by
    rw [cT_blkMat, dblGram, dblGram, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  rw [h, ← h2]
  simp only [Matrix.mul_assoc]

theorem diag_blk_mul {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) (l : Fin (n + n))
    (h : ∀ i : Fin n, M (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l = M (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l)
    (i : Fin n) :
    (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l =
      (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l := by
  simp only [Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := n)).sum_comp, Fintype.sum_sum_type, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, h]

theorem gA_dblSp {D : D7} (A : HSp D) : gA (dblSp A) = dblGram finSumFinEquiv (gA A) :=
  (congrArg (fun x => x.map (incA D)) (gram_hdbl A)).trans ((blkMat_map _ _ (map_zero _) _ _).trans
    (congrArg (blkMat finSumFinEquiv (gA A)) (Matrix.map_neg _ (map_neg _) _)))

theorem gram_frame {D : D7} (A : HSp D) (b : GL (Fin A.rank) (AE D)) (M : GL (Fin (A.rank + A.rank)) (AE D)) :
    adj (blkGL finSumFinEquiv (b, b) * M).1 * gA (dblSp A) * (blkGL finSumFinEquiv (b, b) * M).1 =
      adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 :=
  (congrArg (fun X : Mx D (A.rank + A.rank) (A.rank + A.rank) =>
    adj (blkGL finSumFinEquiv (b, b) * M).1 * X * (blkGL finSumFinEquiv (b, b) * M).1) (gA_dblSp A)).trans
    (gram_blk_mul (cA D) b.1 (gA A) M.1)

theorem exists_siegel_frame {D : D7} (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (b : GL (Fin A.rank) (AE D))
    (M : GL (Fin (A.rank + A.rank)) (AE D))
    (hMg : adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 = incA D μ • rat (Jst D A.rank))
    (hMc : ∀ i j : Fin A.rank,
      M.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) =
      M.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) :
    ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (blkGL finSumFinEquiv (b, b) * M).1 :=
  GlobalTheory.StdUnn.exists_siegel_mul_Tm D A μ hμ (blkGL finSumFinEquiv (b, b) * M) ((gram_frame A b M).trans hMg)
    fun i j => diag_blk_mul b.1 M.1 _ (fun k => hMc k j) i

theorem adj_gram {D : D7} (A : HSp D) (b : Mx D A.rank A.rank) : adj (adj b * gA A * b) = adj b * gA A * b := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem sq_real {D : D7} (A : HSp D) (a b : GL (Fin A.rank) (AE D)) (ha : IsMaj A a)
    (hbw : ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a)
    (w : NumberField.InfinitePlace D.host.F) :
    ((adj b.1 * gA A * b.1) * (adj b.1 * gA A * b.1)).map (compInf D.host.F D.host.E w) = 1 :=
  sq_real_of_majorant _ _ a b ha hbw w

theorem exists_isConj : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∀ (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∃ p : siegel A, IsConj A a κ p := by
  intro D
  obtain ⟨μ, hμ, u, ε, hue⟩ := GlobalTheory.StdUnn.scalData_exists D
  obtain ⟨t, ht⟩ := GlobalTheory.StdUnn.exists_halfData D
  refine ⟨μ, hμ, fun A a ha κ hκ => ?_⟩
  obtain ⟨b, hbL, hbw⟩ := GlobalTheory.StdUnn.exists_isLatticeFrame_bc_eq D A a
  obtain ⟨Hm, hHm, hHmI⟩ := GlobalTheory.StdUnn.Unimod.gram_unimodular D A b hbL
  have hherm : adj Hm.1 = Hm.1 := by rw [hHm]; exact adj_gram A b.1
  have hsq : ∀ w, (Hm.1 * Hm.1).map (compInf D.host.F D.host.E w) = 1 := fun w => by
    rw [hHm]; exact sq_real A a b ha hbw w
  obtain ⟨M, M', hMg, hMc, hM'I, hMu, hMw⟩ := GlobalTheory.StdUnn.Frame.exists_frame D A.rank Hm hherm hHmI hsq μ u ε t hμ hue ht
  rw [hHm] at hMg
  obtain ⟨p, hp⟩ := exists_siegel_frame A μ hμ b M hMg hMc
  exact ⟨p, GlobalTheory.StdUnn.Conj.isConj_of_frame D A μ hμ κ hκ a b hbL hbw M M' u hM'I hMu hMw p hp⟩

end GlobalTheory.StdUnn.ConjElt
