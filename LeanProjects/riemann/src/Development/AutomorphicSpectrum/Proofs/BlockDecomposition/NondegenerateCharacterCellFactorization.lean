import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CosetCell
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.AdelicConjTransposeBlockMatrixTwoByTwoFin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelParabolicUnnMatrixBlockUpperTriangular
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SummableCell
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinRationalPoints
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousHalfTr
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf

namespace GlobalTheory.CompanionTheory.SwUnf.SmallCell
open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect

section Abstract
variable {R : Type} [Ring R]

theorem inv_blocks (A B C E As Bs Cs Es : R) (h1 : -(Cs * A) + As * C = 0) (h2 : -(Cs * B) + As * E = 1)
    (h3 : -(Es * A) + Bs * C = -1) (h4 : -(Es * B) + Bs * E = 0) :
    Es * A + -Bs * C = 1 ∧ Es * B + -Bs * E = 0 ∧ -Cs * A + As * C = 0 ∧ -Cs * B + As * E = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) -h3
  · linear_combination (norm := noncomm_ring) -h4
  · linear_combination (norm := noncomm_ring) h1
  · linear_combination (norm := noncomm_ring) h2

theorem conj_blocks (A B C E ν As Bs Cs Es : R) (h1 : A * Es + B * -Cs = 1) (h2 : A * -Bs + B * As = 0)
    (h3 : C * Es + E * -Cs = 0) (h4 : C * -Bs + E * As = 1) :
    (A * 1 + B * 0) * Es + (A * ν + B * 1) * -Cs = 1 - A * ν * Cs ∧
      (A * 1 + B * 0) * -Bs + (A * ν + B * 1) * As = A * ν * As ∧
      (C * 1 + E * 0) * Es + (C * ν + E * 1) * -Cs = -(C * ν * Cs) ∧
      (C * 1 + E * 0) * -Bs + (C * ν + E * 1) * As = 1 + C * ν * As := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (norm := noncomm_ring) h1
  · linear_combination (norm := noncomm_ring) h2
  · linear_combination (norm := noncomm_ring) h3
  · linear_combination (norm := noncomm_ring) h4

end Abstract

section GenMat
variable {R : Type} [CommRing R] {n : ℕ}

theorem gen_block (A C As Cs : Matrix (Fin n) (Fin n) R) (Vc : Matrix (Fin n) (Fin 1) R)
    (Rw : Matrix (Fin 1) (Fin n) R) (Rs : Matrix (Fin n) (Fin 1) R) (Vs : Matrix (Fin 1) (Fin n) R) (τ : R)
    (hC : C ⬝ Vc = 0) (hCs : Vs ⬝ Cs = 0) (hcomm : Cs * A = As * C) :
    C * (τ • (Vc ⬝ Rw + Rs ⬝ Vs)) * Cs = 0 ∧ (1 - A * (τ • (Vc ⬝ Rw + Rs ⬝ Vs)) * Cs).det = 1 := by
  have hνC : (τ • (Vc ⬝ Rw + Rs ⬝ Vs)) * Cs = τ • (Vc ⬝ (Rw ⬝ Cs)) := by
    rw [Matrix.smul_mul, Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc, hCs, Matrix.mul_zero, add_zero]
  constructor
  · rw [Matrix.mul_assoc, hνC, Matrix.mul_smul, ← Matrix.mul_assoc, hC, Matrix.zero_mul, smul_zero]
  · have ha : 1 - A * (τ • (Vc ⬝ Rw + Rs ⬝ Vs)) * Cs = 1 - (τ • (A ⬝ Vc)) ⬝ (Rw ⬝ Cs) := by
      rw [Matrix.mul_assoc A, hνC, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    have hYX : (Rw ⬝ Cs) ⬝ (τ • (A ⬝ Vc)) = 0 := by
      rw [Matrix.mul_smul, Matrix.mul_assoc, ← Matrix.mul_assoc Cs, hcomm, Matrix.mul_assoc As, hC,
        Matrix.mul_zero, Matrix.mul_zero, smul_zero]
    rw [ha, Matrix.det_one_sub_mul_comm, hYX, sub_zero, Matrix.det_one]

theorem gen_trace (b : Matrix (Fin n) (Fin n) R) (Vc : Matrix (Fin n) (Fin 1) R)
    (Rw : Matrix (Fin 1) (Fin n) R) (Rs : Matrix (Fin n) (Fin 1) R) (Vs : Matrix (Fin 1) (Fin n) R) (τ : R)
    (hS : Rw ⬝ b ⬝ Vc = 1) (hS' : Vs ⬝ b ⬝ Rs = 1) :
    Matrix.trace (b ⬝ (τ • (Vc ⬝ Rw + Rs ⬝ Vs))) = τ * 2 := by
  have t1 : Matrix.trace (b ⬝ (Vc ⬝ Rw)) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hS]
    simp
  have t2 : Matrix.trace (b ⬝ (Rs ⬝ Vs)) = 1 := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hS']
    simp
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.mul_add, Matrix.trace_add, t1, t2, smul_eq_mul, one_add_one_eq_two]

end GenMat

variable {D : D7} {n : ℕ}

theorem blkA_blk4 {R : Type} (a b c d : Matrix (Fin n) (Fin n) R) : blkA (blk4 a b c d) = a := by
  ext i j
  simp [blkA, blk4, Matrix.toBlocks₁₁]

theorem lowerC_map {R S : Type} (f : R → S) (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    lowerC (M.map f) = (lowerC M).map f := by
  ext i j
  simp [lowerC, Matrix.toBlocks₂₁]

theorem exists_blocks {R : Type} (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    ∃ b d, M = blk4 (blkA M) b (lowerC M) d := by
  refine ⟨(M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₁₂,
    (M.submatrix finSumFinEquiv finSumFinEquiv).toBlocks₂₂, ?_⟩
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rcases i with i | i <;> rcases j with j | j <;> rfl

theorem unitary_rel (g : G D n) {A B C E' : Mx D n n} (hg : mat g = blk4 A B C E') :
    -(adj C * A) + adj A * C = 0 ∧ -(adj C * B) + adj A * E' = 1 ∧
      -(adj E' * A) + adj B * C = -1 ∧ -(adj E' * B) + adj B * E' = 0 := by
  have h : adj (mat g) * JR (AF D.host.F) (Jst D n) * mat g = JR (AF D.host.F) (Jst D n) := g.2
  rw [JR_Jst, hg] at h
  simp only [adelicConjTranspose_blockMatrixTwoByTwoFin, submatrix_fromBlocks_mul, mul_zero, zero_mul, mul_one, one_mul, add_zero, zero_add, mul_neg, neg_mul] at h
  exact blockMatrixTwoByTwoFin_injective h

theorem mat_inv (g : G D n) {A B C E' : Mx D n n} (hg : mat g = blk4 A B C E') :
    mat g⁻¹ = blk4 (adj E') (-adj B) (-adj C) (adj A) := by
  obtain ⟨h1, h2, h3, h4⟩ := unitary_rel g hg
  obtain ⟨e1, e2, e3, e4⟩ := inv_blocks A B C E' (adj A) (adj B) (adj C) (adj E') h1 h2 h3 h4
  have hN : blk4 (adj E') (-adj B) (-adj C) (adj A) * mat g = 1 := by
    rw [hg, submatrix_fromBlocks_mul, e1, e2, e3, e4, block_matrix_one]
  have hm : mat g * mat g⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  calc mat g⁻¹ = (blk4 (adj E') (-adj B) (-adj C) (adj A) * mat g) * mat g⁻¹ := by rw [hN, one_mul]
    _ = _ := by rw [mul_assoc, hm, mul_one]

theorem mem_siegelParabolic_of_lowerLeft_entries_eq_zero {p : G D n} {a b d : Mx D n n} (hp : mat p = blk4 a b 0 d) : p ∈ P D n := by
  have key : ∀ (q : G D n) (a b d : Mx D n n), mat q = blk4 a b 0 d →
      ∀ x ∈ upperHalf D n, mat q *ᵥ x ∈ upperHalf D n := by
    intro q a b d hq x hx
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.mem_upperHalf] at hx ⊢
    intro i
    rw [GlobalTheory.CompanionTheory.RatPtsUnn.mulVec_inr]
    have h0 : (fun k => x (finSumFinEquiv (Sum.inr k))) = 0 := funext hx
    have e : ∀ j, blk4 a b 0 d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = 0 := fun j => by
      simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [h0, Matrix.mulVec_zero, hq]
    simp only [e, zero_mul, Finset.sum_const_zero, Pi.zero_apply, add_zero]
  rw [GlobalTheory.CompanionTheory.RatPtsUnn.mem_P_iff]
  intro x
  refine ⟨key p _ _ _ hp x, fun hx => ?_⟩
  have h := key p⁻¹ (adj d) (-adj b) (adj a) (by rw [mat_inv p hp, adj_zero, neg_zero]) _ hx
  rwa [Matrix.mulVec_mulVec, ← mat_mul, inv_mul_cancel, mat_one, Matrix.one_mulVec] at h

theorem conj_block (γ u : G D n) {A B C E' ν : Mx D n n} (hg : mat γ = blk4 A B C E')
    (hu : mat u = blk4 1 ν 0 1) :
    mat (γ * u * γ⁻¹) =
      blk4 (1 - A * ν * adj C) (A * ν * adj A) (-(C * ν * adj C)) (1 + C * ν * adj A) := by
  have hi := mat_inv γ hg
  have hm : mat γ * mat γ⁻¹ = 1 := by rw [← mat_mul, mul_inv_cancel, mat_one]
  rw [hg, hi, submatrix_fromBlocks_mul, ← block_matrix_one] at hm
  obtain ⟨h1, h2, h3, h4⟩ := blockMatrixTwoByTwoFin_injective hm
  obtain ⟨e1, e2, e3, e4⟩ := conj_blocks A B C E' ν (adj A) (adj B) (adj C) (adj E') h1 h2 h3 h4
  rw [mat_mul, mat_mul, hg, hu, hi, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [mul_zero, mul_one] at e1 e2 e3 e4 ⊢
  rw [e1, e2, e3, e4]

theorem cell_absorb {ν : Mx D n n} (Vc : Mx D n 1) (Rw : Mx D 1 n) (τ : AE D)
    (hν : ν = τ • (Vc ⬝ Rw + adj Rw ⬝ adj Vc)) (γ u : G D n) (hu : mat u = blk4 1 ν 0 1)
    (hC : lowerC (mat γ) ⬝ Vc = 0) :
    ∃ p ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 ∧
      Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = p * γ := by
  obtain ⟨b, d, hg⟩ := exists_blocks (mat γ)
  generalize hA : blkA (mat γ) = A at hg
  generalize hCd : lowerC (mat γ) = C at hg hC
  subst hν
  have hCs : adj Vc ⬝ adj C = 0 := by rw [← adj_mul, hC, adj_zero]
  have hcomm : adj C * A = adj A * C := neg_add_eq_zero.1 (unitary_rel γ hg).1
  obtain ⟨hz, hdet⟩ := gen_block A C (adj A) (adj C) Vc Rw (adj Rw) (adj Vc) τ hC hCs hcomm
  have hp := conj_block γ u hg hu
  rw [hz, neg_zero] at hp
  have hP := mem_siegelParabolic_of_lowerLeft_entries_eq_zero hp
  obtain ⟨a, ha⟩ := exists_blkA hP
  refine ⟨γ * u * γ⁻¹, hP, a, ha, ?_, by simp⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, ← ha, hp, blkA_blk4, hdet, Units.val_one]

theorem trace_val (b : Mx D n n) (hb : adj b = b) (Vc : Mx D n 1) (Rw : Mx D 1 n) (τ : AE D)
    (hS : Rw ⬝ b ⬝ Vc = 1) : Matrix.trace (b ⬝ (τ • (Vc ⬝ Rw + adj Rw ⬝ adj Vc))) = τ * 2 := by
  have hS' : adj Vc ⬝ b ⬝ adj Rw = 1 := by
    have h := congrArg adj hS
    rw [adj_mul, adj_mul, hb, adj_one, ← Matrix.mul_assoc] at h
    exact h
  exact gen_trace b Vc Rw (adj Rw) (adj Vc) τ hS hS'

theorem halfTr_algebraMap_mul (t : AF D.host.F) (z : AE D) :
    halfTr (algebraMap (AF D.host.F) (AE D) t * z) = t * halfTr z := by
  have h : Algebra.trace (AF D.host.F) (AE D) (algebraMap (AF D.host.F) (AE D) t * z) =
      t * Algebra.trace (AF D.host.F) (AE D) z := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  rw [halfTr, halfTr, trA, h, mul_left_comm]

theorem exists_scalar (x : AF D.host.F) :
    ∃ t : AF D.host.F, halfTr (algebraMap (AF D.host.F) (AE D) t * 2) = x := by
  have e2 : (2 : AE D) = incA D 2 := (map_ofNat (incA D) 2).symm
  have hf : Module.finrank D.host.F D.host.E ≠ 0 := Module.finrank_pos.ne'
  have hc : (1 / 2 * Algebra.trace D.host.F D.host.E 2 : D.host.F) ≠ 0 := by
    have h2 : (2 : D.host.E) = algebraMap D.host.F D.host.E 2 := (map_ofNat _ 2).symm
    rw [h2, Algebra.trace_algebraMap]
    simp [hf]
  refine ⟨x * algebraMap D.host.F (AF D.host.F) (1 / 2 * Algebra.trace D.host.F D.host.E 2)⁻¹, ?_⟩
  rw [halfTr_algebraMap_mul, e2, GlobalTheory.CompanionTheory.HermPoisson.halfTr_incA', mul_assoc, ← map_mul, inv_mul_cancel₀ hc,
    map_one, mul_one]

theorem cA_algebraMap' (t : AF D.host.F) :
    cA D (algebraMap (AF D.host.F) (AE D) t) = algebraMap (AF D.host.F) (AE D) t := by
  change t ⊗ₜ[D.host.F] D.sp.cm.sig 1 = _
  rw [map_one]
  rfl

theorem adj_rat_herm (β : HermE D n) : adj (rat β.1 : Mx D n n) = rat β.1 := by
  ext i j
  have h := congrFun (congrFun β.2 i) j
  change cA D (incA D (β.1 j i)) = incA D (β.1 i j)
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg _ h

theorem small_cell : ∀ {D : D7} {n : ℕ} {ψ : AddChar (AF D.host.F) ℂ}, IsCharAF D.host.F ψ → ∀ (β : HermE D n), β.1.det ≠ 0 → ∀ (W : Submodule D.host.E (Fin n → D.host.E)), W ≠ ⊥ → ∃ ν : hermA D n, ψ (-halfTr (Matrix.trace (HMul.hMul (β.1.map (incA D)) ν.1 : Mx D n n))) ≠ 1 ∧ ∀ (γ u : G D n), γ ∈ GF D n → ∀ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) → cellKer x = W → mat u = blk4 1 ν.1 0 1 → ∃ p ∈ P D n, ∃ a : GL (Fin n) (AE D), blkA (mat p) = a.1 ∧ Matrix.GeneralLinearGroup.det a = 1 ∧ γ * u = p * γ := by
  intro D n ψ hψ β hβ W hW
  obtain ⟨v, hvW, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hw : β.1 *ᵥ v ≠ 0 := fun h => hv0 (Matrix.eq_zero_of_mulVec_eq_zero hβ h)
  obtain ⟨i0, hi0⟩ := Function.ne_iff.1 hw
  let V0 : Matrix (Fin n) (Fin 1) D.host.E := Matrix.replicateCol _ v
  let R0 : Matrix (Fin 1) (Fin n) D.host.E := Matrix.replicateRow _ (Pi.single i0 ((β.1 *ᵥ v) i0)⁻¹)
  have hbV : β.1 ⬝ V0 = Matrix.replicateCol _ (β.1 *ᵥ v) := by
    ext i j
    simp [V0, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  have hS0 : R0 ⬝ β.1 ⬝ V0 = (1 : Matrix (Fin 1) (Fin 1) D.host.E) := by
    rw [Matrix.mul_assoc, hbV]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [R0, Matrix.mul_apply, Pi.single_apply, inv_mul_cancel₀ (show (β.1 *ᵥ v) i0 ≠ 0 from hi0)]
  have hS : (rat R0 : Mx D 1 n) ⬝ (rat β.1 : Mx D n n) ⬝ (rat V0 : Mx D n 1) = 1 := by
    rw [← rat_mul, ← rat_mul, hS0]
    ext a b
    obtain rfl : a = b := Subsingleton.elim _ _
    simp [rat]
  obtain ⟨x0, hx0⟩ := hψ.2.2.2
  obtain ⟨t, ht⟩ := exists_scalar (D := D) x0
  have hν : adj ((algebraMap (AF D.host.F) (AE D) t) • ((rat V0 : Mx D n 1) ⬝ (rat R0 : Mx D 1 n) + adj (rat R0 : Mx D 1 n) ⬝ adj (rat V0 : Mx D n 1))) =
      (algebraMap (AF D.host.F) (AE D) t) • ((rat V0 : Mx D n 1) ⬝ (rat R0 : Mx D 1 n) + adj (rat R0 : Mx D 1 n) ⬝ adj (rat V0 : Mx D n 1)) := by
    rw [adj_smul, cA_algebraMap', adj_add, adj_mul, adj_mul, adj_adj, adj_adj, add_comm]
  refine ⟨⟨_, hν⟩, ?_, ?_⟩
  · have h := trace_val (rat β.1) (adj_rat_herm β) (rat V0) (rat R0) (algebraMap (AF D.host.F) (AE D) t) hS
    change ψ (-halfTr (Matrix.trace ((rat β.1 : Mx D n n) ⬝ _))) ≠ 1
    rw [h, ht, AddChar.map_neg_eq_inv]
    intro h1
    exact hx0 (inv_eq_one.1 h1)
  · intro γ u hγ x hx hW' hu
    refine cell_absorb (rat V0) (rat R0) _ rfl γ u hu ?_
    have hv : lowerC x *ᵥ v = 0 := by
      rw [← hW'] at hvW
      exact hvW
    have h0 : (HMul.hMul (lowerC x) V0 : Matrix (Fin n) (Fin 1) D.host.E) = 0 := by
      refine Matrix.ext fun i j => ?_
      have := congrFun hv i
      simpa [V0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using this
    rw [hx, lowerC_map]
    change (rat (lowerC x) : Mx D n n) ⬝ (rat V0 : Mx D n 1) = 0
    rw [← rat_mul, h0]
    ext i j
    simp [rat]

end GlobalTheory.CompanionTheory.SwUnf.SmallCell
