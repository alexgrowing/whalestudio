import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemNsp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
open GlobalTheory.WeilM Matrix

noncomputable section
namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model

variable {k : Type} [Field k] {R T D : Type} [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T]
  [Fintype D] [DecidableEq D]

def shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k :=
  fromRows Y.toRows₁ (Y.toRows₂ + c * Y.toRows₁)

def dil (t : k) (Y : Matrix (R ⊕ T) D k) : Matrix (R ⊕ T) D k := fromRows Y.toRows₁ (t • Y.toRows₂)

def stack (Y₁ : Matrix R D k) (C : Matrix T R k) : Matrix (R ⊕ T) D k := fromRows Y₁ (C * Y₁)

def shearGL (c : Matrix T R k) : GL (R ⊕ T) k :=
  ⟨fromBlocks 1 cᵀ 0 1, fromBlocks 1 (-cᵀ) 0 1, by simp [fromBlocks_multiply],
    by simp [fromBlocks_multiply]⟩

def dilGL (t : kˣ) : GL (R ⊕ T) k :=
  ⟨diagonal (Sum.elim 1 fun _ => (t : k)), diagonal (Sum.elim 1 fun _ => ((t⁻¹ : kˣ) : k)), by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp, by
    rw [diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; rcases i with i | i <;> simp⟩

@[simp] theorem toRows₁_shear (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) : (shear c Y).toRows₁ = Y.toRows₁ := by
  simp [shear]

@[simp] theorem toRows₁_dil (t : k) (Y : Matrix (R ⊕ T) D k) : (dil t Y).toRows₁ = Y.toRows₁ := by
  simp [dil]

@[simp] theorem toRows₁_stack (Y₁ : Matrix R D k) (C : Matrix T R k) : (stack Y₁ C).toRows₁ = Y₁ := by
  simp [stack]

theorem submatrix_inl_eq (Y : Matrix (R ⊕ T) D k) (τ : R → D) :
    Y.submatrix Sum.inl τ = Y.toRows₁.submatrix id τ := rfl

theorem shear_stack (c : Matrix T R k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    shear c (stack Y₁ C) = stack Y₁ (C + c) := by
  simp [shear, stack, Matrix.add_mul]

theorem dil_stack (t : k) (Y₁ : Matrix R D k) (C : Matrix T R k) :
    dil t (stack Y₁ C) = stack Y₁ (t • C) := by
  simp [dil, stack, smul_mul]

theorem shear_sub_self (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    shear c Y - Y = fromRows 0 (c * Y.toRows₁) := by
  ext (i | i) j <;> simp [shear]

theorem shearGL_transpose_mul (c : Matrix T R k) (Y : Matrix (R ⊕ T) D k) :
    (shearGL c).valᵀ * Y = shear c Y := by
  ext (i | i) j <;> simp [shearGL, shear, fromBlocks_transpose, Matrix.mul_apply, Fintype.sum_sum_type,
    Matrix.one_apply, add_comm]

theorem dilGL_transpose_mul (t : kˣ) (Y : Matrix (R ⊕ T) D k) :
    (dilGL t : GL (R ⊕ T) k).valᵀ * Y = dil (t : k) Y := by
  ext (i | i) j <;> simp [dilGL, dil, diagonal_transpose, Matrix.mul_apply, Fintype.sum_sum_type, diagonal_apply]

theorem gdet_shearGL (c : Matrix T R k) : gdet (shearGL c) = 1 := by
  ext; simp [shearGL, gdet, det_fromBlocks_zero₂₁]

theorem gdet_dilGL (t : kˣ) : gdet (dilGL t : GL (R ⊕ T) k) = t ^ Fintype.card T := by
  ext; simp [dilGL, gdet, det_diagonal, Fintype.prod_sum_type]

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem omB_shearGL (ν : kˣ →* ℂˣ) (c : Matrix T R k) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (shearGL c) 1 Ψ Y = Ψ (shear c Y) := by
  simp [omB, gdet_shearGL, shearGL_transpose_mul]

theorem exists_apow_eq (x : kˣ) (n : ℕ) : ∃ r : ℝ, 0 < r ∧ apow x ((n : ℂ) / 2) = r := by
  refine ⟨GlobalTheory.SplitWeil.nabs k x ^ ((n : ℝ) / 2), Real.rpow_pos_of_pos (nabs_pos x) _, ?_⟩
  rw [apow, Complex.ofReal_cpow (nabs_pos x).le]
  push_cast; rfl

theorem omB_dilGL (ν : kˣ →* ℂˣ) (t : kˣ) (Ψ : Matrix (R ⊕ T) D k → ℂ) (Y : Matrix (R ⊕ T) D k) :
    omB ν ν (dilGL t : GL (R ⊕ T) k) 1 Ψ Y =
      (ν t : ℂ) ^ Fintype.card T * apow (t ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) * Ψ (dil (t : k) Y) := by
  simp [omB, gdet_dilGL, dilGL_transpose_mul]

end GlobalTheory.RankChart

namespace GlobalTheory.RankChart
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel

theorem out_mk_sub_mem {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x : H) :
    (((QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H).out : H) : G) - x ∈ L := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  have := L.neg_mem h
  simpa [neg_add_eq_sub] using this

theorem mk_eq_mk_iff {G : Type} [AddCommGroup G] (H L : AddSubgroup G) (x y : H) :
    (QuotientAddGroup.mk x : H ⧸ L.addSubgroupOf H) = QuotientAddGroup.mk y ↔ (x : G) - y ∈ L := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, ← L.neg_mem_iff]
  simp [neg_add_eq_sub]

open Classical in

theorem sum_shift_out {G : Type} [AddCommGroup G] (F : G → ℂ) (H L : AddSubgroup G)
    [Fintype (H ⧸ L.addSubgroupOf H)] (hL : ∀ x y, y - x ∈ L → F y = F x) (hH : ∀ x, F x ≠ 0 → x ∈ H) (x : G) :
    ∑ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
      if x ∈ H then ∑ q : H ⧸ L.addSubgroupOf H, F ((q.out : H) : G) else 0 := by
  split_ifs with hx
  · have key : ∀ q : H ⧸ L.addSubgroupOf H, F (x + ((q.out : H) : G)) =
        F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G) := by
      intro q
      have e : (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q =
          QuotientAddGroup.mk ((⟨x, hx⟩ : H) + q.out) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      rw [e]
      exact (hL (((⟨x, hx⟩ : H) + q.out : H) : G) _ (out_mk_sub_mem H L ((⟨x, hx⟩ : H) + q.out))).symm
    rw [Finset.sum_congr rfl fun q _ => key q]
    exact Fintype.sum_equiv (Equiv.addLeft (QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H))
      (fun q => F ((((QuotientAddGroup.mk (⟨x, hx⟩ : H) : H ⧸ L.addSubgroupOf H) + q).out : H) : G))
      (fun q => F ((q.out : H) : G)) fun q => rfl
  · refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    have := H.sub_mem (hH _ h) (q.out : H).2
    rw [add_sub_cancel_right] at this
    exact hx this

open Classical in

theorem sum_ite_out {G : Type} [AddCommGroup G] (H H' : AddSubgroup G) [Fintype (H' ⧸ H.addSubgroupOf H')]
    (hHH' : H ≤ H') (c : ℂ) (x : G) :
    ∑ q : H' ⧸ H.addSubgroupOf H', (if x + ((q.out : H') : G) ∈ H then c else 0) = if x ∈ H' then c else 0 := by
  split_ifs with hx
  · rw [Finset.sum_eq_single (QuotientAddGroup.mk (⟨-x, H'.neg_mem hx⟩ : H'))]
    · rw [if_pos]
      have := out_mk_sub_mem H' H (⟨-x, H'.neg_mem hx⟩ : H')
      rwa [sub_neg_eq_add, add_comm] at this
    · intro q _ hq
      rw [if_neg]
      intro hmem
      apply hq
      rw [← QuotientAddGroup.out_eq' q, mk_eq_mk_iff]
      rwa [sub_neg_eq_add, add_comm]
    · simp
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [if_neg]
    intro hmem
    have := H'.sub_mem (hHH' hmem) (q.out : H').2
    rw [add_sub_cancel_right] at this
    exact hx this

end GlobalTheory.RankChart
