import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

open GlobalTheory.StepData ValuativeRel Matrix

namespace GlobalTheory.StepData
open GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem reGL_symm_mem_KO {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (e : a ≃ b)
    (g : GL b k) : (reGL e).symm g ∈ KO k a ↔ g ∈ KO k b := by
  have hinv : ((reGL e).symm g)⁻¹ = (reGL e).symm g⁻¹ := (map_inv _ _).symm
  rw [mem_KO, mem_KO, hinv, reGL_symm_val, reGL_symm_val]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · simpa using h1 (e.symm i) (e.symm j)
    · simpa using h2 (e.symm i) (e.symm j)
  · rintro ⟨h1, h2⟩
    exact ⟨fun i j => h1 (e i) (e j), fun i j => h2 (e i) (e j)⟩

variable {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t]

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem blk_ixSucc_inl {j : ℕ} (a : Ix r t j) : (ixSucc r t j (.inl a)).blk = a.blk := by
  rcases a with x | ⟨i, s⟩ <;> rfl

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem blk_ixSucc_inr {j : ℕ} (s : t) : (ixSucc r t j (.inr s)).blk = j + 1 := rfl

omit [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] in
theorem Ix.blk_le {j : ℕ} (a : Ix r t j) : a.blk ≤ j := by
  rcases a with x | ⟨i, s⟩
  · exact Nat.zero_le _
  · exact i.isLt

private theorem mem_reindex_J_iff {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (P : TypeDatum k a) (e : a ≃ b) (g : GL b k) : g ∈ (P.reindex e).J ↔ (reGL e).symm g ∈ P.J :=
  Level.mem_map

theorem mem_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ) (g : GL (Ix r t j) k) :
    g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ KO k (Ix r t j) ∧
      (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1) := by
  revert g
  induction j with
  | zero =>
    intro g
    rw [TypeDatum.iter_zero, mem_reindex_J_iff]
    change (reGL (ixZero r t)).symm g ∈ KOne k r ↔ _
    have e0 : ((reGL (ixZero r t)).symm g).val - 1 = g.val.toBlocks₁₁ - 1 := by
      rw [reGL_symm_val]; rfl
    constructor
    · intro hg
      refine ⟨(reGL_symm_mem_KO (ixZero r t) g).1 (KOne_le_KO hg), ?_, ?_⟩
      · intro a b hab
        exfalso
        rcases a with x | ⟨i, _⟩
        · exact Nat.not_lt_zero _ hab
        · exact i.elim0
      · rw [← e0]; exact mem_KOne.1 hg
    · rintro ⟨-, -, h1⟩
      rw [mem_KOne, e0]; exact h1
  | succ j ih =>
    intro g
    rw [TypeDatum.iter_succ, mem_reindex_J_iff, TypeDatum.step_J, TypeDatum.mem_stepJ_iff, reGL_symm_mem_KO]
    have hv : ∀ x y, ((reGL (ixSucc r t j)).symm g).val x y = g.val (ixSucc r t j x) (ixSucc r t j y) := by
      intro x y; rw [reGL_symm_val]; rfl
    constructor
    · rintro ⟨hK, ⟨g', hg', e'⟩, h21⟩
      obtain ⟨-, hlow, h11⟩ := (ih g').1 hg'
      have hg'v : ∀ x y, g'.val x y = g.val (ixSucc r t j (.inl x)) (ixSucc r t j (.inl y)) := by
        intro x y; rw [e']; exact hv (.inl x) (.inl y)
      refine ⟨hK, ?_, ?_⟩
      · intro a b hab
        obtain ⟨x, rfl⟩ := (ixSucc r t j).surjective a
        obtain ⟨y, rfl⟩ := (ixSucc r t j).surjective b
        rcases x with x | s <;> rcases y with y | s'
        · rw [← hg'v]
          rw [blk_ixSucc_inl, blk_ixSucc_inl] at hab
          exact hlow x y hab
        · rw [blk_ixSucc_inr, blk_ixSucc_inl] at hab
          have := Ix.blk_le x
          omega
        · rw [← hv]; exact h21 s y
        · rw [blk_ixSucc_inr, blk_ixSucc_inr] at hab
          omega
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'; exact hg'v (.inl i) (.inl i')
        rw [← hb]; exact h11
    · rintro ⟨hK, hlow, h11⟩
      have hK' : (reGL (ixSucc r t j)).symm g ∈ KO k (Ix r t j ⊕ t) := (reGL_symm_mem_KO _ g).2 hK
      have h21 : MaxM ((reGL (ixSucc r t j)).symm g).val.toBlocks₂₁ := by
        intro s y
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inr s) (.inl y)) < 1
        rw [hv]
        apply hlow
        rw [blk_ixSucc_inr, blk_ixSucc_inl]
        exact Nat.lt_succ_of_le (Ix.blk_le y)
      refine ⟨hK, ?_, h21⟩
      obtain ⟨⟨g', hg'K, e'⟩, -⟩ := exists_diag_blocks hK' h21
      refine ⟨g', (ih g').2 ⟨hg'K, ?_, ?_⟩, e'⟩
      · intro x y hxy
        rw [e']
        show valuation k (((reGL (ixSucc r t j)).symm g).val (.inl x) (.inl y)) < 1
        rw [hv]
        apply hlow
        rwa [blk_ixSucc_inl, blk_ixSucc_inl]
      · have hb : g'.val.toBlocks₁₁ = g.val.toBlocks₁₁ := by
          ext i i'
          rw [e']
          exact hv (.inl (.inl i)) (.inl (.inl i'))
        rw [hb]; exact h11

theorem lam_iter_principal (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, IsTame (μ j)) (j : ℕ)
    (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ)
    (hd : ∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) :
    ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) := by
  revert g d hd
  induction j with
  | zero =>
    intro g d hd
    rw [Fin.prod_univ_zero]
    exact (Level.map_lam (reGL (ixZero r t)) (TypeDatum.principal k r).toLevel g).trans rfl
  | succ j ih =>
    intro g d hd
    have hmem : (reGL (ixSucc r t j)).symm (g : GL (Ix r t (j + 1)) k) ∈
        ((TypeDatum.principal k r).iter t μ hμ j).stepJ t := g.2
    have hv : ∀ x y, ((reGL (ixSucc r t j)).symm (g : GL (Ix r t (j + 1)) k)).val x y =
        (g : GL (Ix r t (j + 1)) k).val (ixSucc r t j x) (ixSucc r t j y) := by
      intro x y; rw [reGL_symm_val]; rfl
    obtain ⟨-, ⟨g', hg', e'⟩, -, -, ⟨D, -, eD⟩⟩ := ((TypeDatum.principal k r).iter t μ hμ j).mem_stepJ.1 hmem
    have hstep := ((TypeDatum.principal k r).iter t μ hμ j).step_lam_eq (μ (j + 1)) (hμ _) ⟨_, hmem⟩
      ⟨g', hg'⟩ e' D eD
    have hre := Level.map_lam (reGL (ixSucc r t j))
      (((TypeDatum.principal k r).iter t μ hμ j).step t (μ (j + 1)) (hμ _)).toLevel g
    refine hre.trans (hstep.trans ?_)
    have hD : Matrix.GeneralLinearGroup.det D = d (Fin.last j) := by
      ext
      rw [hd (Fin.last j)]
      show (D : Matrix t t k).det = _
      rw [eD]
      congr 1
    rw [Fin.prod_univ_castSucc, ih ⟨g', hg'⟩ (fun c => d c.castSucc) (fun c => by
      show ((d c.castSucc : kˣ) : k) = _
      rw [hd c.castSucc]
      congr 1
      ext s s'
      show (g : GL (Ix r t (j + 1)) k).val (.inr (c.castSucc, s)) (.inr (c.castSucc, s')) =
        g'.val (.inr (c, s)) (.inr (c, s'))
      rw [e']
      exact (hv (.inl (.inr (c, s))) (.inl (.inr (c, s')))).symm), hD]
    simp only [Fin.val_castSucc, Fin.val_last]

theorem iter_principal_spec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r t : Type} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] (μ : ℕ → kˣ →* ℂˣ) (hμ : ∀ j, GlobalTheory.SplitWeil.IsTame (μ j)) (j : ℕ), (∀ g : GL (Ix r t j) k, g ∈ ((TypeDatum.principal k r).iter t μ hμ j).J ↔ g ∈ GlobalTheory.SplitWeil.KO k (Ix r t j) ∧ (∀ a b : Ix r t j, b.blk < a.blk → valuation k (g.val a b) < 1) ∧ MaxM (g.val.toBlocks₁₁ - 1)) ∧ ∀ (g : ((TypeDatum.principal k r).iter t μ hμ j).J) (d : Fin j → kˣ), (∀ c, (d c : k) = (Ix.diagonalBlockOfMatrix (g : GL (Ix r t j) k).val c).det) → ((TypeDatum.principal k r).iter t μ hμ j).lam g = ∏ c : Fin j, μ (c.val + 1) (d c) :=
  fun μ hμ j => ⟨fun g => mem_iter_principal μ hμ j g, fun g d hd => lam_iter_principal μ hμ j g d hd⟩

end GlobalTheory.StepData
