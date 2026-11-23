import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpZeroMemLev
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLevelIffSymmetricPositionEntryPattern
open ValuativeRel Matrix
open scoped Classical

noncomputable section
namespace GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def scal (ϖ : kˣ) : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → k := Sum.elim 1 fun i => (ϖ : k) ^ (i.val + 1)

def back : XIx (Fin κ) t 0 ⊕ Fin (s + 1) → Fin κ ⊕ Fin (s + 1) :=
  fun r => (ixZero (Fin κ ⊕ Fin (s + 1)) t).symm ((stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm r)

theorem back_eps (i : Fin κ) : back (s := s) t (.inl (.inl (.inl i))) = .inl i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inl (.inl (.inl i))) = .inl (.inl i) from
    (Equiv.symm_apply_eq _).2 rfl]
  exact (Equiv.symm_apply_eq _).2 rfl

theorem levelZeroOldIndexOfNew_inr (i : Fin (s + 1)) : back (κ := κ) t (.inr i) = .inr i := by
  unfold back
  rw [show (stdOrd (Fin κ) t 0 (s + 1) (Nat.zero_add _)).symm (.inr i) = .inl (.inr i) from
    (Equiv.symm_apply_eq _).2 (standardOrderExtendedBasis_apply_low_block (Fin κ) t (l := s + 1) 0 (s + 1) (Nat.zero_add _) i).symm]
  exact (Equiv.symm_apply_eq _).2 rfl

theorem scal_ne_zero (ϖ : kˣ) (r : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) : scal t ϖ r ≠ 0 := by
  rcases r with r | r <;> simp [scal]

theorem bas_val : ((S.T t).bas 0 (s + 1) (Nat.zero_add _)).val = diagonal (scal t S.ϖ) := by
  show (embA _ (SplitFlip.diagGL fun i : Fin (s + 1) => S.ϖ ^ (i.val + 1))).val = _
  simp only [embA, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk, SplitFlip.diagGL_val]
  rw [← diagonal_one, fromBlocks_diagonal]
  congr 1

theorem bas_inv_val : (((S.T t).bas 0 (s + 1) (Nat.zero_add _))⁻¹).val = diagonal fun r => (scal t S.ϖ r)⁻¹ := by
  refine Units.inv_eq_of_mul_eq_one_right ?_
  rw [bas_val, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext r; exact mul_inv_cancel₀ (scal_ne_zero t S.ϖ r)

theorem upZero_entry (x : GL (Fin κ ⊕ Fin (s + 1)) k) (r c : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) :
    (upZero S t x).val r c = scal t S.ϖ r * x.val (back t r) (back t c) * (scal t S.ϖ c)⁻¹ := by
  rw [upZero_apply, Units.val_mul, Units.val_mul, bas_val, bas_inv_val, mul_diagonal, diagonal_mul, reGL_val, reGL_val]
  rfl

theorem xZero_symm (i : Fin κ) : (xZero (Fin κ) t).symm (.inl (.inl i)) = i := (Equiv.symm_apply_eq _).2 rfl

theorem upZero_mem_N {n : GL (Fin κ ⊕ Fin (s + 1)) k} (hn : n ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    upZero S t n ∈ N k (XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) := by
  rw [Model.mem_N_iff] at hn ⊢
  intro r c h
  rw [upZero_entry]
  rcases r with ((r | r) | ⟨r, _⟩) | r
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, back_eps, hn _ _ (by simp [lev])]
      by_cases e : r = c
      · subst e; simp [scal]
      · simp [scal, Matrix.one_apply, e]
    · exact c.elim0
    · exact c.elim0
    · rw [back_eps, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      simp [Matrix.one_apply]
  · exact r.elim0
  · exact r.elim0
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      simp [Matrix.one_apply]
    · exact c.elim0
    · exact c.elim0
    · rw [levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr, hn _ _ (by simpa [lev] using h)]
      by_cases e : r = c
      · subst e; simp [scal, Matrix.one_apply]
      · simp [Matrix.one_apply, e]

theorem simpleSum_upZero (n : GL (Fin κ ⊕ Fin (s + 1)) k) :
    simpleSum (upZero S t n) = ((S.ϖ⁻¹ : kˣ) : k) * simpleSum n := by
  have hϖ : (S.ϖ : k) ≠ 0 := S.ϖ.ne_zero
  unfold simpleSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [upZero_entry, levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
    simp only [scal, Sum.elim_inr, h, Units.val_inv_eq_inv_val]
    field_simp
    ring
  · simp

theorem superSum_one : superSum Fin.val (1 : Matrix (Fin κ) (Fin κ) k) = 0 := by
  unfold superSum
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
  split_ifs with h
  · have : i ≠ j := by rintro rfl; omega
    simp [Matrix.one_apply, this]
  · rfl

theorem lam_eq (n : S.P.J) (hn : n.1 ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (simpleSum (upZero S t n.1)) : ℂ) := by
  rw [S.sym.2 n, simpleSum_upZero]
  have h11 : (n : GL (Fin κ ⊕ Fin (s + 1)) k).val.toBlocks₁₁ = 1 := by
    rw [Model.mem_N_iff] at hn
    ext i j
    simpa [toBlocks₁₁, Matrix.one_apply] using hn (.inl i) (.inl j) (by simp [lev])
  rw [h11, superSum_one]
  simp

theorem upZero_embX (γ : GL (Fin κ) k) :
    upZero S t (embX (s + 1) γ) = embX (s + 1) (reGL (xZero (Fin κ) t) γ) := by
  ext r c
  rw [upZero_entry]
  rcases r with ((r | r) | ⟨r, _⟩) | r
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [back_eps, back_eps]
      simp [embX, scal, reGL_val, xZero_symm]
    · exact c.elim0
    · exact c.elim0
    · rw [back_eps, levelZeroOldIndexOfNew_inr]
      simp [embX]
  · exact r.elim0
  · exact r.elim0
  · rcases c with ((c | c) | ⟨c, _⟩) | c
    · rw [levelZeroOldIndexOfNew_inr, back_eps]
      simp [embX]
    · exact c.elim0
    · exact c.elim0
    · rw [levelZeroOldIndexOfNew_inr, levelZeroOldIndexOfNew_inr]
      by_cases e : r = c
      · subst e; simp [embX, scal, Matrix.one_apply]
      · simp [embX, Matrix.one_apply, e]

theorem upZero_N_embX : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], (∀ n : S.P.J, n.1 ∈ GlobalTheory.RootEx.N k (Fin κ) (s + 1) (S.ρ + 1) → GlobalTheory.LevZeroGen.upZero S t n.1 ∈ GlobalTheory.RootEx.N k (GlobalTheory.StepData.XIx (Fin κ) t 0) (s + 1) (S.ρ + 1) ∧ ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (GlobalTheory.RootEx.simpleSum (GlobalTheory.LevZeroGen.upZero S t n.1)) : ℂ)) ∧ ∀ γ : GL (Fin κ) k, GlobalTheory.LevZeroGen.upZero S t (GlobalTheory.RootEx.embX (s + 1) γ) = GlobalTheory.RootEx.embX (s + 1) (GlobalTheory.StepData.reGL (GlobalTheory.LevZeroGen.xZero (Fin κ) t) γ) := by
  intro k _ _ _ _ s κ S t _ _
  exact ⟨fun n hn => ⟨upZero_mem_N S t hn, lam_eq S t n hn⟩, upZero_embX S t⟩

end GlobalTheory.LevZeroUp
