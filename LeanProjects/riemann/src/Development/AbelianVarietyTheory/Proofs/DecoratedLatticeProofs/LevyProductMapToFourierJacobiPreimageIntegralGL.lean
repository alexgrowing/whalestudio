import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdRFJCoe
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

noncomputable section
namespace GlobalTheory.HaarFJInt

open GlobalTheory.RootEx.Radical

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def midLev (c ρ : ℕ) : n ⊕ Fin c → ℕ := Sum.elim (fun _ => 2 * ρ + 1) (fun i => 2 * (i.val + 1))

theorem uni_of_mem_N {ρ : ℕ} {u : GL (n ⊕ Fin c) k} (hu : u ∈ N k n c (ρ + 1)) :
    Uni (midLev c ρ) u.val := by
  rw [mem_N_iff] at hu
  intro r s hrs
  refine hu r s ?_
  rcases r with r | r <;> rcases s with s | s <;> simp only [midLev, lev, Sum.elim_inl, Sum.elim_inr] at hrs ⊢ <;> omega

theorem uni_colE (ρ : ℕ) (β : n → k) : Uni (midLev c ρ) (colE c (ρ + 1) β).val := by
  intro r s hrs
  rcases r with r | r <;> rcases s with s | s
  · simp [colE, upU, Matrix.one_apply]
  · simp only [midLev, Sum.elim_inl, Sum.elim_inr] at hrs
    have : s.val ≠ ρ := by omega
    simp [colE, upU, this]
  · simp [colE, upU]
  · simp [colE, upU, Matrix.one_apply]

theorem uni_inl_inl {ρ : ℕ} {M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k} (h : Uni (midLev c ρ) M) (i j : n) :
    M (Sum.inl i) (Sum.inl j) = (1 : Matrix n n k) i j := by
  rw [h _ _ (by simp [midLev])]
  simp [Matrix.one_apply]

theorem embX_mem_KO {g : GL n k} (hg : g ∈ KO k n) : embX c g ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff] at hg ⊢
  have one_int : ∀ (i j : Fin c), (1 : Matrix (Fin c) (Fin c) k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.1 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j
  · rw [← map_inv, embX_val]
    rcases i with i | i <;> rcases j with j | j
    · exact hg.2 i j
    · exact zero_mem _
    · exact zero_mem _
    · exact one_int i j

theorem colE_mem_KO (p : ℕ) {β : n → k} (hβ : ∀ i, β i ∈ 𝒪[k]) : colE c p β ∈ KO k (n ⊕ Fin c) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  have one_int : ∀ {m : Type} [DecidableEq m] (i j : m), (1 : Matrix m m k) i j ∈ 𝒪[k] := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    · exact one_mem _
    · exact zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · simp only [colE, upU, fromBlocks_apply₁₂, Matrix.of_apply]
      split_ifs
      · exact hβ i
      · exact zero_mem _
    · simp only [colE, upU, fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · exact one_int i j
  · rcases i with i | i <;> rcases j with j | j
    · exact one_int i j
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inl i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₁₂, Matrix.neg_apply, Matrix.of_apply]
      split_ifs
      · exact neg_mem (hβ i)
      · rw [neg_zero]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inl j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₁, Matrix.zero_apply]; exact zero_mem _
    · show (fromBlocks 1 (-(Matrix.of fun r (i : Fin c) => if i.val + 1 = p then β r else 0)) 0 1 :
        Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (Sum.inr i) (Sum.inr j) ∈ 𝒪[k]
      simp only [fromBlocks_apply₂₂]; exact one_int i j

theorem embX_mul_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (embX c g * w).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem mul_embX_inl {ρ : ℕ} (g : GL n k) (w : GL (n ⊕ Fin c) k) (hw : Uni (midLev c ρ) w.val) (i j : n) :
    (w * embX c g).val (Sum.inl i) (Sum.inl j) = g.val i j := by
  rw [Units.val_mul, embX_val, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [uni_inl_inl hw, Matrix.one_apply]

theorem col_eq {ρ : ℕ} (hρ : ρ < c) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1)) (β : n → k) (t : n) :
    (u * colE c (ρ + 1) β).val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = β t := by
  have h1 := uni_inl_inl (uni_of_mem_N hu)
  have h0 : u.val (Sum.inl t) (Sum.inr ⟨ρ, hρ⟩) = 0 := by
    rw [mem_N_iff] at hu
    rw [hu _ _ (by simp [lev])]
    simp
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_sum_type]
  simp [colE, upU, h1, Matrix.one_apply, h0]

theorem mem_KO_iff_prod {ρ : ℕ} (hρ : ρ < c) (g : GL n k) (u : GL (n ⊕ Fin c) k) (hu : u ∈ N k n c (ρ + 1))
    (β : n → k) :
    embX c g * u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) ↔
      g ∈ KO k n ∧ u ∈ KO k (n ⊕ Fin c) ∧ ∀ i, β i ∈ 𝒪[k] := by
  constructor
  · intro hr
    have hw : Uni (midLev c ρ) (u * colE c (ρ + 1) β).val :=
      Uni.mul (uni_of_mem_N hu) (uni_colE ρ β)
    have hwi : Uni (midLev c ρ) ((u * colE c (ρ + 1) β)⁻¹).val := Uni.inv hw
    have hr' := (GlobalTheory.SplitFlip.mem_KO_iff _).1 hr
    have hg : g ∈ KO k n := by
      rw [GlobalTheory.SplitFlip.mem_KO_iff]
      refine ⟨fun i j => ?_, fun i j => ?_⟩
      · have := hr'.1 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, embX_mul_inl g _ hw] at this
      · have := hr'.2 (Sum.inl i) (Sum.inl j)
        rwa [mul_assoc, _root_.mul_inv_rev, ← map_inv, mul_embX_inl g⁻¹ _ hwi] at this
    have hwK : u * colE c (ρ + 1) β ∈ KO k (n ⊕ Fin c) := by
      have := mul_mem (inv_mem (embX_mem_KO (c := c) hg)) hr
      rwa [mul_assoc, inv_mul_cancel_left] at this
    have hβ : ∀ i, β i ∈ 𝒪[k] := fun i => by
      have := ((GlobalTheory.SplitFlip.mem_KO_iff _).1 hwK).1 (Sum.inl i) (Sum.inr ⟨ρ, hρ⟩)
      rwa [col_eq hρ u hu β i] at this
    refine ⟨hg, ?_, hβ⟩
    have := mul_mem hwK (inv_mem (colE_mem_KO (c := c) (ρ + 1) hβ))
    rwa [mul_inv_cancel_right] at this
  · rintro ⟨hg, huK, hβ⟩
    exact mul_mem (mul_mem (embX_mem_KO hg) huK) (colE_mem_KO _ hβ)

end GlobalTheory.HaarFJInt

open GlobalTheory.HaarFJInt in
theorem GlobalTheory.HaarFJInt.prodRFJ_preimage_KO : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c ρ : ℕ), ρ < c → prodRFJ (k := k) (n := n) (c := c) ρ ⁻¹' {x | (x : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = ((KO k n : Set (GL n k)) ×ˢ {u : N k n c (ρ + 1) | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)}) ×ˢ {β : n → k | ∀ i, β i ∈ 𝒪[k]} := by
  intro k _ _ _ _ n _ _ c ρ hρ
  ext ⟨⟨g, u⟩, β⟩
  simp only [Set.mem_preimage, Set.mem_setOf_eq, prodRFJ_coe, Set.mem_prod, SetLike.mem_coe]
  rw [mem_KO_iff_prod hρ g u u.2 β, and_assoc]
end
