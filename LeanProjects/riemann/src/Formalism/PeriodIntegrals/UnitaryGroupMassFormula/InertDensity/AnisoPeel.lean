import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.FinrankInfKerAddOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ExistsTraceNeZero
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.ValMain

open Finset Module

noncomputable section

namespace DensInertW

open DensInertW.Sub

section
variable {L : Type} [Field L]

def anP {n m : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L) (W : Submodule L (Fin n → L))
    (B : Matrix (Fin m) (Fin m) L) (X : Fin m → Fin n → L) : Prop :=
  (∀ i, X i ∈ W) ∧ LinearIndependent L X ∧ ∀ i j, hf q M (X i) (X j) = B i j

open Classical in
theorem an_cntT_eq [Fintype L] {n m q : ℕ} (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) (B : Matrix (Fin m) (Fin m) L) :
    cntT q M W B = (Finset.univ.filter (anP q M W B)).card := by
  unfold cntT
  rw [← Set.ncard_coe_finset]
  congr 1
  ext X
  simp [anP]

open Classical in
theorem an_fiber [Fintype L] {n m q : ℕ} {M : Matrix (Fin n) (Fin n) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : IsHerm q M) (W : Submodule L (Fin n → L)) (b : L) (w : Fin m → L) (x : Fin n → L)
    (hxW : x ∈ W) (hxx : hf q M x x = b) (hb : b ≠ 0) :
    (Finset.univ.filter (fun X : Fin (m + 1) → Fin n → L =>
        anP q M W (Matrix.diagonal (Fin.cons b w : Fin (m + 1) → L)) X ∧ X 0 = x)).card =
      (Finset.univ.filter (anP q M (W ⊓ LinearMap.ker (hfL q M x)) (Matrix.diagonal w))).card := by
  have hq := q_ne_zero_of_inv hinv
  symm
  refine Finset.card_nbij' (fun U : Fin m → Fin n → L => (Fin.cons x U : Fin (m + 1) → Fin n → L))
    (fun X : Fin (m + 1) → Fin n → L => (fun i : Fin m => X i.succ)) ?_ ?_ ?_ ?_
  · intro U hU
    have hU' := (Finset.mem_filter.1 (Finset.mem_coe.1 hU)).2
    obtain ⟨hUW, hUi, hUg⟩ := hU'
    have hUx : ∀ i, hf q M (U i) x = 0 := fun i => (hUW i).2
    have hxU : ∀ i, hf q M x (U i) = 0 := fun i => by
      rw [hf_symm hadd hinv hM, hUx i, zero_pow hq]
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨?_, ?_, ?_⟩, rfl⟩
    · intro i
      induction i using Fin.cases with
      | zero => exact hxW
      | succ i => exact (hUW i).1
    · rw [linearIndependent_finCons]
      refine ⟨hUi, fun hmem => ?_⟩
      have hle : Submodule.span L (Set.range U) ≤ W ⊓ LinearMap.ker (hfL q M x) := by
        rw [Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact hUW j
      have := (hle hmem).2
      change hf q M x x = 0 at this
      exact hb (hxx ▸ this)
    · intro i j
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => simpa [Matrix.diagonal_apply] using hxx
        | succ j =>
          simp only [Fin.cons_zero, Fin.cons_succ, Matrix.diagonal_apply,
            (Fin.succ_ne_zero j).symm, if_false]
          exact hxU j
      | succ i =>
        induction j using Fin.cases with
        | zero =>
          simp only [Fin.cons_zero, Fin.cons_succ, Matrix.diagonal_apply, Fin.succ_ne_zero,
            if_false]
          exact hUx i
        | succ j =>
          simp only [Fin.cons_succ, Matrix.diagonal_apply, Fin.succ_inj]
          rw [hUg i j, Matrix.diagonal_apply]
  · intro X hX
    have hX' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).2
    obtain ⟨⟨hXW, hXi, hXg⟩, hX0⟩ := hX'
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun i => ⟨hXW _, ?_⟩, hXi.comp _ (Fin.succ_injective _), ?_⟩
    · change hf q M (X i.succ) x = 0
      rw [← hX0, hXg, Matrix.diagonal_apply, if_neg (Fin.succ_ne_zero i)]
    · intro i j
      rw [hXg, Matrix.diagonal_apply, Matrix.diagonal_apply]
      simp only [Fin.succ_inj, Fin.cons_succ]
  · intro U _
    rfl
  · intro X hX
    have hX' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).2
    rw [← hX'.2]
    exact Fin.cons_self_tail X

end

theorem anisoPeel_of_valCount (hv : ValCount) : AnisoPeel := by
  intro K L _ _ _ _ _ h2 n M W hM hW m b w k hbf hb0 hk
  classical
  have hadd : ∀ a b : L, (a + b) ^ Fintype.card K = a ^ Fintype.card K + b ^ Fintype.card K :=
    fun a b => frob_add (K := K) a b
  have hinv : ∀ a : L, (a ^ Fintype.card K) ^ Fintype.card K = a := frob_frob h2
  rw [an_cntT_eq]
  rw [Finset.card_eq_sum_card_fiberwise (f := fun X : Fin (m + 1) → Fin n → L => X 0)
    (t := Finset.univ.filter (fun x : Fin n → L => x ∈ W ∧ hf (Fintype.card K) M x x = b))]
  · push_cast
    have hterm : ∀ x ∈ Finset.univ.filter (fun x : Fin n → L =>
        x ∈ W ∧ hf (Fintype.card K) M x x = b),
        (((Finset.univ.filter (anP (Fintype.card K) M W
          (Matrix.diagonal (Fin.cons b w : Fin (m + 1) → L)))).filter
          (fun X : Fin (m + 1) → Fin n → L => X 0 = x)).card : ℤ) = k := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      obtain ⟨hxW, hxx⟩ := hx
      have hee : hf (Fintype.card K) M x x ≠ 0 := hxx ▸ hb0
      rw [Finset.filter_filter, an_fiber hadd hinv hM W b w x hxW hxx hb0]
      have hk' := hk _ (nondeg_perp_aniso hadd W hW x hxW hee) (finrank_perp_aniso W x hxW hee)
      rw [an_cntT_eq] at hk'
      exact hk'
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.filter (fun x : Fin n → L =>
        x ∈ W ∧ hf (Fintype.card K) M x x = b)).card : ℤ) =
        valN (Fintype.card K) (Module.finrank L W) := by
      have h0 := hv K L h2 n M W hM hW b hbf
      rw [if_neg hb0] at h0
      rw [← h0, ← Set.ncard_coe_finset]
      congr 2
      ext v
      simp
    rw [hcard]
  · intro X hX
    have hX' := (Finset.mem_filter.1 (Finset.mem_coe.1 hX)).2
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hX'.1 0, ?_⟩
    rw [hX'.2.2 0 0, Matrix.diagonal_apply_eq, Fin.cons_zero]

theorem anisotropic_valuation_peel : AnisoPeel := anisoPeel_of_valCount valuation_count

end DensInertW
