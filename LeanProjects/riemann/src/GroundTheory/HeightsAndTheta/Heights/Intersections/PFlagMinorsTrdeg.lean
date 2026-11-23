import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagMinorsTrdeg
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotIdentity
import GroundTheory.HeightsAndTheta.Heights.Intersections.StFlagPivotAlgIndep
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

theorem card_pivotCols_ge {n : ℕ} (a : Fin (n - 1)) :
    Fintype.card {b : Fin n // (a : ℕ) ≤ b} = n - a := by
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun b : Fin n => (a : ℕ) ≤ b) = Finset.Ici (Fin.castLE (Nat.sub_le n 1) a) := by
    ext b; simp [Fin.le_def]
  rw [this, Fin.card_Ici]
  simp

theorem card_pivotIndex (n : ℕ) :
    Fintype.card (Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}) = flagDim n + (n - 1) := by
  rw [Fintype.card_sigma]
  simp_rw [card_pivotCols_ge]
  rw [Fin.sum_univ_eq_sum_range (fun i => n - i) (n - 1)]
  rcases n with _ | m
  · simp [flagDim]
  · simp only [Nat.add_sub_cancel, flagDim]
    have hr : ∑ i ∈ Finset.range m, (m + 1 - i) = ∑ i ∈ Finset.range m, (i + 2) := by
      rw [← Finset.sum_range_reflect (fun i => i + 2) m]
      exact Finset.sum_congr rfl fun i hi => by simp at hi; omega
    rw [hr, Finset.sum_add_distrib]
    have h2 := Finset.sum_range_id_mul_two m
    have h3 : (m + 1) * m = (∑ i ∈ Finset.range m, i) * 2 + 2 * m := by
      rw [h2]; rcases m with _ | k
      · simp
      · simp only [Nat.add_sub_cancel]; ring
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    rw [h3]
    omega

theorem det_mem_subring {R : Type} [CommRing R] {m : Type} [Fintype m] [DecidableEq m] (S : Subring R)
    (M : Matrix m m R) (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply]
  refine S.sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (S.prod_mem fun i _ => h _ _) _

section

variable (F : Type) [Field F] (n : ℕ)

def flagMinorAlg : Subalgebra F (MvPolynomial (Fin n × Fin n) F) :=
  Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat F n) q.1 q.2)

abbrev PivotIdx := Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}

theorem pivotMinor_mem_flagMinorAlg (q : PivotIdx n) : pivotMinor (genMat F n) q.1 q.2.1 ∈ flagMinorAlg F n := by
  rw [pivotMinor_eq_flagMinor _ q.1 q.2.1 q.2.2]
  exact Algebra.subset_adjoin ⟨⟨q.1, _⟩, rfl⟩

def pivotElt (q : PivotIdx n) : flagMinorAlg F n := ⟨_, pivotMinor_mem_flagMinorAlg F n q⟩

def pivotAlg : Subalgebra F (flagMinorAlg F n) := Algebra.adjoin F (Set.range (pivotElt F n))

def pivotAlgP : Subalgebra F (MvPolynomial (Fin n × Fin n) F) :=
  Algebra.adjoin F (Set.range fun q : PivotIdx n => pivotMinor (genMat F n) q.1 q.2.1)

theorem pivotAlgP_eq_map : pivotAlgP F n = (pivotAlg F n).map (flagMinorAlg F n).val := by
  rw [pivotAlg, AlgHom.map_adjoin, ← Set.range_comp]
  rfl

theorem leadMinor_mem_pivotAlgP (a : Fin (n - 1)) : leadMinor (genMat F n) a ∈ pivotAlgP F n :=
  Algebra.subset_adjoin ⟨⟨a, ⟨Fin.castLE (Nat.sub_le n 1) a, le_rfl⟩⟩, rfl⟩

theorem pivotMatrix_mem_pivotAlgP (j : Fin (n - 1)) (r : Fin (j + 1)) (b : Fin n) :
    pivotMatrix (genMat F n) (Fin.castLE (by have := j.2; omega) r) b ∈ pivotAlgP F n := by
  have hr : (r : ℕ) < n - 1 := by have := j.2; have := r.2; omega
  simp only [pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos hr]
  by_cases h : (r : ℕ) ≤ b
  · exact Algebra.subset_adjoin ⟨⟨⟨r, hr⟩, ⟨b, h⟩⟩, rfl⟩
  · rw [pivotMinor_eq_zero _ ⟨r, hr⟩ b (by simp only; omega)]
    exact zero_mem _

theorem exists_of_mem_pivotAlgP {y : MvPolynomial (Fin n × Fin n) F} (hy : y ∈ pivotAlgP F n) :
    ∃ z : pivotAlg F n, ((z : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F) = y := by
  rw [pivotAlgP_eq_map] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact ⟨⟨z, hz⟩, rfl⟩

theorem isAlgebraic_flagMinor (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) (q : Σ j, PluckerBlocks n n j) :
    IsAlgebraic (pivotAlg F n)
      (⟨flagMinor (genMat F n) q.1 q.2, Algebra.subset_adjoin ⟨q, rfl⟩⟩ : flagMinorAlg F n) := by
  obtain ⟨j, S⟩ := q
  obtain ⟨c, hc⟩ := exists_of_mem_pivotAlgP F n (y := ∏ a ∈ Finset.Iic j, leadMinor (genMat F n) a)
    (Subalgebra.prod_mem _ fun a _ => leadMinor_mem_pivotAlgP F n a)
  obtain ⟨d, hd⟩ := exists_of_mem_pivotAlgP F n
    (y := leadMinor (genMat F n) j * flagMinor (pivotMatrix (genMat F n)) j S)
    (Subalgebra.mul_mem _ (leadMinor_mem_pivotAlgP F n j)
      (det_mem_subring (pivotAlgP F n).toSubring _ fun r s => pivotMatrix_mem_pivotAlgP F n j r _))
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact (Finset.prod_ne_zero_iff.mpr fun a _ => hne a) hc.symm
  have h1 : c • (⟨flagMinor (genMat F n) j S, Algebra.subset_adjoin ⟨⟨j, S⟩, rfl⟩⟩ : flagMinorAlg F n) =
      algebraMap (pivotAlg F n) (flagMinorAlg F n) d := by
    apply Subtype.val_injective
    change ((c : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F) * flagMinor (genMat F n) j S =
      ((d : flagMinorAlg F n) : MvPolynomial (Fin n × Fin n) F)
    rw [hc, hd, ← h₁ (MvPolynomial (Fin n × Fin n) F) n (genMat F n) j S, mul_comm]
  exact IsAlgebraic.of_smul (mem_nonZeroDivisors_of_ne_zero hc0) (h1 ▸ isAlgebraic_algebraMap d)

theorem isAlgebraic_pivotAlg (h₁ : FlagPivotIdentity.Statement)
    (hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0) :
    Algebra.IsAlgebraic (pivotAlg F n) (flagMinorAlg F n) := by
  constructor
  rintro ⟨y, hy⟩
  induction hy using Algebra.adjoin_induction with
  | mem y hy' =>
    obtain ⟨q, rfl⟩ := hy'
    exact isAlgebraic_flagMinor F n h₁ hne q
  | algebraMap r => exact isAlgebraic_algebraMap (algebraMap F (pivotAlg F n) r)
  | add y z hy hz ihy ihz =>
    have e : (⟨y + z, add_mem hy hz⟩ : flagMinorAlg F n) = ⟨y, hy⟩ + ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact ihy.add ihz
  | mul y z hy hz ihy ihz =>
    have e : (⟨y * z, mul_mem hy hz⟩ : flagMinorAlg F n) = ⟨y, hy⟩ * ⟨z, hz⟩ := Subtype.ext rfl
    rw [e]
    exact ihy.mul ihz

end

theorem FlagMinorsTrdeg.proof (h₁ : FlagPivotIdentity.Statement) (h₂ : FlagPivotAlgIndep.Statement) :
    FlagMinorsTrdeg.Statement := by
  intro F _ n
  have hx : AlgebraicIndependent F (pivotElt F n) :=
    AlgebraicIndependent.of_comp (flagMinorAlg F n).val (h₂ F n)
  have hne : ∀ a : Fin (n - 1), leadMinor (genMat F n) a ≠ 0 := fun a h =>
    hx.ne_zero ⟨a, ⟨Fin.castLE (Nat.sub_le n 1) a, le_rfl⟩⟩ (Subtype.ext h)
  have tb := hx.isTranscendenceBasis_iff_isAlgebraic.mpr (isAlgebraic_pivotAlg F n h₁ hne)
  have e := tb.cardinalMk_eq_trdeg
  rw [Cardinal.mk_fintype, card_pivotIndex] at e
  exact e.symm

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
