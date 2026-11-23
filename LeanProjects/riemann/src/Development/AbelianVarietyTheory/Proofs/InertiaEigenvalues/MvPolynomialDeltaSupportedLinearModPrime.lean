import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem polyDelta_supported_linear_mod (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (D : Delta l A) (i : ℕ) :
    ∀ s ∈ MvPolynomial.supported A (Set.Iic i), (polyDelta D).δ s ∈ MvPolynomial.supported A (Set.Iic (i + 1)) ∧
      ∃ a ∈ MvPolynomial.supported A (Set.Iic i), ∃ b ∈ MvPolynomial.supported A (Set.Iic i),
        (polyDelta D).δ s - (a * MvPolynomial.X (i + 1) + b) ∈ Ideal.span {(l : MvPolynomial ℕ A)} := by
  intro s hs
  have hX : ∀ (U : Set ℕ) (j : ℕ), j ∈ U → (MvPolynomial.X j : MvPolynomial ℕ A) ∈ MvPolynomial.supported A U :=
    fun U j hj => by
      rw [MvPolynomial.supported_eq_adjoin_X]; exact Algebra.subset_adjoin ⟨j, hj, rfl⟩
  have hC : ∀ (U : Subalgebra A (MvPolynomial ℕ A)) (a : A), MvPolynomial.C a ∈ U :=
    fun U a => U.algebraMap_mem a
  set S := MvPolynomial.supported A (Set.Iic i) with hS
  set T := MvPolynomial.supported A (Set.Iic (i + 1)) with hT
  have hST : S ≤ T := MvPolynomial.supported_mono (Set.Iic_subset_Iic.2 (Nat.le_succ i))
  have hcc : ∀ x y, x ∈ S → y ∈ S → cc l x y ∈ S := by
    intro x y hx hy
    unfold cc
    refine Subalgebra.sum_mem _ fun k _ => ?_
    refine Subalgebra.mul_mem _ (Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (Subalgebra.pow_mem _ hx _))
      (Subalgebra.pow_mem _ hy _)
  have hS' : S = Algebra.adjoin A (MvPolynomial.X '' Set.Iic i) := MvPolynomial.supported_eq_adjoin_X _
  rw [hS'] at hs
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, hj, rfl⟩ := hx
    have hj' : j ≤ i := Set.mem_Iic.1 hj
    rw [polyDelta_X]
    refine ⟨hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
    rcases Nat.lt_or_ge j i with h | h
    · refine ⟨0, Subalgebra.zero_mem _, MvPolynomial.X (j + 1), hX _ _ (Set.mem_Iic.2 (by omega)), ?_⟩
      simp
    · have : j = i := le_antisymm hj' h
      subst this
      refine ⟨1, Subalgebra.one_mem _, 0, Subalgebra.zero_mem _, ?_⟩
      simp
  | algebraMap a =>
    rw [MvPolynomial.algebraMap_eq, polyDelta_C]
    refine ⟨hC _ _, 0, Subalgebra.zero_mem _, MvPolynomial.C (D.δ a), hC _ _, ?_⟩
    simp
  | add x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x + y) = (polyDelta D).δ x + (polyDelta D).δ y - cc l x y := (polyDelta D).δ_add x y
    rw [hd]
    refine ⟨T.sub_mem (T.add_mem hx1 hy1) (hST (hcc x y hx hy)), a1 + a2, S.add_mem ha1 ha2,
      b1 + b2 - cc l x y, S.sub_mem (S.add_mem hb1 hb2) (hcc x y hx hy), ?_⟩
    have := Ideal.add_mem _ hx2 hy2
    convert this using 1
    ring
  | mul x y hx hy ihx ihy =>
    rw [← hS'] at hx hy
    obtain ⟨hx1, a1, ha1, b1, hb1, hx2⟩ := ihx
    obtain ⟨hy1, a2, ha2, b2, hb2, hy2⟩ := ihy
    have hd : (polyDelta D).δ (x * y) = x ^ l * (polyDelta D).δ y + y ^ l * (polyDelta D).δ x +
        (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y := (polyDelta D).δ_mul x y
    rw [hd]
    refine ⟨T.add_mem (T.add_mem (T.mul_mem (T.pow_mem (hST hx) _) hy1) (T.mul_mem (T.pow_mem (hST hy) _) hx1))
        (T.mul_mem (T.mul_mem (T.natCast_mem _) hx1) hy1),
      x ^ l * a2 + y ^ l * a1, S.add_mem (S.mul_mem (S.pow_mem hx _) ha2) (S.mul_mem (S.pow_mem hy _) ha1),
      x ^ l * b2 + y ^ l * b1, S.add_mem (S.mul_mem (S.pow_mem hx _) hb2) (S.mul_mem (S.pow_mem hy _) hb1), ?_⟩
    have h3 : (l : MvPolynomial ℕ A) * (polyDelta D).δ x * (polyDelta D).δ y ∈
        Ideal.span {(l : MvPolynomial ℕ A)} :=
      Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    have := Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ (x ^ l) hy2) (Ideal.mul_mem_left _ (y ^ l) hx2)) h3
    convert this using 1
    ring

end GlobalTheory.BSP
