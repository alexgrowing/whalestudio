import Mathlib
import ReciprocityTheory.DualLattices.FischerSelfNeZero

noncomputable section

open MvPolynomial

namespace GlobalTheory.FockIsotypic

variable {σ : Type} [Fintype σ]

def flat (σ : Type) [Fintype σ] : σ ≃ Fin (Fintype.card σ) × Unit :=
  (Fintype.equivFin σ).trans (Equiv.prodPUnit _).symm

def fis (P Q : MvPolynomial σ ℂ) : ℂ :=
  ReciprocityTheory.PGsh.fischer (rename (flat σ) P) (rename (flat σ) Q)

theorem fis_conj (P Q : MvPolynomial σ ℂ) : starRingEnd ℂ (fis P Q) = fis Q P := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  set Q' := rename (flat σ) Q
  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' Q' (P'.support ∪ Q'.support) Finset.subset_union_left,
    ReciprocityTheory.PGsh.fischer_eq_sum Q' P' (P'.support ∪ Q'.support) Finset.subset_union_right, map_sum]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [ReciprocityTheory.PGsh.fw, map_mul, Complex.conj_conj, map_natCast]
  ring

theorem fis_self_re_nonneg (P : MvPolynomial σ ℂ) : 0 ≤ (fis P P).re := by
  classical
  unfold fis
  set P' := rename (flat σ) P
  rw [ReciprocityTheory.PGsh.fischer_eq_sum P' P' P'.support subset_rfl, Complex.re_sum]
  refine Finset.sum_nonneg fun A _ => ?_
  rw [Complex.mul_conj, ReciprocityTheory.PGsh.fw, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)

theorem fis_self_ne_zero {P : MvPolynomial σ ℂ} (hP : P ≠ 0) : fis P P ≠ 0 :=
  ReciprocityTheory.PGsh.fischer_self_ne_zero _ fun h =>
    hP (rename_injective _ (flat σ).injective (h.trans (map_zero _).symm))

theorem fis_add_right (P Q Q' : MvPolynomial σ ℂ) : fis P (Q + Q') = fis P Q + fis P Q' := by
  unfold fis
  rw [map_add, ReciprocityTheory.PGsh.fischer_add_right]

theorem fis_smul_right (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis P (c • Q) = starRingEnd ℂ c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_right]

theorem fis_add_left (P P' Q : MvPolynomial σ ℂ) : fis (P + P') Q = fis P Q + fis P' Q := by
  unfold fis
  rw [map_add, ReciprocityTheory.PGsh.fischer_add_left]

theorem fis_smul_left (c : ℂ) (P Q : MvPolynomial σ ℂ) : fis (c • P) Q = c * fis P Q := by
  unfold fis
  rw [map_smul, ReciprocityTheory.PGsh.fischer_smul_left]

@[reducible] def fisCore (S : Submodule ℂ (MvPolynomial σ ℂ)) : InnerProductSpace.Core ℂ S where
  inner x y := fis y.1 x.1
  conj_inner_symm x y := fis_conj _ _
  re_inner_nonneg x := fis_self_re_nonneg _
  add_left x y z := fis_add_right _ _ _
  smul_left x y r := fis_smul_right _ _ _
  definite x hx := by
    by_contra h
    exact fis_self_ne_zero (fun h' => h (Subtype.ext h')) hx

end GlobalTheory.FockIsotypic

end
