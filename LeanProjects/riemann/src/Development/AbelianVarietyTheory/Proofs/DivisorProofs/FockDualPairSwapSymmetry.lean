import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

noncomputable section
namespace GlobalTheory.FockSwap

variable {p q r s : ℕ}

theorem linePos_swap (l : Ln p q r s) : linePos (l.swap : Ln r s p q) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> rfl

theorem rename_lowB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (lowB l P) = lowB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold lowB
  rw [linePos_swap]
  split_ifs
  · exact (pderiv_rename Prod.swap_injective l P).symm
  · simp

theorem rename_raiB (l : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (raiB l P) = raiB (l.swap : Ln r s p q) (rename Prod.swap P) := by
  unfold raiB
  rw [linePos_swap]
  split_ifs
  · simp
  · simp only [LinearMap.neg_apply, map_neg, neg_inj]
    exact (pderiv_rename Prod.swap_injective l P).symm

theorem rename_omE (l l' : Ln p q r s) (P : Pol p q r s) :
    rename Prod.swap (omE l l' P) =
      omE (l.swap : Ln r s p q) l'.swap (rename Prod.swap P) := by
  unfold omE
  simp only [LinearMap.add_apply, map_add, Module.End.mul_apply, rename_raiB, rename_lowB,
    Prod.swap_inj]
  congr 1
  split_ifs <;> simp

theorem rename_omAct (M : Matrix (Ln p q r s) (Ln p q r s) ℂ) (P : Pol p q r s) :
    rename Prod.swap (omAct p q r s M P) =
      omAct r s p q (M.submatrix Prod.swap Prod.swap) (rename Prod.swap P) := by
  simp only [omAct_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    rename_omE]
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l => ?_
  refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun l' => ?_
  simp

theorem rename_fockAct1 (Z : Mat p q) (P : Pol p q r s) :
    rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_fockAct2 (Z : Mat r s) (P : Pol p q r s) :
    rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P) := by
  simp only [fockAct1, fockAct2, LinearMap.comp_apply]
  rw [rename_omAct]
  congr 2
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMapBilinear_apply_apply, mul_comm]

theorem rename_minusPart {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : rename e (minusPart A P) = minusPart B (rename e P) := by
  unfold minusPart
  have := (renameEquiv ℂ e).toAddEquiv.map_finsum
    (fun d : ℕ => homogeneousComponent d (A (homogeneousComponent (d + 2) P)))
  refine this.trans (finsum_congr fun d => ?_)
  show rename e _ = _
  rw [rename_homogeneousComponent, h, rename_homogeneousComponent]

theorem minusPart_eq_zero_iff {σ τ : Type} (e : σ ≃ τ) (A : Module.End ℂ (MvPolynomial σ ℂ))
    (B : Module.End ℂ (MvPolynomial τ ℂ)) (h : ∀ P, rename e (A P) = B (rename e P))
    (P : MvPolynomial σ ℂ) : minusPart A P = 0 ↔ minusPart B (rename e P) = 0 := by
  rw [← rename_minusPart e A B h, map_eq_zero_iff _ (rename_injective _ e.injective)]

theorem swap_symmetry : ∀ (p q r s : ℕ), (∀ (Z : Mat p q) (P : Pol p q r s), rename Prod.swap (fockAct1 p q r s Z P) = fockAct2 r s p q Z (rename Prod.swap P)) ∧ (∀ (Z : Mat r s) (P : Pol p q r s), rename Prod.swap (fockAct2 p q r s Z P) = fockAct1 r s p q Z (rename Prod.swap P)) ∧ (∀ P : Pol p q r s, (P ∈ harm1 p q r s ↔ rename Prod.swap P ∈ harm2 r s p q) ∧ (P ∈ harm2 p q r s ↔ rename Prod.swap P ∈ harm1 r s p q)) := by
  intro p q r s
  refine ⟨rename_fockAct1, rename_fockAct2, fun P => ⟨?_, ?_⟩⟩
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct2 Z) P
  · exact forall₂_congr fun Z _ =>
      minusPart_eq_zero_iff (Equiv.prodComm _ _) _ _ (rename_fockAct1 Z) P

end GlobalTheory.FockSwap
