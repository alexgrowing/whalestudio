import Formalism.LocalToGlobal.ProjectiveLattices.LocalIntegralPolynomials.LocStructSt
import ReciprocityTheory.SemistableReduction.AlgAll

noncomputable section

namespace Formalism.L2.Pj.LocAlg

open ReciprocityTheory.ChartRestriction.G.T0 MvPolynomial

variable {Ω : Type} [Field Ω] {D N : ℕ}

def yv (jc : Fin (N + 1)) (x : Fin N → Ω) : Fin (N + 1) → Ω :=
  Fin.insertNth (α := fun _ => Ω) jc 1 x

theorem yv_self (jc : Fin (N + 1)) (x : Fin N → Ω) : yv jc x jc = 1 := by
  unfold yv
  exact Fin.insertNth_apply_same (α := fun _ => Ω) jc 1 x

theorem yv_succAbove (jc : Fin (N + 1)) (x : Fin N → Ω) (k : Fin N) : yv jc x (jc.succAbove k) = x k := by
  unfold yv
  exact Fin.insertNth_apply_succAbove (α := fun _ => Ω) jc 1 x k

theorem sImg_self (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) :
    sImg jc x (i, jc) = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N)
      (if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k)) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) jc _ _

theorem sImg_succAbove (jc : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    sImg jc x (i, jc.succAbove k) =
      algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (X (Sum.inr (i, k))) := by
  unfold sImg
  congr 1
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) jc _ _ k

theorem sum_y_sImg (jc : Fin (N + 1)) (x : Fin N → Ω) {i : Fin (D + 1)} (hi : i ≠ 0) :
    ∑ j, algebraMap Ω (OmS Ω D N) (yv jc x j) * sImg jc x (i, j) = 0 := by
  rw [Fin.sum_univ_succAbove _ jc, yv_self, sImg_self, if_neg hi]
  simp only [yv_succAbove, sImg_succAbove, map_one, one_mul, map_neg, map_sum, map_mul]
  rw [neg_add_eq_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [IsScalarTower.algebraMap_apply Ω (MvPolynomial (SVar D N) Ω) (OmS Ω D N),
    MvPolynomial.algebraMap_eq, mul_comm]

theorem exists_valuation_adapted_index (jc : Fin (N + 1)) (x : Fin N → Ω) (W : ValuationSubring Ω) :
    ∃ j0, yv jc x j0 ≠ 0 ∧ ∀ j, yv jc x j / yv jc x j0 ∈ W := by
  obtain ⟨j0, -, hj0⟩ := Finset.exists_max_image Finset.univ (fun j => W.valuation (yv jc x j))
    ⟨jc, Finset.mem_univ _⟩
  have h1 : W.valuation (yv jc x jc) = 1 := by rw [yv_self, map_one]
  have hne : W.valuation (yv jc x j0) ≠ 0 := by
    intro h
    have hle := hj0 jc (Finset.mem_univ _)
    rw [h, h1] at hle
    exact one_ne_zero (le_antisymm hle zero_le')
  refine ⟨j0, fun h => hne (by rw [h, map_zero]), fun j => ?_⟩
  rw [← ValuationSubring.valuation_le_one_iff, map_div₀]
  exact (div_le_one₀ (zero_lt_iff.mpr hne)).mpr (hj0 j (Finset.mem_univ _))

def tj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) : SVar D N → OmS Ω D N :=
  Sum.elim (fun _ => sImg jc x (0, j0)) (fun p => sImg jc x (p.1, j0.succAbove p.2))

def qj (jc j0 : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) : MvPolynomial (SVar D N) Ω :=
  Fin.insertNth (α := fun _ => MvPolynomial (SVar D N) Ω) j0
    (if p.1 = 0 then X (Sum.inl ())
      else -∑ k, C (yv jc x (j0.succAbove k) / yv jc x j0) * X (Sum.inr (p.1, k)))
    (fun k => X (Sum.inr (p.1, k))) p.2

variable {jc j0 : Fin (N + 1)} {x : Fin N → Ω}

theorem aeval_qj (hy0 : yv jc x j0 ≠ 0) (p : TVar D N) :
    aeval (tj jc j0 x) (qj jc j0 x p) = sImg jc x p := by
  obtain ⟨i, j⟩ := p
  rcases Fin.eq_self_or_eq_succAbove j0 j with h | ⟨k, h⟩
  · rw [h]
    simp only [qj, Fin.insertNth_apply_same]
    split_ifs with hi
    · rw [hi, aeval_X]
      rfl
    · have hs := sum_y_sImg jc x hi
      rw [Fin.sum_univ_succAbove _ j0] at hs
      have hy : algebraMap Ω (OmS Ω D N) (yv jc x j0) ≠ 0 := (map_ne_zero _).mpr hy0
      have key : sImg jc x (i, j0) = -(∑ k, algebraMap Ω (OmS Ω D N) (yv jc x (j0.succAbove k)) *
          sImg jc x (i, j0.succAbove k)) / algebraMap Ω (OmS Ω D N) (yv jc x j0) := by
        rw [eq_div_iff hy]
        linear_combination hs
      simp only [map_neg, map_sum, map_mul, aeval_X, aeval_C, tj, Sum.elim_inr, map_div₀]
      rw [key, neg_div, Finset.sum_div]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
  · rw [h]
    simp only [qj, Fin.insertNth_apply_succAbove, aeval_X]
    rfl

def intPoly (σ : Type) (W : Subring Ω) : Subring (MvPolynomial σ Ω) where
  carrier := {P | ∀ e, P.coeff e ∈ W}
  mul_mem' := by
    intro P Q hP hQ e
    classical
    rw [coeff_mul]
    exact sum_mem fun d _ => W.mul_mem (hP _) (hQ _)
  one_mem' := by
    intro e
    classical
    rw [coeff_one]
    split_ifs
    exacts [W.one_mem, W.zero_mem]
  add_mem' := by
    intro P Q hP hQ e
    rw [coeff_add]
    exact W.add_mem (hP e) (hQ e)
  zero_mem' := by
    intro e
    rw [coeff_zero]
    exact W.zero_mem
  neg_mem' := by
    intro P hP e
    rw [coeff_neg]
    exact W.neg_mem (hP e)

theorem mem_intPoly {σ : Type} {W : Subring Ω} {P : MvPolynomial σ Ω} :
    P ∈ intPoly σ W ↔ ∀ e, P.coeff e ∈ W :=
    Iff.rfl

theorem C_mem_intPoly {σ : Type} {W : Subring Ω} {a : Ω} (ha : a ∈ W) : (C a : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_C]
  split_ifs
  exacts [ha, W.zero_mem]

theorem X_mem_intPoly {σ : Type} {W : Subring Ω} (s : σ) : (X s : MvPolynomial σ Ω) ∈ intPoly σ W := by
  intro e
  classical
  rw [coeff_X']
  split_ifs
  exacts [W.one_mem, W.zero_mem]

theorem aeval_mem_intPoly {σ τ : Type} {W : Subring Ω} {q : σ → MvPolynomial τ Ω}
    (hq : ∀ s, q s ∈ intPoly τ W) {P : MvPolynomial σ Ω} (hP : P ∈ intPoly σ W) :
    aeval q P ∈ intPoly τ W := by
  rw [P.as_sum, map_sum]
  refine Subring.sum_mem _ fun v _ => ?_
  rw [aeval_monomial]
  refine Subring.mul_mem _ ?_ ?_
  · rw [MvPolynomial.algebraMap_eq]
    exact C_mem_intPoly (hP v)
  · exact Subring.prod_mem _ fun s _ => Subring.pow_mem _ (hq s) _

theorem qj_mem {W : Subring Ω} (hyW : ∀ j, yv jc x j / yv jc x j0 ∈ W) (p : TVar D N) :
    qj jc j0 x p ∈ intPoly (SVar D N) W := by
  obtain ⟨i, j⟩ := p
  rcases Fin.eq_self_or_eq_succAbove j0 j with h | ⟨k, h⟩
  · rw [h]
    simp only [qj, Fin.insertNth_apply_same]
    split_ifs
    · exact X_mem_intPoly _
    · exact Subring.neg_mem _ (Subring.sum_mem _ fun k _ =>
        Subring.mul_mem _ (C_mem_intPoly (hyW _)) (X_mem_intPoly _))
  · rw [h]
    simp only [qj, Fin.insertNth_apply_succAbove]
    exact X_mem_intPoly _

end Formalism.L2.Pj.LocAlg
