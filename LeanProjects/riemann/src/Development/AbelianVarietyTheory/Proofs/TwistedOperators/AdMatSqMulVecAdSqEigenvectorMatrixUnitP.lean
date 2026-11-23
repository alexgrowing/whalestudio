import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory

noncomputable section
namespace GlobalTheory.PolarU

variable {p q : ℕ}

def posMat (p q : ℕ) (f : Bool → ℕ → Bool → ℕ → ℂ) : Mat p q :=
  Matrix.of fun a b => f a.isLeft (posIx a) b.isLeft (posIx b)

theorem sum_ite_val {n : ℕ} (m : ℕ) (g : ℕ → ℂ) :
    (∑ j : Fin n, if m = (j : ℕ) then g j else 0) = if m < n then g m else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨m, h⟩ : Fin n)]
    · simp
    · intro b _ hb
      rw [if_neg]
      rintro rfl
      exact hb rfl
    · simp
  · refine Finset.sum_eq_zero fun j _ => if_neg ?_
    rintro rfl
    exact h j.2

theorem posIx_inl (i : Fin p) : posIx (Sum.inl i : Ix p q) = i := rfl

theorem posIx_inr (j : Fin q) : posIx (Sum.inr j : Ix p q) = j := rfl

theorem aOf_apply (h : ℕ → ℝ) (a b : Ix p q) :
    aOf p q h a b = if a.isLeft = b.isLeft then 0
      else if posIx a = posIx b then ((h (posIx a) : ℝ) : ℂ) else 0 := by
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : (i : ℕ) = j <;>
    simp [aOf, pOf, posIx_inl, posIx_inr, hij, eq_comm (a := (j : ℕ))]

theorem aOf_symm (h : ℕ → ℝ) (a b : Ix p q) : aOf p q h a b = aOf p q h b a := by
  rw [aOf_apply, aOf_apply]
  by_cases h1 : a.isLeft = b.isLeft
  · simp [h1]
  · by_cases h2 : posIx a = posIx b
    · simp [h1, Ne.symm h1, h2]
    · simp [h1, Ne.symm h1, h2, Ne.symm h2]

theorem sum_aOf (h : ℕ → ℝ) (a : Ix p q) (g : Bool → ℕ → ℂ) :
    ∑ c, aOf p q h a c * g c.isLeft (posIx c)
      = (cutH p q h (posIx a) : ℂ) * g (!a.isLeft) (posIx a) := by
  rw [Fintype.sum_sum_type]
  rcases a with i | i
  · have h1 : ∀ k : Fin p, aOf p q h (Sum.inl i) (Sum.inl k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin q, aOf p q h (Sum.inl i) (Sum.inr k) * g false k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g false k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, zero_add, Bool.not_true]
    rw [sum_ite_val (n := q) i (fun m => ((h i : ℝ) : ℂ) * g false m)]
    by_cases hi : (i : ℕ) < q <;> simp [cutH, hi]
  · have h1 : ∀ k : Fin q, aOf p q h (Sum.inr i) (Sum.inr k) = 0 := fun k => by simp [aOf_apply]
    have h2 : ∀ k : Fin p, aOf p q h (Sum.inr i) (Sum.inl k) * g true k
        = if (i : ℕ) = k then ((h i : ℝ) : ℂ) * g true k else 0 := fun k => by
      by_cases hk : (i : ℕ) = k <;> simp [aOf_apply, posIx_inl, posIx_inr, hk]
    simp only [h1, posIx_inl, posIx_inr, Sum.isLeft_inl, Sum.isLeft_inr, h2, zero_mul,
      Finset.sum_const_zero, add_zero, Bool.not_false]
    rw [sum_ite_val (n := p) i (fun m => ((h i : ℝ) : ℂ) * g true m)]
    by_cases hi : (i : ℕ) < p <;> simp [cutH, hi]

theorem ad_aOf_posMat (h : ℕ → ℝ) (f : Bool → ℕ → Bool → ℕ → ℂ) :
    aOf p q h * posMat p q f - posMat p q f * aOf p q h
      = posMat p q fun s m t n =>
        (cutH p q h m : ℂ) * f (!s) m t n - (cutH p q h n : ℂ) * f s m (!t) n := by
  ext a b
  simp only [Matrix.sub_apply, Matrix.mul_apply, posMat, Matrix.of_apply]
  rw [sum_aOf h a (fun s m => f s m b.isLeft (posIx b)),
    ← sum_aOf h b (fun t n => f a.isLeft (posIx a) t n)]
  congr 1
  exact Finset.sum_congr rfl fun c _ => by rw [mul_comm, aOf_symm]

theorem eigP_eq_posMat (ab : PIx p q) :
    eigP ab.1 = vecM (posMat p q fun s m t n =>
      if s ≠ t ∧ m = posIx ab.1.1 ∧ n = posIx ab.1.2 then
        (if ab.1.1.isLeft then 1 else if s then -1 else 1) else 0) := by
  obtain ⟨⟨a, b⟩, hab⟩ := ab
  funext ⟨c, d⟩
  rcases a with i | i <;> rcases b with j | j <;> simp only [sameBlock, not_true] at hab <;>
    rcases c with k | k <;> rcases d with l | l <;>
    simp [eigP, vecM, posMat, posIx_inl, posIx_inr, sameBlock, Fin.ext_iff]
  split_ifs <;> rfl

theorem adMat_sq_mulVec_eigP (p q : ℕ) (h : ℕ → ℝ) (ab : PIx p q) :
    (adMat (aOf p q h) ^ 2) *ᵥ eigP ab.1 = (((rootP h ab.1 : ℝ) : ℂ) ^ 2) • eigP ab.1 := by
  rw [pow_two (adMat _), ← Matrix.mulVec_mulVec, eigP_eq_posMat, adMat_mulVec, ad_aOf_posMat,
    adMat_mulVec, ad_aOf_posMat]
  funext ⟨c, d⟩
  simp only [vecM, posMat, Matrix.of_apply, Pi.smul_apply, smul_eq_mul, rootP, Bool.not_not]
  generalize c.isLeft = s
  generalize d.isLeft = t
  generalize ab.1.1.isLeft = u
  by_cases hm : posIx c = posIx ab.1.1 ∧ posIx d = posIx ab.1.2
  · rw [hm.1, hm.2]
    cases s <;> cases t <;> cases u <;> simp <;> ring
  · simp [hm]

end GlobalTheory.PolarU
