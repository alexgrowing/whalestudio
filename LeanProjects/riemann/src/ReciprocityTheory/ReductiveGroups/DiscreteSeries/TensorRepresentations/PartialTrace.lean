import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TensorV
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Gelfand
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.AntiEIsGlRep

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]

def ptr (A : Module.End ℂ (Fin n → M)) : Module.End ℂ M :=
  ∑ c, (coordV c).comp (A.comp (LinearMap.single ℂ (fun _ : Fin n => M) c))

theorem ptr_apply (A : Module.End ℂ (Fin n → M)) (x : M) :
    ptr A x = ∑ c, A (Pi.single c x) c := by
  unfold ptr
  rw [LinearMap.sum_apply]
  rfl

theorem pow_single_of_mat (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) (c : Fin n) (x : M) :
    (A ^ k) (Pi.single c x) = fun s => ePow T k s c x := by
  induction k with
  | zero =>
    funext s
    simp only [pow_zero, ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply, Module.End.one_apply]
    by_cases h : s = c
    · subst h; simp
    · simp [h]
  | succ k ih =>
    funext s
    rw [pow_succ', Module.End.mul_apply, ih, hA]
    simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ', Matrix.mul_apply, Matrix.of_apply, LinearMap.sum_apply,
      Module.End.mul_apply]

theorem ePow_neg_equiv (F : Fin n → Fin n → Module.End ℂ M) (σ : Fin n ≃ Fin n) (k : ℕ) (a b : Fin n) :
    ePow (fun a b => -F (σ a) (σ b)) k a b = ((-1 : ℂ) ^ k) • ePow F k (σ a) (σ b) := by
  induction k generalizing a b with
  | zero => simp [ePow, Bl.ThirdBlockLemmaA.goal1, Matrix.one_apply]
  | succ k ih =>
    have e1 : ∀ (G : Fin n → Fin n → Module.End ℂ M) (a b : Fin n),
        ePow G (k + 1) a b = ∑ r, ePow G k a r * G r b := by
      intro G a b
      simp only [ePow, Bl.ThirdBlockLemmaA.goal1, pow_succ, Matrix.mul_apply, Matrix.of_apply]
    rw [e1, e1]
    simp_rw [ih]
    conv_rhs => rw [Finset.smul_sum, ← Equiv.sum_comp σ]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [smul_mul_assoc, mul_neg, smul_neg, pow_succ, mul_neg_one, neg_smul, mul_one]

theorem ptr_eq_gelfand (A : Module.End ℂ (Fin n → M)) (T : Fin n → Fin n → Module.End ℂ M)
    (hA : ∀ f s, A f s = ∑ r, T s r (f r)) (k : ℕ) : ptr (A ^ k) = gelfand T k := by
  ext x
  rw [ptr_apply]
  simp only [gelfand, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [pow_single_of_mat A T hA k c x]

theorem ptr_eeV_pow (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) :
    ptr (eeV E ^ k) = ((-1 : ℂ) ^ k) • gelfand (antiE E) k := by
  have hA : ∀ f s, eeV E f s = ∑ r, (fun s r => E r s) s r (f r) := by
    intro f s
    simp [eeV, coordV]
  rw [ptr_eq_gelfand _ _ hA k]
  have key : ∀ a, ePow (antiE E) k a a =
      ((-1 : ℂ) ^ k) • ePow (fun s r => E r s) k (Fin.revPerm a) (Fin.revPerm a) := fun a =>
    ePow_neg_equiv (fun s r => E r s) Fin.revPerm k a a
  simp only [gelfand, key, Finset.smul_sum, smul_smul, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_smul]
  exact (Equiv.sum_comp Fin.revPerm (fun a => ePow (fun s r => E r s) k a a)).symm

theorem ptr_eeVd_pow (E : Fin n → Fin n → Module.End ℂ M) (k : ℕ) :
    ptr (eeVd E ^ k) = ((-1 : ℂ) ^ k) • gelfand E k := by
  have hA : ∀ f r, eeVd E f r = ∑ s, (fun r s => -E r s) r s (f s) := by
    intro f r
    simp [eeVd, coordV]
  rw [ptr_eq_gelfand _ _ hA k]
  simp only [gelfand, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact ePow_neg_equiv E (Equiv.refl _) k a a

end ReciprocityTheory.ChartRestriction.DS
