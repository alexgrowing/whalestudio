import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntDerApply
open IsLocalRing GlobalTheory.FormalOrigin

namespace GlobalTheory.FormalOrigin.TaylorDeriv

theorem foldr_iterate_comm {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι → ℕ) (a : ι) (f : A) (l : List ι) :
    l.foldr (fun i g => (ds i)^[α i] g) (ds a f) = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, ih]
    have : Function.Commute (ds i) (ds a) := fun x => h i a x
    exact (this.iterate_left (α i)) _

theorem foldr_iterate_add_single {A ι : Type} (ds : ι → A → A) (h : ∀ a b f, ds a (ds b f) = ds b (ds a f))
    (α : ι →₀ ℕ) (a : ι) (f : A) (l : List ι) (hl : l.Nodup) (ha : a ∈ l) :
    l.foldr (fun i g => (ds i)^[(α + Finsupp.single a 1 : ι →₀ ℕ) i] g) f
      = ds a (l.foldr (fun i g => (ds i)^[α i] g) f) := by
  classical
  induction l with
  | nil => simp at ha
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.foldr_cons]
    by_cases hi : i = a
    · subst hi
      have : l.foldr (fun j g => (ds j)^[(α + Finsupp.single i 1 : ι →₀ ℕ) j] g) f
          = l.foldr (fun j g => (ds j)^[α j] g) f := by
        apply List.foldr_ext
        intro j hj b
        have : j ≠ i := fun e => hl.1 (e ▸ hj)
        simp [Finsupp.single_apply, this.symm]
      rw [this]
      simp [Function.iterate_succ_apply']
    · have ha' : a ∈ l := by
        rcases List.mem_cons.1 ha with e | e
        · exact absurd e.symm hi
        · exact e
      rw [ih hl.2 ha']
      have e : (α + Finsupp.single a 1 : ι →₀ ℕ) i = α i := by
        simp [Finsupp.single_apply, Ne.symm hi]
      rw [e]
      have : Function.Commute (ds i) (ds a) := fun x => h i a x
      exact (this.iterate_left (α i)) _

theorem iterOp_apply_eq_add_single {A : Type} {n : ℕ} (ds : Fin n → A → A)
    (h : ∀ a b f, ds a (ds b f) = ds b (ds a f)) (α : Fin n →₀ ℕ) (a : Fin n) (f : A) :
    iterOp ds α (ds a f) = iterOp ds (α + Finsupp.single a 1) f := by
  unfold iterOp
  rw [foldr_iterate_comm ds h, foldr_iterate_add_single ds h α a f _ (List.nodup_finRange n) (List.mem_finRange a)]

theorem prod_factorial_add_single {n : ℕ} (α : Fin n →₀ ℕ) (a : Fin n) :
    ∏ i, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = (∏ i, ((α i).factorial : ℚ)) * ((α a : ℚ) + 1) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ← Finset.mul_prod_erase _ (fun i => ((α i).factorial : ℚ)) (Finset.mem_univ a)]
  have : ∏ i ∈ Finset.univ.erase a, (((α + Finsupp.single a 1 : Fin n →₀ ℕ) i).factorial : ℚ)
      = ∏ i ∈ Finset.univ.erase a, ((α i).factorial : ℚ) := by
    refine Finset.prod_congr rfl fun i hi => ?_
    have := Finset.ne_of_mem_erase hi
    simp [Finsupp.single_apply, this.symm]
  rw [this]
  simp [Nat.factorial_succ]
  ring

theorem taylor_deriv_eq_pderiv : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra ℚ B] (n : ℕ) (ev : A →+* B) (ds : Fin n → Derivation ℤ A A), (∀ a b f, ds a (ds b f) = ds b (ds a f)) → ∀ a f, taylor ev (fun i => ⇑(ds i)) (ds a f) = MvPowerSeries.pderiv B a (taylor ev (fun i => ⇑(ds i)) f) := by
  intro A B _ _ _ n ev ds h a f
  ext α
  rw [MvPowerSeries.coeff_pderiv]
  simp only [MvPowerSeries.coeff_apply, taylor]
  rw [prod_factorial_add_single, ← iterOp_apply_eq_add_single (fun i => ⇑(ds i)) h]
  have e : ((α a : B) + 1) = algebraMap ℚ B ((α a : ℚ) + 1) := by simp
  have hp : ((α a : ℚ) + 1) ≠ 0 := by positivity
  rw [e, mul_comm _ (algebraMap ℚ B _), ← Algebra.smul_def, smul_smul]
  congr 1
  field_simp

end GlobalTheory.FormalOrigin.TaylorDeriv
