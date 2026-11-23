import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwlineLemmas

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_pt (n : ℕ) (D : Finset (Fin n × Fin n)) : Fin n × Fin n → MvPolynomial (Fin n × Fin n) ℚ :=
  open Classical in
  fun v => (if v.1 = v.2 then 1 else 0) + (if v ∈ D then X v else 0)

def qn_IntS (n : ℕ) : Subring (MvPolynomial (Fin n × Fin n) ℚ) :=
  (MvPolynomial.map (σ := Fin n × Fin n) (Int.castRingHom ℚ)).range

theorem qn_pt_step (n : ℕ) (D : Finset (Fin n × Fin n)) (a s : Fin n) (hw : (a, s) ∉ D)
    (hs : ∀ c, (s, c) ∉ D) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n (insert (a, s) D)) F =
      Polynomial.eval₂ (aeval (qn_pt n D)).toRingHom (X (a, s)) (rowGen ℚ s a F) := by
  classical
  have h : (aeval (qn_pt n (insert (a, s) D))).toRingHom =
      (Polynomial.eval₂RingHom (aeval (qn_pt n D)).toRingHom (X (a, s))).comp (rowGen ℚ s a).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [rowGen, algebraMap_eq, Polynomial.algebraMap_apply]
    · rintro ⟨b, c⟩
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        rowGen, aeval_X, Polynomial.coe_eval₂RingHom]
      by_cases hb : b = a
      · subst hb
        by_cases hc : c = s
        · subst hc
          simp [qn_pt, hw, hs]
        · have h1 : (b, c) ≠ (b, s) := by simp [hc]
          have h2 : s ≠ c := fun h => hc h.symm
          simp [qn_pt, hs, h1, h2, hc]
      · have h1 : (b, c) ≠ (a, s) := by simp [hb]
        simp [qn_pt, h1, hb]
  exact congrArg (fun φ => φ F) h

theorem qn_pt_empty (n : ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ) :
    aeval (qn_pt n ∅) F = C (eval (idFrame ℚ n n) F) := by
  have h : (aeval (qn_pt n ∅)).toRingHom = (C : ℚ →+* MvPolynomial (Fin n × Fin n) ℚ).comp (eval (idFrame ℚ n n)) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [algebraMap_eq]
    · rintro ⟨b, c⟩
      by_cases hbc : b = c
      · subst hbc; simp [qn_pt, idFrame]
      · have : b.val ≠ c.val := fun h => hbc (Fin.ext h)
        simp [qn_pt, idFrame, hbc, this]
  exact congrArg (fun φ => φ F) h

theorem qn_X_mem (n : ℕ) (v : Fin n × Fin n) : (X v : MvPolynomial (Fin n × Fin n) ℚ) ∈ qn_IntS n :=
  ⟨X v, by simp⟩

theorem qn_int_pt (n : ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z) (D : Finset (Fin n × Fin n)) :
    (∀ x ∈ D, x.2 < x.1) → ∀ F ∈ W, aeval (qn_pt n D) F ∈ qn_IntS n := by
  classical
  induction D using Finset.induction_on_min_value (fun x : Fin n × Fin n => x.1) with
  | empty =>
    intro _ F hF
    obtain ⟨z, hz⟩ := hev F hF
    rw [qn_pt_empty, hz]
    exact ⟨C z, by simp⟩
  | insert w D hw hmin ih =>
    obtain ⟨a, s⟩ := w
    intro hD F hF
    have hsa : s < a := hD (a, s) (Finset.mem_insert_self _ _)
    have hs : ∀ c, (s, c) ∉ D := by
      intro c hc
      have := hmin (s, c) hc
      exact absurd hsa (not_lt.mpr this)
    have ih' := ih (fun x hx => hD x (Finset.mem_insert_of_mem hx))
    rw [qn_pt_step n D a s hw hs, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    refine Subring.sum_mem _ fun k _ => ?_
    exact Subring.mul_mem _ (ih' _ (hW F hF s a k (ne_of_lt hsa))) (Subring.pow_mem _ (qn_X_mem n _) _)

def qn_low (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun v => v.2 < v.1

def qn_off {n : ℕ} (m : Fin n × Fin n →₀ ℕ) : Fin n × Fin n →₀ ℕ := m.filter fun v => v.2 < v.1

theorem qn_prod_pt (n : ℕ) (m : Fin n × Fin n →₀ ℕ) :
    (∏ i, qn_pt n (qn_low n) i ^ m i) = open Classical in if LowerTri m then monomial (qn_off m) 1 else 0 := by
  classical
  split_ifs with h
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    refine Finset.prod_congr rfl fun i _ => ?_
    obtain ⟨a, c⟩ := i
    rcases lt_trichotomy a c with hac | hac | hac
    · have h0 : m (a, c) = 0 := h a c hac
      have h1 : ¬ c < a := not_lt.mpr hac.le
      simp [h0, qn_off, Finsupp.filter_apply, h1]
    · subst hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply]
    · have h1 : a ≠ c := ne_of_gt hac
      simp [qn_pt, qn_low, qn_off, Finsupp.filter_apply, hac, h1]
  · unfold LowerTri at h
    push Not at h
    obtain ⟨a, c, hac, hne⟩ := h
    refine Finset.prod_eq_zero (Finset.mem_univ (a, c)) ?_
    have hac' : a < c := hac
    have h1 : ¬ c < a := not_lt.mpr hac'.le
    have h2 : a ≠ c := ne_of_lt hac'
    simp [qn_pt, qn_low, h1, h2, hne]

theorem qn_off_inj {n : ℕ} (ν : Fin n → ℕ) (m e : Fin n × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hmc : ∀ t : Fin n, ∑ a : Fin n, m (a, t) = ν t) (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t)
    (h : qn_off m = qn_off e) : m = e := by
  classical
  have hoff : ∀ a c : Fin n, a ≠ c → m (a, c) = e (a, c) := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with h1 | h1
    · rw [hm a c h1, he a c h1]
    · have := DFunLike.congr_fun h (a, c)
      simpa [qn_off, Finsupp.filter_apply, h1] using this
  ext ⟨a, c⟩
  by_cases hac : a = c
  · subst hac
    have h1 := hmc a
    have h2 := hec a
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a)] at h1 h2
    have h3 : ∑ x ∈ Finset.univ.erase a, m (x, a) = ∑ x ∈ Finset.univ.erase a, e (x, a) :=
      Finset.sum_congr rfl fun x hx => hoff x a (Finset.ne_of_mem_erase hx)
    omega
  · exact hoff a c hac

theorem qn_coeff_pt (n : ℕ) (ν : Fin n → ℕ) (F : MvPolynomial (Fin n × Fin n) ℚ)
    (hF : IsWeightedHomogeneous (colW n n) F ν) (e : Fin n × Fin n →₀ ℕ) (he : LowerTri e)
    (hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t) :
    coeff (qn_off e) (aeval (qn_pt n (qn_low n)) F) = coeff e F := by
  classical
  rw [aeval_def, eval₂_eq', coeff_sum]
  simp only [algebraMap_eq, coeff_C_mul, qn_prod_pt]
  rw [Finset.sum_eq_single e]
  · rw [if_pos he, coeff_monomial, if_pos rfl, mul_one]
  · intro m hm hne
    split_ifs with hl
    · rw [coeff_monomial, if_neg, mul_zero]
      intro hoff
      apply hne
      refine qn_off_inj ν m e hl he ?_ hec hoff
      intro t
      rw [← lhwline_weight_col, hF (mem_support_iff.mp hm)]
    · simp
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

theorem qn_tri (n : ℕ) (ν : Fin n → ℕ) (W : Set (MvPolynomial (Fin n × Fin n) ℚ))
    (hW : ∀ F ∈ W, ∀ (a b : Fin n) (k : ℕ), a ≠ b → rowDiv ℚ a b k F ∈ W)
    (hev : ∀ F ∈ W, ∃ z : ℤ, eval (idFrame ℚ n n) F = z)
    (hcol : ∀ F ∈ W, IsWeightedHomogeneous (colW n n) F ν) :
    ∀ F ∈ W, ∀ e : Fin n × Fin n →₀ ℕ, LowerTri e → ∃ z : ℤ, coeff e F = z := by
  classical
  intro F hF e he
  by_cases hec : ∀ t : Fin n, ∑ a : Fin n, e (a, t) = ν t
  · rw [← qn_coeff_pt n ν F (hcol F hF) e he hec]
    obtain ⟨G, hG⟩ := qn_int_pt n W hW hev (qn_low n) (fun x hx => (Finset.mem_filter.mp hx).2) F hF
    refine ⟨coeff (qn_off e) G, ?_⟩
    rw [← hG, coeff_map]
    rfl
  · refine ⟨0, ?_⟩
    rw [Int.cast_zero]
    by_contra hne
    apply hec
    intro t
    rw [← lhwline_weight_col, hcol F hF hne]

end Formalism.InvariantFactorPaths.ColumnFamilies
