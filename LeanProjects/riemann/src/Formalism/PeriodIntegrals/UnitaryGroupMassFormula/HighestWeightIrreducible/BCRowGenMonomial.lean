import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ClosedEqNablaC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LGradedLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwinLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ClosedEqNabla
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas

open MvPolynomial Formalism.GradedWeylDivisibility Formalism.REAL

noncomputable section

namespace PI.WHw

theorem bC_rowGen_X {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen ℂ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (lgraded_wa (n := n) a v) := by
  simp only [rowGen, MvPolynomial.aeval_X, lgraded_wa]
  split_ifs with h
  · have hv : ((a, v.2) : Fin r × Fin n) = v := Prod.ext h.symm rfl
    rw [hv]
    ring
  · simp

theorem bC_rowGen_C {r n : ℕ} (a : Fin r) (c : ℂ) :
    rowGen ℂ a a (C c : MvPolynomial (Fin r × Fin n) ℂ) = Polynomial.C (C c) := by
  first
    | simp [rowGen, MvPolynomial.aeval_C]
    | rfl

theorem bC_rowGen_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowGen ℂ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (lgraded_wa a) m) := by
  induction m using Finsupp.induction
  next =>
    rw [MvPolynomial.monomial_zero', bC_rowGen_C]
    simp
  next v e m _ _ ih =>
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow, bC_rowGen_X, ih]
    have hw : Finsupp.weight (lgraded_wa a) (Finsupp.single v e + m) =
        e * lgraded_wa a v + Finsupp.weight (lgraded_wa a) m := by
      simp [map_add, Finsupp.weight_apply, Finsupp.sum_single_index]
    rw [hw]
    simp only [map_mul, map_pow]
    ring

theorem bC_euler_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowDiv ℂ a a 1 (monomial m c) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℂ) • monomial m c := by
  unfold rowDiv
  rw [bC_rowGen_monomial, Polynomial.coeff_C_mul, add_comm (1 : Polynomial _) Polynomial.X,
    Polynomial.coeff_X_add_one_pow, Nat.choose_one_right]
  first
    | rw [Nat.cast_smul_eq_nsmul, nsmul_eq_mul, mul_comm]
    | simp [nsmul_eq_mul, mul_comm]
    | (rw [MvPolynomial.smul_eq_C_mul, mul_comm]; simp)

theorem bC_coeff_euler {r n : ℕ} (a : Fin r) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (m : Fin r × Fin n →₀ ℕ) :
    coeff m (rowDiv ℂ a a 1 f) = ((Finsupp.weight (lgraded_wa a) m : ℕ) : ℂ) * coeff m f := by
  have hadd : ∀ p q : MvPolynomial (Fin r × Fin n) ℂ,
      rowDiv ℂ a a 1 (p + q) = rowDiv ℂ a a 1 p + rowDiv ℂ a a 1 q := by
    intro p q
    simp [rowDiv, map_add]
  induction f using MvPolynomial.induction_on'
  next m' c =>
    rw [bC_euler_monomial, MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    split_ifs with h
    · subst h
      simp [smul_eq_mul]
    · simp
  next p q hp hq =>
    rw [hadd, MvPolynomial.coeff_add, MvPolynomial.coeff_add, hp, hq, mul_add]

theorem bC_sep {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (a : Fin r) (V : Finset ℕ) :
    ∀ f ∈ M, (∀ m ∈ f.support, Finsupp.weight (lgraded_wa a) m ∈ V) →
      ∀ t, weightedHomogeneousComponent (lgraded_wa a) t f ∈ M := by
  classical
  induction V using Finset.induction_on
  next =>
    intro f _ hV t
    have hf0 : f = 0 := by
      ext m
      by_contra hm
      have h1 := hV m (MvPolynomial.mem_support_iff.mpr (by simpa using hm))
      simp at h1
    rw [hf0, map_zero]
    exact M.zero_mem
  next s V hs ih =>
    intro f hf hV t
    set g := rowDiv ℂ a a 1 f - (s : ℂ) • f with hg
    have hgM : g ∈ M := M.sub_mem (hM a a 1 f hf) (M.smul_mem _ hf)
    have hcg : ∀ m, MvPolynomial.coeff m g =
        ((Finsupp.weight (lgraded_wa a) m : ℂ) - s) * MvPolynomial.coeff m f := by
      intro m
      rw [hg, MvPolynomial.coeff_sub, MvPolynomial.coeff_smul, bC_coeff_euler, smul_eq_mul]
      ring
    have hgV : ∀ m ∈ g.support, Finsupp.weight (lgraded_wa a) m ∈ V := by
      intro m hm
      rw [MvPolynomial.mem_support_iff, hcg] at hm
      have hfm : MvPolynomial.coeff m f ≠ 0 := right_ne_zero_of_mul hm
      have hws : (Finsupp.weight (lgraded_wa a) m : ℂ) - s ≠ 0 := left_ne_zero_of_mul hm
      rcases Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hfm)) with h | h
      · exact (hws (by rw [h, sub_self])).elim
      · exact h
    have hIH := ih g hgM hgV
    have hcomp : ∀ t', t' ≠ s → weightedHomogeneousComponent (lgraded_wa a) t' f ∈ M := by
      intro t' ht'
      have e : weightedHomogeneousComponent (lgraded_wa a) t' f =
          ((t' : ℂ) - s)⁻¹ • weightedHomogeneousComponent (lgraded_wa a) t' g := by
        ext m
        rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_weightedHomogeneousComponent,
          MvPolynomial.coeff_weightedHomogeneousComponent, hcg]
        split_ifs with hm
        · rw [hm, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀, one_mul]
          exact sub_ne_zero.mpr (by exact_mod_cast ht')
        · simp
      rw [e]
      exact M.smul_mem _ (hIH t')
    by_cases hts : t = s
    · rw [hts]
      have hsum : weightedHomogeneousComponent (lgraded_wa a) s f =
          f - ∑ t' ∈ V, weightedHomogeneousComponent (lgraded_wa a) t' f := by
        ext m
        rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_sum]
        simp only [MvPolynomial.coeff_weightedHomogeneousComponent]
        rw [Finset.sum_ite_eq]
        by_cases hm : MvPolynomial.coeff m f = 0
        · simp [hm]
        · rcases Finset.mem_insert.mp (hV m (MvPolynomial.mem_support_iff.mpr hm)) with h | h
          · simp [h, hs]
          · have hne : Finsupp.weight (lgraded_wa a) m ≠ s := fun e => hs (e ▸ h)
            simp [h, hne]
      rw [hsum]
      exact M.sub_mem hf (M.sum_mem fun t' ht' => hcomp t' (fun e => hs (e ▸ ht')))
    · exact hcomp t hts

theorem bC_multi {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (μ : Fin r → ℕ) (A : Finset (Fin r)) :
    ∀ f ∈ M, ∃ h ∈ M, ∀ m, coeff m h =
      if (∀ a ∈ A, Finsupp.weight (lgraded_wa a) m = μ a) then coeff m f else 0 := by
  classical
  induction A using Finset.induction_on
  next =>
    intro f hf
    exact ⟨f, hf, fun m => by simp⟩
  next a0 A ha0 ih =>
    intro f hf
    obtain ⟨h, hhM, hh⟩ := ih f hf
    refine ⟨weightedHomogeneousComponent (lgraded_wa a0) (μ a0) h,
      bC_sep M hM a0 (h.support.image (Finsupp.weight (lgraded_wa a0))) h hhM
        (fun m hm => Finset.mem_image_of_mem _ hm) (μ a0), fun m => ?_⟩
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, hh]
    by_cases h1 : Finsupp.weight (lgraded_wa a0) m = μ a0
    · simp [h1, Finset.forall_mem_insert]
    · simp [h1, Finset.forall_mem_insert]

theorem bC_graded {r n : ℕ} (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M)
    (f : MvPolynomial (Fin r × Fin n) ℂ) (hf : f ∈ M) (μ : Fin r → ℕ) :
    weightedHomogeneousComponent (rowW r n) μ f ∈ M := by
  classical
  have hw : ∀ (m : Fin r × Fin n →₀ ℕ) (a : Fin r),
      (Finsupp.weight (rowW r n) m) a = Finsupp.weight (lgraded_wa a) m := by
    intro m a
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, rowW, lgraded_wa, Pi.smul_apply,
      Pi.single_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases h : v.1 = a
    · simp [h]
    · simp [h, Ne.symm h]
  obtain ⟨h, hhM, hh⟩ := bC_multi M hM μ Finset.univ f hf
  have e : weightedHomogeneousComponent (rowW r n) μ f = h := by
    ext m
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, hh]
    have hiff : Finsupp.weight (rowW r n) m = μ ↔
        ∀ a ∈ Finset.univ, Finsupp.weight (lgraded_wa a) m = μ a := by
      constructor
      · intro e a _
        rw [← hw, e]
      · intro e
        funext a
        rw [hw]
        exact e a (Finset.mem_univ a)
    by_cases e1 : Finsupp.weight (rowW r n) m = μ
    · rw [if_pos e1, if_pos (hiff.mp e1)]
    · rw [if_neg e1, if_neg (fun h' => e1 (hiff.mpr h'))]
  rw [e]
  exact hhM

private theorem isWeightedHomogeneous_coeff_rowGen_X_fst_weight {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) (k : ℕ) :
    IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      ((rowGen ℂ a b (X v)).coeff k) (((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
  simp only [rowGen, MvPolynomial.aeval_X]
  have hX : ∀ u : Fin r × Fin n, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      (X u : MvPolynomial (Fin r × Fin n) ℂ) ((u.1 : ℕ) : ℤ) :=
    fun u => MvPolynomial.isWeightedHomogeneous_X ℂ _ u
  have h0 : ∀ e : ℤ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      (0 : MvPolynomial (Fin r × Fin n) ℂ) e :=
    fun e => MvPolynomial.isWeightedHomogeneous_zero ℂ _ e
  by_cases hb : v.1 = b
  · rw [if_pos hb, Polynomial.X_mul_C, Polynomial.C_mul_X_eq_monomial, Polynomial.coeff_add,
      Polynomial.coeff_C, Polynomial.coeff_monomial]
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hX v
    · by_cases hk1 : k = 1
      · subst hk1
        have e : ((v.1 : ℕ) : ℤ) + ((1 : ℕ) : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) = ((a : ℕ) : ℤ) := by
          rw [hb]
          push_cast
          ring
        rw [e]
        simpa using hX (a, v.2)
      · rw [if_neg hk0, if_neg (Ne.symm hk1), add_zero]
        exact h0 _
  · rw [if_neg hb, add_zero, Polynomial.coeff_C]
    by_cases hk0 : k = 0
    · subst hk0
      simpa using hX v
    · rw [if_neg hk0]
      exact h0 _

private theorem isWeightedHomogeneous_coeff_mul_fst_weight {r n : ℕ} (c : ℤ)
    (F G : Polynomial (MvPolynomial (Fin r × Fin n) ℂ)) (d e : ℤ)
    (hF : ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (F.coeff k) (d + (k : ℤ) * c))
    (hG : ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (G.coeff k) (e + (k : ℤ) * c)) :
    ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) ((F * G).coeff k) (d + e + (k : ℤ) * c) := by
  intro k
  rw [Polynomial.coeff_mul]
  first
    | (apply MvPolynomial.IsWeightedHomogeneous.sum
       intro x hx
       have hx' : x.1 + x.2 = k := by simpa using hx
       have e1 : d + e + (k : ℤ) * c = (d + (x.1 : ℤ) * c) + (e + (x.2 : ℤ) * c) := by
         rw [← hx']
         push_cast
         ring
       rw [e1]
       exact (hF x.1).mul (hG x.2))
    | (rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
       refine Submodule.sum_mem _ fun x hx => ?_
       rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
       have hx' : x.1 + x.2 = k := by simpa using hx
       have e1 : d + e + (k : ℤ) * c = (d + (x.1 : ℤ) * c) + (e + (x.2 : ℤ) * c) := by
         rw [← hx']
         push_cast
         ring
       rw [e1]
       exact (hF x.1).mul (hG x.2))

private theorem isWeightedHomogeneous_coeff_rowGen_monomial {r n : ℕ} (a b : Fin r) (m : Fin r × Fin n →₀ ℕ) (c0 : ℂ) :
    ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) ((rowGen ℂ a b (monomial m c0)).coeff k)
      (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
  induction m using Finsupp.induction
  next =>
    intro k
    have hC : rowGen ℂ a b (monomial 0 c0 : MvPolynomial (Fin r × Fin n) ℂ) =
        Polynomial.C (MvPolynomial.C c0) := by
      rw [MvPolynomial.monomial_zero']
      first
        | simp [rowGen, MvPolynomial.aeval_C]
        | rfl
    rw [hC, Polynomial.coeff_C]
    by_cases hk : k = 0
    · subst hk
      simpa using MvPolynomial.isWeightedHomogeneous_C (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) c0
    · rw [if_neg hk]
      exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
  next v e m _ _ ih =>
    intro k
    rw [MvPolynomial.monomial_single_add, map_mul, map_pow]
    have hw : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (Finsupp.single v e + m) =
        (e : ℤ) * ((v.1 : ℕ) : ℤ) + Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m := by
      simp [map_add, Finsupp.weight_apply, Finsupp.sum_single_index, nsmul_eq_mul]
    rw [hw]
    have hpow : ∀ j : ℕ, ∀ k : ℕ, IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
        (((rowGen ℂ a b (X v)) ^ j).coeff k) ((j : ℤ) * ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
      intro j
      induction j with
      | zero =>
        intro k
        rw [pow_zero, Polynomial.coeff_one]
        by_cases hk : k = 0
        · subst hk
          simpa using MvPolynomial.isWeightedHomogeneous_one ℂ (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
        · rw [if_neg hk]
          exact MvPolynomial.isWeightedHomogeneous_zero ℂ _ _
      | succ j ihj =>
        intro k
        rw [pow_succ]
        have h := isWeightedHomogeneous_coeff_mul_fst_weight (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) _ _ ((j : ℤ) * ((v.1 : ℕ) : ℤ)) ((v.1 : ℕ) : ℤ) ihj
          (isWeightedHomogeneous_coeff_rowGen_X_fst_weight a b v) k
        rw [show ((j + 1 : ℕ) : ℤ) * ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) =
          (j : ℤ) * ((v.1 : ℕ) : ℤ) + ((v.1 : ℕ) : ℤ) + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) by push_cast; ring]
        exact h
    exact isWeightedHomogeneous_coeff_mul_fst_weight (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) _ _ _ _ (hpow e) ih k

private theorem isWeightedHomogeneous_rowDiv {r n : ℕ} (a b : Fin r) (p : MvPolynomial (Fin r × Fin n) ℂ) (d : ℤ)
    (hp : IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) p d) (k : ℕ) :
    IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) (rowDiv ℂ a b k p) (d + (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ))) := by
  classical
  rw [MvPolynomial.as_sum p]
  unfold rowDiv
  rw [map_sum, Polynomial.finset_sum_coeff]
  first
    | (apply MvPolynomial.IsWeightedHomogeneous.sum
       intro x hx
       have hmd : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) x = d := hp (MvPolynomial.mem_support_iff.mp hx)
       rw [← hmd]
       exact isWeightedHomogeneous_coeff_rowGen_monomial a b x _ k)
    | (rw [← MvPolynomial.mem_weightedHomogeneousSubmodule]
       refine Submodule.sum_mem _ fun x hx => ?_
       rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
       have hmd : Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) x = d := hp (MvPolynomial.mem_support_iff.mp hx)
       rw [← hmd]
       exact isWeightedHomogeneous_coeff_rowGen_monomial a b x _ k)

theorem bC_exists_killed {r n : ℕ}
    (M : Submodule ℂ (MvPolynomial (Fin r × Fin n) ℂ)) (hM : RowDivClosed M) (hne : M ≠ ⊥) :
    ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
  classical
  have hnn : ∀ (p : MvPolynomial (Fin r × Fin n) ℂ) (e : ℤ), IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) p e →
      p ≠ 0 → 0 ≤ e := by
    intro p e hp hp0
    obtain ⟨m, hm⟩ := MvPolynomial.ne_zero_iff.mp hp0
    rw [← hp hm, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_nonneg fun v _ => nsmul_nonneg (by show (0 : ℤ) ≤ ((v.1 : ℕ) : ℤ); positivity) _
  have main : ∀ N : ℕ, ∀ g ∈ M, g ≠ 0 → IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) g (N : ℤ) →
      ∃ v ∈ M, v ≠ 0 ∧ ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k v = 0 := by
    intro N
    induction N using Nat.strong_induction_on with
    | _ N ih =>
      intro g hgM hg0 hgN
      by_cases hk : ∀ a b : Fin r, a < b → ∀ k : ℕ, 1 ≤ k → rowDiv ℂ a b k g = 0
      · exact ⟨g, hgM, hg0, hk⟩
      · push_neg at hk
        obtain ⟨a, b, hab, k, hk1, hne⟩ := hk
        have hh := isWeightedHomogeneous_rowDiv a b g _ hgN k
        have h0 := hnn _ _ hh hne
        have hab' : (a : ℕ) < b := hab
        set s : ℤ := (k : ℤ) * (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) with hs
        have hneg : s ≤ -1 := by
          have h1 : (1 : ℤ) ≤ k := by exact_mod_cast hk1
          have h2 : (((a : ℕ) : ℤ) - ((b : ℕ) : ℤ)) ≤ -1 := by omega
          rw [hs]
          nlinarith
        have hlt : ((((N : ℤ) + s).toNat : ℕ) : ℤ) < (N : ℤ) := by
          rw [Int.toNat_of_nonneg h0]
          omega
        refine ih (((N : ℤ) + s).toNat) (by exact_mod_cast hlt) _ (hM a b k g hgM) hne ?_
        rw [Int.toNat_of_nonneg h0]
        exact hh
  have hL : ∀ m : Fin r × Fin n →₀ ℕ, Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m =
      ∑ i : Fin r, ((i : ℕ) : ℤ) * ((Finsupp.weight (rowW r n) m i : ℕ) : ℤ) := by
    intro m
    simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, rowW, Pi.smul_apply, Pi.single_apply,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [Pi.single_apply] <;> ring
  obtain ⟨f, hfM, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.mp hf0
  have hg0M : weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f ∈ M :=
    bC_graded M hM f hfM _
  have hg0c : coeff m0 (weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f) =
      coeff m0 f := by
    rw [MvPolynomial.coeff_weightedHomogeneousComponent, if_pos rfl]
  have hg0ne : weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f ≠ 0 := by
    intro h
    apply hm0
    rw [← hg0c, h, MvPolynomial.coeff_zero]
  have hg0h : IsWeightedHomogeneous (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ))
      (weightedHomogeneousComponent (rowW r n) (Finsupp.weight (rowW r n) m0) f)
      (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m0) := by
    intro m hm
    rw [MvPolynomial.coeff_weightedHomogeneousComponent] at hm
    split_ifs at hm with h
    · rw [hL, hL, h]
    · exact absurd rfl hm
  have hnn0 := hnn _ _ hg0h hg0ne
  exact main (Finsupp.weight (fun v : Fin r × Fin n => ((v.1 : ℕ) : ℤ)) m0).toNat _ hg0M hg0ne (by rw [Int.toNat_of_nonneg hnn0]; exact hg0h)

end PI.WHw
