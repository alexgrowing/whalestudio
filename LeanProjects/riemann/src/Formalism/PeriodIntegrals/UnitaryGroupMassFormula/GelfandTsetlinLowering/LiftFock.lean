import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.LiftDefs
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LEhwLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LRowdivLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQRowDivAdj

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility Formalism.REAL MvPolynomial

namespace Fock6

def wa {r n : ℕ} (c : Fin r) : Fin r × Fin n → ℕ := fun v => if v.1 = c then 1 else 0

def rw1 {r n : ℕ} (c : Fin r) : Fin r × Fin n → ℤ := fun v => ((wa c v : ℕ) : ℤ)

theorem applyWord_cons {R : Type*} [CommRing R] {r n : ℕ} (x : Fin r × Fin r × ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl

theorem applyWord_append {R : Type*} [CommRing R] {r n : ℕ} (l1 l2 : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (l1 ++ l2) f = applyWord R l1 (applyWord R l2 f) := by
  unfold applyWord
  exact List.foldr_append ..

theorem weight_indicator_eq_degree {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (c : Fin r) :
    Finsupp.weight (rw1 c) m = ((Finsupp.weight (rowW r n) m c : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum, Finset.sum_apply]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  by_cases hv : v.1 = c
  · simp [rw1, wa, rowW, hv]
  · simp [rw1, wa, rowW, hv, Pi.single_apply, Ne.symm hv]

theorem weight_rw1_eq_weight_wa {r n : ℕ} (m : Fin r × Fin n →₀ ℕ) (c : Fin r) :
    Finsupp.weight (rw1 c) m = ((Finsupp.weight (wa c) m : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  push_cast
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [rw1]

theorem rowGen_diag_X {r n : ℕ} (a : Fin r) (v : Fin r × Fin n) :
    rowGen ℂ a a (X v) = Polynomial.C (X v) * (1 + Polynomial.X) ^ (wa (n := n) a v) := by
  unfold rowGen
  rw [aeval_X]
  by_cases hv : v.1 = a
  · have hv' : (a, v.2) = v := Prod.ext hv.symm rfl
    simp [wa, hv, hv']
    ring
  · simp [wa, hv]

theorem rowGen_diag_C {r n : ℕ} (a : Fin r) (c : ℂ) :
    rowGen ℂ a a (C c : MvPolynomial (Fin r × Fin n) ℂ) = Polynomial.C (C c) := by
  unfold rowGen
  rw [aeval_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]

theorem rowGen_diag_monomial {r n : ℕ} (a : Fin r) (m : Fin r × Fin n →₀ ℕ) (c : ℂ) :
    rowGen ℂ a a (monomial m c) =
      Polynomial.C (monomial m c) * (1 + Polynomial.X) ^ (Finsupp.weight (wa a) m) := by
  classical
  have hw : Finsupp.weight (wa a) m = ∑ v ∈ m.support, wa (n := n) a v * m v := by
    rw [Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl (fun v _ => by rw [smul_eq_mul, mul_comm])
  simp only [monomial_eq, Finsupp.prod, map_mul, map_prod, map_pow, rowGen_diag_C, rowGen_diag_X, mul_pow,
    Finset.prod_mul_distrib, ← pow_mul, Finset.prod_pow_eq_pow_sum, hw]
  ring

theorem rowDiv_diag {r n : ℕ} (a : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) ℂ) (H : ℤ)
    (hf : IsWeightedHomogeneous (rw1 a) f H) :
    rowDiv ℂ a a k f = ((H.toNat.choose k : ℕ) : ℂ) • f := by
  classical
  unfold rowDiv
  conv_lhs => rw [f.as_sum]
  rw [map_sum, Polynomial.finset_sum_coeff]
  conv_rhs => rw [f.as_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [rowGen_diag_monomial, Polynomial.coeff_C_mul, Polynomial.coeff_one_add_X_pow]
  have hw := hf (mem_support_iff.mp hm)
  rw [weight_rw1_eq_weight_wa] at hw
  have hw' : Finsupp.weight (wa a) m = H.toNat := by omega
  rw [hw', MvPolynomial.smul_eq_C_mul, map_natCast, mul_comm]

private theorem isWeightedHomogeneous_coeff_mul_rw1 {r n : ℕ} (c : Fin r) (s D E : ℤ) (P Q : Polynomial (MvPolynomial (Fin r × Fin n) ℂ))
    (hP : ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) (P.coeff j) (D + j * s))
    (hQ : ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) (Q.coeff j) (E + j * s)) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((P * Q).coeff j) ((D + E) + j * s) := by
  rw [Polynomial.coeff_mul, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun x hx => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hx' : x.1 + x.2 = j := by simpa using hx
  rw [show (D + E) + (j : ℤ) * s = (D + (x.1 : ℤ) * s) + (E + (x.2 : ℤ) * s) by
    rw [← hx']
    push_cast
    ring]
  exact (hP x.1).mul (hQ x.2)

private theorem isWeightedHomogeneous_coeff_one_rw1 {r n : ℕ} (c : Fin r) (s : ℤ) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((1 : Polynomial (MvPolynomial (Fin r × Fin n) ℂ)).coeff j) (0 + j * s) := by
  by_cases hj : j = 0
  · subst hj
    simpa using isWeightedHomogeneous_one ℂ (rw1 (n := n) c)
  · rw [show (1 : Polynomial (MvPolynomial (Fin r × Fin n) ℂ)).coeff j = 0 by simp [Polynomial.coeff_one, hj]]
    exact isWeightedHomogeneous_zero ℂ _ _

private theorem isWeightedHomogeneous_coeff_rowGen_X {r n : ℕ} (a b c : Fin r) (v : Fin r × Fin n) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((rowGen ℂ a b (X v : MvPolynomial (Fin r × Fin n) ℂ)).coeff j)
      (rw1 c v + j * ((if a = c then 1 else 0) - (if b = c then 1 else 0))) := by
  have hX : ∀ u : Fin r × Fin n, IsWeightedHomogeneous (rw1 c) (X u : MvPolynomial (Fin r × Fin n) ℂ) (rw1 c u) :=
    fun u => isWeightedHomogeneous_X ℂ _ u
  have hdeg : ∀ (φ : MvPolynomial (Fin r × Fin n) ℂ) (d d' : ℤ), d = d' →
      IsWeightedHomogeneous (rw1 c) φ d → IsWeightedHomogeneous (rw1 c) φ d' := fun φ d d' e h => e ▸ h
  unfold rowGen
  rw [aeval_X]
  by_cases hv : v.1 = b
  · rw [if_pos hv]
    have hr : ∀ u : Fin r × Fin n, rw1 c u = if u.1 = c then 1 else 0 := fun u => by
      unfold rw1 wa
      split_ifs <;> simp
    rcases j with _ | _ | k
    · rw [Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_mul_zero, add_zero]
      exact hdeg _ _ _ (by simp) (hX v)
    · rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C_zero]
      refine hdeg _ _ _ ?_ (hX (a, v.2))
      rw [hr, hr, hv]
      dsimp only
      split_ifs <;> norm_num
    · rw [Polynomial.coeff_add, Polynomial.coeff_C, if_neg (by omega), zero_add, Polynomial.coeff_X_mul,
        Polynomial.coeff_C, if_neg (by omega)]
      exact isWeightedHomogeneous_zero ℂ _ _
  · rw [if_neg hv, add_zero, Polynomial.coeff_C]
    by_cases hj : j = 0
    · rw [if_pos hj]
      subst hj
      exact hdeg _ _ _ (by simp) (hX v)
    · rw [if_neg hj]
      exact isWeightedHomogeneous_zero ℂ _ _

private theorem isWeightedHomogeneous_coeff_pow_rw1 {r n : ℕ} (c : Fin r) (s D : ℤ) (P : Polynomial (MvPolynomial (Fin r × Fin n) ℂ))
    (hP : ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) (P.coeff j) (D + j * s)) (e : ℕ) :
    ∀ j : ℕ, IsWeightedHomogeneous (rw1 c) ((P ^ e).coeff j) ((e : ℤ) * D + j * s) := by
  induction e with
  | zero =>
    intro j
    simpa using isWeightedHomogeneous_coeff_one_rw1 (n := n) c s j
  | succ e ih =>
    intro j
    rw [pow_succ, show ((e + 1 : ℕ) : ℤ) * D + (j : ℤ) * s = ((e : ℤ) * D + D) + j * s by push_cast; ring]
    exact isWeightedHomogeneous_coeff_mul_rw1 c s _ _ (P ^ e) P ih hP j

private theorem isWeightedHomogeneous_coeff_prod_rowGen_X_pow {r n : ℕ} (a b c : Fin r) (m : Fin r × Fin n →₀ ℕ) (t : Finset (Fin r × Fin n)) :
    ∀ j : ℕ, IsWeightedHomogeneous (rw1 c)
      ((∏ v ∈ t, (rowGen ℂ a b (X v : MvPolynomial (Fin r × Fin n) ℂ)) ^ (m v)).coeff j)
      ((∑ v ∈ t, (m v : ℤ) * rw1 c v) + j * ((if a = c then 1 else 0) - (if b = c then 1 else 0))) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · intro j
    simpa using isWeightedHomogeneous_coeff_one_rw1 (n := n) c _ j
  · intro v t hv ih j
    rw [Finset.prod_insert hv, Finset.sum_insert hv]
    exact isWeightedHomogeneous_coeff_mul_rw1 c _ _ _ _ _ (isWeightedHomogeneous_coeff_pow_rw1 c _ _ _ (isWeightedHomogeneous_coeff_rowGen_X a b c v) (m v)) ih j

private theorem isWeightedHomogeneous_coeff_rowGen {r n : ℕ} (a b c : Fin r) (g : MvPolynomial (Fin r × Fin n) ℂ) (H : ℤ)
    (hg : IsWeightedHomogeneous (rw1 c) g H) (j : ℕ) :
    IsWeightedHomogeneous (rw1 c) ((rowGen ℂ a b g).coeff j)
      (H + j * ((if a = c then 1 else 0) - (if b = c then 1 else 0))) := by
  classical
  rw [g.as_sum, map_sum, Polynomial.finset_sum_coeff, ← mem_weightedHomogeneousSubmodule]
  refine Submodule.sum_mem _ fun m hm => ?_
  rw [mem_weightedHomogeneousSubmodule]
  have hw := hg (mem_support_iff.mp hm)
  have hC : rowGen ℂ a b (C (coeff m g) : MvPolynomial (Fin r × Fin n) ℂ) = Polynomial.C (C (coeff m g)) := by
    unfold rowGen
    rw [aeval_C, Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod]
  simp only [map_pow]
  rw [hC, Polynomial.coeff_C_mul]
  have hp := isWeightedHomogeneous_coeff_prod_rowGen_X_pow a b c m m.support j
  have hsum : (∑ v ∈ m.support, (m v : ℤ) * rw1 c v) = H := by
    rw [← hw, Finsupp.weight_apply, Finsupp.sum]
    exact Finset.sum_congr rfl (fun v _ => by rw [nsmul_eq_mul])
  rw [hsum] at hp
  rw [MvPolynomial.C_mul', ← mem_weightedHomogeneousSubmodule]
  exact Submodule.smul_mem _ _ ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hp)

theorem word_homog {r n : ℕ} (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : ∀ c : Fin r, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) f H) :
    ∀ c : Fin r, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) (applyWord ℂ w f) H := by
  induction w with
  | nil => exact hf
  | cons x w ih =>
    intro c
    obtain ⟨H, hH⟩ := ih c
    exact ⟨_, isWeightedHomogeneous_coeff_rowGen x.1 x.2.1 c (applyWord ℂ w f) H hH x.2.2⟩

theorem word_reduce {r n : ℕ} (f : MvPolynomial (Fin r × Fin n) ℂ)
    (hf : ∀ c : Fin r, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) f H) (w : List (Fin r × Fin r × ℕ)) :
    ∃ w', OffDiag w' ∧ ∃ z : ℂ, applyWord ℂ w f = z • applyWord ℂ w' f := by
  have hsm : ∀ (a b : Fin r) (k : ℕ) (z : ℂ) (g : MvPolynomial (Fin r × Fin n) ℂ),
      rowDiv ℂ a b k (z • g) = z • rowDiv ℂ a b k g := by
    intro a b k z g
    unfold rowDiv
    rw [map_smul, Polynomial.coeff_smul]
  induction w with
  | nil => exact ⟨[], fun x hx => by simp at hx, 1, by rw [one_smul]⟩
  | cons x w ih =>
    obtain ⟨w', hw', z, hz⟩ := ih
    obtain ⟨a, b, k⟩ := x
    by_cases hab : a = b
    · subst hab
      obtain ⟨H, hH⟩ := word_homog w' f hf a
      refine ⟨w', hw', z * ((H.toNat.choose k : ℕ) : ℂ), ?_⟩
      show rowDiv ℂ a a k (applyWord ℂ w f) = _
      rw [hz, hsm, rowDiv_diag a k _ H hH, smul_smul]
    · refine ⟨(a, b, k) :: w', ?_, z, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hab
        · exact hw' y hy
      · show rowDiv ℂ a b k (applyWord ℂ w f) = z • rowDiv ℂ a b k (applyWord ℂ w' f)
        rw [hz, hsm]

theorem word_adj {r n : ℕ} (w : List (Fin r × Fin r × ℕ)) :
    ∀ F G : MvPolynomial (Fin r × Fin n) ℂ,
      fockF (applyWord ℂ w F) G = fockF F (applyWord ℂ (transposeWord w) G) := by
  induction w with
  | nil => intro F G; rfl
  | cons x w ih =>
    intro F G
    rw [applyWord_cons, Formalism.GradedWeylDivisibility.lfockq_adjC, ih]
    congr 1
    unfold transposeWord
    rw [List.map_cons, List.reverse_cons, applyWord_append]
    rfl

theorem transposeWord_transposeWord {r : ℕ} (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (transposeWord w) = w := by
  unfold transposeWord
  simp [List.map_map, Function.comp_def, List.map_reverse]

theorem transposeWord_liftWord {n N : ℕ} (h : n + 1 = N) (w : List (Fin n × Fin n × ℕ)) :
    transposeWord (liftWord h w) = liftWord h (transposeWord w) := by
  unfold transposeWord liftWord
  simp [List.map_map, Function.comp_def, List.map_reverse]

theorem offDiag_transpose {r : ℕ} {w : List (Fin r × Fin r × ℕ)} (hw : OffDiag w) :
    OffDiag (transposeWord w) := by
  intro x hx
  unfold transposeWord at hx
  simp only [List.mem_map, List.mem_reverse] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact fun h => hw y hy h.symm

theorem natW_anti {n : ℕ} (sg : DomWeight n) : Antitone sg.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by linarith [sg.anti hij])

theorem eqv_word (hD : EqvDiv) {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (w : List (Fin n × Fin n × ℕ)) (hw : OffDiag w) (s : MvPolynomial (Fin n × Fin n) ℂ)
    (hs : s ∈ nablaSq ℂ n mu) :
    applyWord ℂ w s ∈ nablaSq ℂ n mu ∧ φ (applyWord ℂ w s) = applyWord ℂ (liftWord h w) (φ s) := by
  induction w with
  | nil => exact ⟨hs, rfl⟩
  | cons x w ih =>
    have hx : x.1 ≠ x.2.1 := hw x (by simp)
    obtain ⟨hm, he⟩ := ih (fun y hy => hw y (by simp [hy]))
    refine ⟨?_, ?_⟩
    · rw [applyWord_cons]
      exact Formalism.GradedWeylDivisibility.rowDivStable ℂ n n mu.natW x.1 x.2.1 x.2.2 _ hm
    · rw [applyWord_cons, hD n N h mu lam φ hφ x.1 x.2.1 hx x.2.2 _ hm, he]
      rfl

end Fock6

open Fock6 in
theorem fockDetect_of (h3 : PI.HwIrred) (hD : EqvDiv) : FockDetect := by
  intro n N h lam sg _ io0 hEqv hext u hu hort
  set E : MvPolynomial (Fin n × Fin n) ℂ := extremal ℂ n sg with hE
  have hEmem : E ∈ nablaSq ℂ n sg := hwMem ℂ n n le_rfl sg.natW (natW_anti sg)
  have hErow : ∀ c : Fin n, ∃ H : ℤ, IsWeightedHomogeneous (rw1 c) E H := by
    intro c
    refine ⟨((rowNu (r := n) sg.natW c : ℕ) : ℤ), fun m hm => ?_⟩
    have := hwRowWeight ℂ n n le_rfl sg.natW (natW_anti sg) hm
    rw [weight_indicator_eq_degree]
    exact congrArg (fun v : Fin n → ℕ => ((v c : ℕ) : ℤ)) this

  have key : ∀ w, OffDiag w → fockF (io0 u) (io0 (applyWord ℂ w E)) = 0 := by
    intro w hw
    rw [(eqv_word hD h sg lam io0 hEqv w hw E hEmem).2, hext]
    have e := word_adj (transposeWord (liftWord h w)) (io0 u) (xi ℂ h lam sg)
    rw [transposeWord_transposeWord, transposeWord_liftWord] at e
    rw [← e]
    exact hort _ (offDiag_transpose hw)

  let S : Set (MvPolynomial (Fin n × Fin n) ℂ) := {f | ∃ w, OffDiag w ∧ f = applyWord ℂ w E}
  have hspan : u ∈ Submodule.span ℂ S := by
    have hu' : u ∈ delSq ℂ n sg := (h3 n sg).1 ▸ hu
    refine (Submodule.span_le.mpr ?_) hu'
    rintro _ ⟨w, rfl⟩
    obtain ⟨w', hw', z, hz⟩ := word_reduce E hErow w
    show applyWord ℂ w E ∈ Submodule.span ℂ S
    rw [hz]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨w', hw', rfl⟩)

  let P : Submodule ℂ (MvPolynomial (Fin n × Fin n) ℂ) :=
    { carrier := {y | fockF (io0 u) (io0 y) = 0}
      zero_mem' := by simp [fockF]
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_ofPred_eq, map_add] at *
        unfold fockF at *
        rw [← zero_add (0 : ℂ)]
        nth_rewrite 1 [← ha]
        rw [← hb, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        simp only [coeff_add, star_add]
        ring
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_ofPred_eq, map_smul] at *
        unfold fockF at *
        have : ∑ m ∈ (io0 u).support, (io0 u).coeff m * star ((c • io0 a).coeff m) *
            ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) =
            star c * ∑ m ∈ (io0 u).support, (io0 u).coeff m * star ((io0 a).coeff m) *
              ((∏ k ∈ m.support, (m k).factorial : ℕ) : ℂ) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          simp only [coeff_smul, smul_eq_mul, star_mul']
          ring
        rw [this, ha, mul_zero] }
  have hSP : Submodule.span ℂ S ≤ P := by
    rw [Submodule.span_le]
    rintro _ ⟨w, hw, rfl⟩
    exact key w hw
  have h0 : fockF (io0 u) (io0 u) = 0 := hSP hspan
  by_contra hne
  have := (fockPos _ (io0 u) hne).1
  rw [h0] at this
  simp at this

end PI.WGL
