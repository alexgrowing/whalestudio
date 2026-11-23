import Formalism.ThetaLogCoordinates.FockResolutionOnto.FockMonomialProofs.LatDefs
import Formalism.ThetaLogCoordinates.FockResolutionOnto.MulEarlyModP
import Formalism.ThetaLogCoordinates.TraceIsometryWeights.DischargeHeightBound

namespace Formalism.InvariantFactorPaths.L4

open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset

section LatM
variable {p : ℕ} [Fact p.Prime] {K : ℕ}

section general
variable {r : ℕ} [NeZero r]

theorem mem_restrictedLattice_of_mem (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (o : ℕ)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hY : h ∈ Y p (setLast LL o) J M)
    (hi : h ∈ IntPol p (Fin (K + 1) × Fin r)) : initPart (Fin.last K, ρ) 0 h ∈ M2 p LL J M ρ := by
  unfold M2
  exact Submodule.mem_iSup_of_mem o (Submodule.mem_map.2 ⟨h, Submodule.mem_inf.2 ⟨hY, hi⟩, rfl⟩)

theorem restrictedLattice_le (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (S : Submodule ℤ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]))
    (hS : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
      initPart (Fin.last K, ρ) 0 h ∈ S) : M2 p LL J M ρ ≤ S := by
  unfold M2
  refine iSup_le fun o => ?_
  intro z hz
  obtain ⟨h, hh, rfl⟩ := Submodule.mem_map.1 hz
  obtain ⟨hY, hi⟩ := Submodule.mem_inf.1 hh
  exact hS o h hY hi

theorem restrictedLattice_map_le (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (T : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hT : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
      T (initPart (Fin.last K, ρ) 0 h) ∈ M2 p LL J M ρ) : ∀ z ∈ M2 p LL J M ρ, T z ∈ M2 p LL J M ρ := by
  intro z hz
  have hle : M2 p LL J M ρ ≤ (M2 p LL J M ρ).comap (T.restrictScalars ℤ_[p]) :=
    restrictedLattice_le LL J M ρ _ (fun o h hY hi => hT o h hY hi)
  exact hle hz

theorem restrictedLattice_zpClosed (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) :
    ZpClosed p (M2 p LL J M ρ).toAddSubgroup := by
  intro a ha x hx
  exact (M2 p LL J M ρ).smul_mem (⟨a, ha⟩ : ℤ_[p]) hx

theorem pow_intertwine {V : Type} [AddCommGroup V] [Module ℚ_[p] V] (R A B : V →ₗ[ℚ_[p]] V)
    (h : ∀ x, R (A x) = B (R x)) (k : ℕ) (x : V) : R ((A ^ k) x) = (B ^ k) (R x) := by
  induction k generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Module.End.mul_apply]

theorem restrictedLattice_divided_power (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (A B : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (k : ℕ)
    (hAB : ∀ x, resL p (Fin.last K, ρ) 0 (A x) = B (resL p (Fin.last K, ρ) 0 x))
    (hint : ∀ x ∈ IntPol p (Fin (K + 1) × Fin r),
      ((k.factorial : ℚ_[p]))⁻¹ • (A ^ k) x ∈ IntPol p (Fin (K + 1) × Fin r))
    (hY : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, ∃ o' : ℕ, (A ^ k) h ∈ Y p (setLast LL o') J M) :
    ∀ z ∈ M2 p LL J M ρ, ((k.factorial : ℚ_[p]))⁻¹ • (B ^ k) z ∈ M2 p LL J M ρ := by
  intro z hz
  have key : ∀ o : ℕ, ∀ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) →
      (((k.factorial : ℚ_[p]))⁻¹ • (B ^ k)) (initPart (Fin.last K, ρ) 0 h) ∈ M2 p LL J M ρ := by
    intro o h hh hi
    obtain ⟨o', ho'⟩ := hY o h hh
    have e1 : (B ^ k) (initPart (Fin.last K, ρ) 0 h) = initPart (Fin.last K, ρ) 0 ((A ^ k) h) :=
      (pow_intertwine (resL p (Fin.last K, ρ) 0) A B hAB k h).symm
    have e2 : initPart (Fin.last K, ρ) 0 (((k.factorial : ℚ_[p]))⁻¹ • (A ^ k) h)
        = ((k.factorial : ℚ_[p]))⁻¹ • initPart (Fin.last K, ρ) 0 ((A ^ k) h) :=
      (resL p (Fin.last K, ρ) 0).map_smul _ _
    rw [LinearMap.smul_apply, e1, ← e2]
    exact mem_restrictedLattice_of_mem LL J M ρ o' _ (Submodule.smul_mem _ _ ho') (hint h hi)
  have := restrictedLattice_map_le LL J M ρ (((k.factorial : ℚ_[p]))⁻¹ • (B ^ k)) key z hz
  simpa only [LinearMap.smul_apply] using this

private theorem glAct_mem_yCond_r {N : ℕ} (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) (a b : Fin r) :
    ∀ x ∈ YCond p (r := r) LL j Mt, glAct p LL j a b x ∈ YCond p LL j Mt := by
  intro x hx
  have hle : YCond p (r := r) LL j Mt ≤ (YCond p LL j Mt).comap (glAct p LL j a b) := by
    unfold YCond
    exact sSup_le fun S hS y hy => le_sSup hS (hS.2 a b y hy)
  exact hle hx

private theorem yCond_of_K_succ_le (LL : Letters (K + 1)) (j : ℕ) (Mt : WithTop ℤ) (hj : K + 1 ≤ j) :
    YCond p (r := r) LL j Mt = YCond p LL (K + 1) Mt := by
  have hg : ∀ c d : Fin r, glAct p LL j c d = glAct p LL (K + 1) c d := by
    intro c d
    unfold glAct
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (i : ℕ) < K + 1 := i.isLt
    have h2 : (i : ℕ) < j := by omega
    simp only [h1, h2, ↓reduceIte]
  have hw : ∀ m : Fin (K + 1) × Fin r →₀ ℕ, wt LL j 0 m = wt LL (K + 1) 0 m := by
    intro m
    unfold wt
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (i : ℕ) < K + 1 := i.isLt
    have h2 : (i : ℕ) < j := by omega
    simp only [h1, h2, ↓reduceIte]
  unfold YCond GlStable
  simp_rw [hg, hw]

theorem glAct_y (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c d : Fin r) :
    ∀ h ∈ Y p LL J M, glAct p LL (K + 1) c d h ∈ Y p LL J M := by
  intro h hh
  rw [Y, Submodule.mem_inf, Submodule.mem_iInf] at hh ⊢
  refine ⟨glAct_pol LL LL (K + 1) c d hh.1, fun k => ?_⟩
  have hk := hh.2 k
  by_cases hJ : J k ≤ K + 1
  · rw [glAct_split LL (J k) (K + 1) c d, LinearMap.add_apply]
    exact (YCond p LL (J k) (M k)).add_mem (glAct_mem_yCond_r LL (J k) (M k) c d h hk)
      (ops_ycond LL (J k) (M k) _ (glRest_mem LL (J k) (K + 1) hJ c d) h hk)
  · rw [yCond_of_K_succ_le LL (J k) (M k) (by omega)] at hk ⊢
    exact glAct_mem_yCond_r LL (K + 1) (M k) c d h hk

private theorem multiDeg_setLast_pred_of_add_single (LL : Letters (K + 1)) (o : ℕ) (a : Fin r) (m : Fin (K + 1) × Fin r →₀ ℕ)
    (hm : MultiDeg (setLast LL o) (m + Finsupp.single (Fin.last K, a) 1)) :
    MultiDeg (setLast LL (o - 1)) m := by
  intro i
  have h := hm i
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Finsupp.single_apply, Prod.mk.injEq] at h
  by_cases hi : i = Fin.last K
  · subst hi
    simp [setLast] at h ⊢
    omega
  · have hi' : Fin.last K ≠ i := Ne.symm hi
    simp [setLast, hi, hi'] at h ⊢
    exact h

theorem dW_y (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (a : Fin r) (o : ℕ) : ∀ h ∈ Y p (setLast LL o) J M, dW p K a h ∈ Y p (setLast LL (o - 1)) J M := by
  intro h hh
  rw [Y, Submodule.mem_inf, Submodule.mem_iInf] at hh ⊢
  refine ⟨?_, fun k => ?_⟩
  · have hP := hh.1
    simp only [Pol, MvPolynomial.mem_restrictSupport_iff] at hP ⊢
    intro m hm
    have hm' : coeff m (pderiv (Fin.last K, a) h) ≠ 0 := mem_support_iff.1 hm
    rw [coeff_pderiv] at hm'
    have hs : m + Finsupp.single (Fin.last K, a) 1 ∈ h.support := mem_support_iff.2 (left_ne_zero_of_mul hm')
    exact multiDeg_setLast_pred_of_add_single LL o a m (hP hs)
  · have hk := hh.2 k
    rw [yCond_setLast] at hk ⊢
    by_cases hJ : J k ≤ K
    · exact ops_ycond LL (J k) (M k) (dW p K a) (FockB.pderiv_mem (by simp; omega)) h hk
    · rw [yCond_of_K_succ_le LL (J k) (M k) (by omega)] at hk ⊢
      exact ycond_pderiv LL hv (M k) a h hk

theorem dW_pow_y (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (a : Fin r) (o k : ℕ) :
    ∀ h ∈ Y p (setLast LL o) J M, ((dW p K a) ^ k) h ∈ Y p (setLast LL (o - k)) J M := by
  intro h hh
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ← Nat.sub_sub]
    exact dW_y LL hv J M a (o - k) _ ih

private theorem yCond_mono' {N : ℕ} (LL : Letters N) (j : ℕ) {Mt Mt' : WithTop ℤ} (hM : Mt ≤ Mt') :
    YCond p (r := r) LL j Mt ≤ YCond p LL j Mt' := by
  unfold YCond
  refine sSup_le_sSup fun S hS => ⟨hS.1.trans ?_, hS.2⟩
  exact MvPolynomial.restrictSupport_mono (R := ℚ_[p]) (fun m hm => le_trans hm hM)

theorem uop_y (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ)
    (c : ℤ) (k0 : Fin q) (hk0 : K + 1 ≤ J k0) (hc : M k0 = ((c : ℤ) : WithTop ℤ))
    (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (a : Fin r) (o : ℕ) :
    ∀ h ∈ Y p (setLast LL o) J M, Uop p LL c univ a h ∈ Y p (setLast LL (o + 1)) J M := by
  intro h hh
  rw [Y, Submodule.mem_inf, Submodule.mem_iInf] at hh ⊢
  refine ⟨raising_degree_holds p K r LL c univ a o h hh.1, fun k => ?_⟩
  have hk := hh.2 k
  rw [yCond_setLast] at hk ⊢
  by_cases hJ : J k ≤ K
  · exact raising_keeps_early_letters p K r LL c univ a (J k) (M k) hJ h hk
  · have h0 := hh.2 k0
    rw [yCond_setLast, yCond_of_K_succ_le LL (J k0) (M k0) hk0, hc] at h0
    have h1 := raising_keeps_last_letter p K r LL c a hv h h0
    rw [yCond_of_K_succ_le LL (J k) (M k) (by omega)]
    have hle : ((c : ℤ) : WithTop ℤ) ≤ M k := by
      rw [← hc]
      exact hmin k (by omega)
    exact yCond_mono' LL (K + 1) hle h1

theorem uop_pow_y (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (c : ℤ) (k0 : Fin q) (hk0 : K + 1 ≤ J k0) (hc : M k0 = ((c : ℤ) : WithTop ℤ))
    (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k) (a : Fin r) (o k : ℕ) :
    ∀ h ∈ Y p (setLast LL o) J M, ((Uop p LL c univ a) ^ k) h ∈ Y p (setLast LL (o + k)) J M := by
  intro h hh
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ← add_assoc]
    exact uop_y LL hv J M c k0 hk0 hc hmin a (o + k) _ ih

theorem glAct_pow_y (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c d : Fin r) (k : ℕ) :
    ∀ h ∈ Y p LL J M, ((glAct p LL (K + 1) c d) ^ k) h ∈ Y p LL J M := by
  intro h hh
  induction k with
  | zero => simpa using hh
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact glAct_y LL J M c d _ ih

private theorem pderiv_last_eq_zero_of_mem_pol_setLast_zero (LL : Letters (K + 1)) (d : Fin r) (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hP : y ∈ Pol p r (setLast LL 0)) : pderiv (Fin.last K, d) y = 0 := by
  rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hP
  ext m
  rw [coeff_pderiv, coeff_zero]
  have h0 : coeff (m + Finsupp.single (Fin.last K, d) 1) y = 0 := by
    by_contra hne
    have hm := hP (mem_support_iff.2 hne) (Fin.last K)
    have hle : (m + Finsupp.single (Fin.last K, d) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, d) ≤
        ∑ c, (m + Finsupp.single (Fin.last K, d) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, c) :=
      Finset.single_le_sum
        (f := fun c => (m + Finsupp.single (Fin.last K, d) 1 : Fin (K + 1) × Fin r →₀ ℕ) (Fin.last K, c))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ d)
    rw [hm] at hle
    simp [setLast] at hle
  rw [h0, zero_mul]

private theorem mem_yCond_succ_of_mem_pol_setLast_zero (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hy : y ∈ YCond p LL K Mt)
    (hP : y ∈ Pol p r (setLast LL 0)) : y ∈ YCond p LL (K + 1) Mt := by
  have hR : YCond p (r := r) LL K Mt ≤
      MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL K 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    unfold YCond
    exact sSup_le fun S hS => hS.1
  have h1 : YCond p LL K Mt ⊓ Pol p r (setLast LL 0) ≤
      MvPolynomial.restrictSupport ℚ_[p] {m | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    intro z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    have hz1' := hR hz1
    rw [Pol, MvPolynomial.mem_restrictSupport_iff] at hz2
    rw [MvPolynomial.mem_restrictSupport_iff] at hz1' ⊢
    intro m hm
    have hw := hz1' hm
    have hd := hz2 hm (Fin.last K)
    have h0 : m (Fin.last K, 0) = 0 := by
      simp [setLast] at hd
      exact hd 0
    show ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt
    rw [wt_succ LL hv, h0]
    simpa using hw
  have h2 : GlStable p LL (K + 1) (YCond p LL K Mt ⊓ Pol p r (setLast LL 0)) := by
    intro c d z hz
    obtain ⟨hz1, hz2⟩ := Submodule.mem_inf.1 hz
    rw [glAct_succ LL hv, pderiv_last_eq_zero_of_mem_pol_setLast_zero LL d z hz2, mul_zero, add_zero]
    exact Submodule.mem_inf.2 ⟨glAct_mem_yCond_r LL K Mt c d z hz1, glAct_pol LL (setLast LL 0) K c d hz2⟩
  have hS : YCond p LL K Mt ⊓ Pol p r (setLast LL 0) ≤ YCond p LL (K + 1) Mt := le_sSup ⟨h1, h2⟩
  exact hS (Submodule.mem_inf.2 ⟨hy, hP⟩)

theorem restrictedLattice_of_deg_zero (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ XSp p (setLast LL 0) J M ρ) (hi : x ∈ IntPol p (Fin (K + 1) × Fin r)) : x ∈ M2 p LL J M ρ := by
  have hfix : initPart (Fin.last K, ρ) 0 x = x := by
    have hF : x ∈ FreeOf p (Fin.last K, ρ) := by
      simp only [XSp, Submodule.mem_inf] at hx
      exact hx.1.2
    rw [FreeOf, MvPolynomial.mem_restrictSupport_iff] at hF
    ext m
    rw [coeff_initPart]
    split_ifs with hm
    · rfl
    · by_contra hne
      exact hm (hF (mem_support_iff.2 (Ne.symm hne)))
  rw [← hfix]
  refine mem_restrictedLattice_of_mem LL J M ρ 0 x ?_ hi
  simp only [XSp, Submodule.mem_inf, Submodule.mem_iInf] at hx
  obtain ⟨⟨hP, _⟩, hk⟩ := hx
  rw [Y, Submodule.mem_inf, Submodule.mem_iInf]
  refine ⟨hP, fun k => ?_⟩
  have hk' := hk k
  rw [yCond_setLast]
  by_cases hJ : K + 1 ≤ J k
  · rw [if_pos hJ, Submodule.mem_inf, yCond_setLast] at hk'
    rw [yCond_of_K_succ_le LL (J k) (M k) hJ]
    exact mem_yCond_succ_of_mem_pol_setLast_zero LL hv (M k) x hk'.1 hP
  · rw [if_neg hJ, yCond_setLast] at hk'
    exact hk'

theorem compL_deg (LL : Letters (K + 1)) (o o' : ℕ) (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p])
    (hx : x ∈ Pol p r (setLast LL o')) :
    compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) x = if o' = o then x else 0 := by
  ext m
  change MvPolynomial.coeff m (compP _ x) = _
  rw [coeff_compP]
  by_cases hm : m ∈ x.support
  · have hmd : MultiDeg (setLast LL o') m := ((MvPolynomial.mem_restrictSupport_iff ℚ_[p]).1 hx) hm
    have hs : ∑ a, m (Fin.last K, a) = o' := by
      rw [hmd (Fin.last K)]
      simp [setLast]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd (hs.symm.trans h1) h2
    · exact absurd (hs.trans h2) h1
    · simp
  · have h0 : MvPolynomial.coeff m x = 0 := by
      by_contra hne
      exact hm (MvPolynomial.mem_support_iff.2 hne)
    split_ifs <;> simp [h0]

theorem restrictedLattice_exists_lift (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r) (o : ℕ)
    (z : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hz : z ∈ M2 p LL J M ρ) (hzP : z ∈ Pol p r (setLast LL o)) :
    ∃ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h = z := by
  have hP : ∀ w ∈ M2 p LL J M ρ, ∃ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
      initPart (Fin.last K, ρ) 0 h
        = compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) w := by
    intro w hw
    unfold M2 at hw
    refine Submodule.iSup_induction _ (motive := fun w => ∃ h ∈ Y p (setLast LL o) J M,
      h ∈ IntPol p (Fin (K + 1) × Fin r) ∧ initPart (Fin.last K, ρ) 0 h
        = compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) w) hw ?_ ?_ ?_
    · intro o' w' hw'
      obtain ⟨h', hh', rfl⟩ := Submodule.mem_map.1 hw'
      obtain ⟨hY', hI'⟩ := Submodule.mem_inf.1 hh'
      have hpol : h' ∈ Pol p r (setLast LL o') := (Submodule.mem_inf.1 hY').1
      have hcomm : compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o)
            (initPart (Fin.last K, ρ) 0 h')
          = initPart (Fin.last K, ρ) 0
            (compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o) h') := by
        ext m
        change MvPolynomial.coeff m (compP _ _) = MvPolynomial.coeff m (initPart _ _ (compP _ _))
        rw [coeff_compP, coeff_initPart, coeff_initPart, coeff_compP]
        split_ifs <;> rfl
      change ∃ h ∈ Y p (setLast LL o) J M, h ∈ IntPol p (Fin (K + 1) × Fin r) ∧
        initPart (Fin.last K, ρ) 0 h = compL ℚ_[p] (fun m : Fin (K + 1) × Fin r →₀ ℕ => ∑ a, m (Fin.last K, a) = o)
          (initPart (Fin.last K, ρ) 0 h')
      rw [hcomm, compL_deg LL o o' h' hpol]
      split_ifs with ho
      · subst ho
        exact ⟨h', hY', hI', rfl⟩
      · exact ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, rfl⟩
    · refine ⟨0, Submodule.zero_mem _, Submodule.zero_mem _, ?_⟩
      rw [map_zero]
      exact (resL p (Fin.last K, ρ) 0).map_zero
    · rintro x y ⟨h1, hY1, hI1, e1⟩ ⟨h2, hY2, hI2, e2⟩
      exact ⟨h1 + h2, add_mem hY1 hY2, add_mem hI1 hI2, by rw [initPart_add, e1, e2, map_add]⟩
  obtain ⟨h, hY, hI, he⟩ := hP z hz
  refine ⟨h, hY, hI, ?_⟩
  rw [he, compL_deg LL o o z hzP, if_pos rfl]

end general

section larger
variable {s : ℕ}

theorem restrictedLattice_divStable (hU : UDivInt) (hD : DWDivInt) (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c) :
    DivStable G.E (M2 p LL J M (Fin.last s)).toAddSubgroup := by
  rw [hE]
  intro a b hab k x hx
  rw [Submodule.mem_toAddSubgroup] at hx ⊢
  cases a using Fin.cases with
  | zero =>
    cases b using Fin.cases with
    | zero => exact absurd rfl hab
    | succ j =>
      simp only [EX, Fin.cases_zero, Fin.cases_succ]
      have hne : ((Fin.last K, Fin.castSucc j) : Fin (K + 1) × Fin (s + 1)) ≠ (Fin.last K, Fin.last s) :=
        fun h => (Fin.castSucc_lt_last j).ne (congrArg Prod.snd h)
      refine restrictedLattice_divided_power LL J M (Fin.last s) (dW p K (Fin.castSucc j)) (dW p K (Fin.castSucc j)) k ?_ ?_ ?_ x hx
      · intro y
        exact resL_pderiv _ _ hne 0 y
      · intro y hy
        exact hD p K (s + 1) (Fin.castSucc j) k y hy
      · intro o h hh
        exact ⟨o - k, dW_pow_y LL hv J M (Fin.castSucc j) o k h hh⟩
  | succ i =>
    cases b using Fin.cases with
    | zero =>
      simp only [EX, Fin.cases_zero, Fin.cases_succ]
      refine restrictedLattice_divided_power LL J M (Fin.last s) (Uop p LL c univ (Fin.castSucc i))
        (Uop p LL c (univ.erase (Fin.last s)) (Fin.castSucc i)) k ?_ ?_ ?_ x hx
      · intro y
        rw [resL_apply, resL_apply]
        exact restriction_raising_holds p K (s + 1) LL c (Fin.last s) (Fin.castSucc i) y (Fin.castSucc_lt_last i).ne
      · intro y hy
        exact hU p K (s + 1) LL c univ (Fin.castSucc i) k (Finset.mem_univ _) y hy
      · intro o h hh
        exact ⟨o + k, uop_pow_y LL hv J M c k0 hk0 hc hmin (Fin.castSucc i) o k h hh⟩
    | succ j =>
      have hij : i ≠ j := fun h => hab (h ▸ rfl)
      simp only [EX, Fin.cases_succ]
      refine restrictedLattice_divided_power LL J M (Fin.last s) (glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j))
        (glAct p LL (K + 1) (Fin.castSucc i) (Fin.castSucc j)) k ?_ ?_ ?_ x hx
      · intro y
        refine resL_glAct LL (K + 1) _ _ _ 0 (fun l _ => ⟨?_, ?_⟩) y
        · exact fun h => (Fin.castSucc_lt_last i).ne (congrArg Prod.snd h)
        · exact fun h => (Fin.castSucc_lt_last j).ne (congrArg Prod.snd h)
      · intro y hy
        exact divided_integral_holds p (K + 1) (s + 1) LL (K + 1) (Fin.castSucc i) (Fin.castSucc j)
          (fun h => hij (Fin.castSucc_injective _ h)) k y hy
      · intro o h hh
        have h1 := glAct_pow_y (setLast LL o) J M (Fin.castSucc i) (Fin.castSucc j) k h hh
        rw [glAct_setLast] at h1
        exact ⟨o, h1⟩

theorem span_le_restrictedLattice (hU : UDivInt) (hD : DWDivInt) (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) {q : ℕ}
    (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (c : ℤ) (k0 : Fin q) (hk0 : K + 1 ≤ J k0)
    (hc : M k0 = ((c : ℤ) : WithTop ℤ)) (hmin : ∀ k, K + 1 ≤ J k → M k0 ≤ M k)
    (G : GlW ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]) (s + 1)) (hE : G.E = EX p LL c)
    (S : Set (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]))
    (hS : S ⊆ ((M2 p LL J M (Fin.last s)).toAddSubgroup : Set (MvPolynomial (Fin (K + 1) × Fin (s + 1)) ℚ_[p]))) :
    DeltaLat p G S ≤ (M2 p LL J M (Fin.last s)).toAddSubgroup := by
  unfold DeltaLat
  exact sInf_le ⟨hS, restrictedLattice_zpClosed LL J M (Fin.last s), restrictedLattice_divStable hU hD LL hv J M c k0 hk0 hc hmin G hE⟩

end larger

end LatM

end Formalism.InvariantFactorPaths.L4
