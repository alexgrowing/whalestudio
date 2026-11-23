import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.CoeffRowActDiagA
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinBranching.StepACleared

noncomputable section

namespace PI.WGB

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

variable {n : ℕ}

def mStarA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) : Fin (n + 1) × Fin (n + 1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v =>
    Fin.lastCases (Fin.lastCases (ν (Fin.last n)) (fun k => ν (Fin.castSucc k) - kap k) v.2)
      (fun a => Fin.lastCases 0 (fun k => if k = a then kap a else 0) v.2) v.1

@[simp] theorem mStarA_cc (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (a k : Fin n) :
    mStarA kap ν (Fin.castSucc a, Fin.castSucc k) = if k = a then kap a else 0 := by
  simp [mStarA]

@[simp] theorem mStarA_cl (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (a : Fin n) :
    mStarA kap ν (Fin.castSucc a, Fin.last n) = 0 := by
  simp [mStarA]

@[simp] theorem mStarA_lc (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (k : Fin n) :
    mStarA kap ν (Fin.last n, Fin.castSucc k) = ν (Fin.castSucc k) - kap k := by
  simp [mStarA]

@[simp] theorem mStarA_ll (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) :
    mStarA kap ν (Fin.last n, Fin.last n) = ν (Fin.last n) := by
  simp [mStarA]

def IsDPtA (x : Fin (n + 1) × Fin (n + 1) → ℂ) : Prop :=
  ∀ a j : Fin (n + 1), a.val < n → a ≠ j → x (a, j) = 0

theorem mono_eq_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) (m : Fin (n + 1) × Fin (n + 1) →₀ ℕ)
    (hm : m ∈ g.support) (hne : ∏ v, x v ^ m v ≠ 0) : m = mStarA kap ν := by
  have hz : ∀ v, x v = 0 → m v = 0 := by
    intro v hv
    by_contra h
    exact hne (Finset.prod_eq_zero (Finset.mem_univ v) (by rw [hv, zero_pow h]))
  have htop : ∀ (a : Fin n) (s : Fin (n + 1)), s ≠ Fin.castSucc a → m (Fin.castSucc a, s) = 0 :=
    fun a s hs => hz _ (hx _ _ (by simp) (Ne.symm hs))
  have hdiag : ∀ a : Fin n, m (Fin.castSucc a, Fin.castSucc a) = kap a := by
    intro a
    rw [← hrow m hm a, Finset.sum_eq_single (Fin.castSucc a)]
    · intro s _ hs
      exact htop a s hs
    · simp
  have hcolsum : ∀ j, ∑ ρ, m (ρ, j) = ν j := by
    intro j
    rw [← lhwline_weight_col, hcol (mem_support_iff.mp hm)]
  ext ⟨ρ, s⟩
  induction ρ using Fin.lastCases with
  | last =>
    induction s using Fin.lastCases with
    | last =>
      have h := hcolsum (Fin.last n)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_zero (fun a _ => htop a _ (Fin.castSucc_lt_last a).ne'),
        zero_add] at h
      rw [mStarA_ll, h]
    | cast k =>
      have h := hcolsum (Fin.castSucc k)
      rw [Fin.sum_univ_castSucc, Finset.sum_eq_single k] at h
      · rw [hdiag] at h
        rw [mStarA_lc]
        omega
      · intro b _ hb
        exact htop b _ (fun e => hb (Fin.castSucc_injective _ e).symm)
      · simp
  | cast a =>
    induction s using Fin.lastCases with
    | last =>
      rw [mStarA_cl]
      exact htop a _ (Fin.castSucc_lt_last a).ne'
    | cast k =>
      rw [mStarA_cc]
      split_ifs with hka
      · subst hka
        exact hdiag k
      · exact htop a _ (fun e => hka (Fin.castSucc_injective _ e))

theorem eval_D_A (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (g : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hcol : IsWeightedHomogeneous (colW (n + 1) (n + 1)) g ν)
    (hrow : ∀ m ∈ g.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kap a)
    (x : Fin (n + 1) × Fin (n + 1) → ℂ) (hx : IsDPtA x) :
    eval x g = coeff (mStarA kap ν) g * ∏ v, x v ^ (mStarA kap ν) v := by
  rw [MvPolynomial.eval_eq']
  by_cases hs : mStarA kap ν ∈ g.support
  · rw [Finset.sum_eq_single (mStarA kap ν)]
    · intro m hm hne
      by_contra hz
      have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
      exact hne (mono_eq_A kap ν g hcol hrow x hx m hm hprod)
    · intro h
      exact absurd hs h
  · have hc : coeff (mStarA kap ν) g = 0 := by
      by_contra h
      exact hs (MvPolynomial.mem_support_iff.mpr h)
    rw [hc, zero_mul]
    refine Finset.sum_eq_zero fun m hm => ?_
    by_contra hz
    have hprod : ∏ v, x v ^ m v ≠ 0 := fun h0 => hz (by rw [h0, mul_zero])
    exact hs (mono_eq_A kap ν g hcol hrow x hx m hm hprod ▸ hm)

def kapA (lam : DomWeight (n + 1)) (mu : DomWeight n) (a : Fin n) : ℕ := (mu.w a - lam.detShift).toNat

theorem props_A (lam : DomWeight (n + 1)) (mu : DomWeight n) (f : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)
    (hf : f ∈ nablaSq ℂ (n + 1) lam) (hfix : IsFixedW rfl lam mu f) :
    IsWeightedHomogeneous (colW (n + 1) (n + 1)) f lam.natW ∧ RInvA (fun x => eval x f) ∧
      lhwline_CInv (fun x => eval x f) ∧
      ∀ m ∈ f.support, ∀ a : Fin n, ∑ s, m (Fin.castSucc a, s) = kapA lam mu a := by
  refine ⟨(lsat_mem_dualWeyl.mp hf).1, ?_, ?_, ?_⟩
  · intro x a b t hab hb
    have ha : a.val < n := lt_trans hab hb
    have h1 : a = Fin.castSucc ⟨a.val, ha⟩ := Fin.ext rfl
    have h2 : b = Fin.castSucc ⟨b.val, hb⟩ := Fin.ext rfl
    simp only
    rw [h1, h2]
    exact fixed_rowOp_A lam mu f hfix _ _ (by rw [Fin.lt_def] at hab ⊢; exact hab) t x
  · exact lhwline_CInv_of f (fun l j hlj c => ((dualWeylPoint ℂ (n + 1) (n + 1) lam.natW f).mp hf).2 l j hlj c)
  · intro m hm a
    have := fixed_rowDeg_A lam mu f hfix m hm a
    unfold kapA
    omega

def mkPtA (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : Fin (n + 1) × Fin (n + 1) → ℂ :=
  fun v => Fin.lastCases (z v.2) (fun a => Fin.lastCases 0 (fun k => if k = a then dv a else 0) v.2) v.1

theorem mkPtA_D (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) : IsDPtA (mkPtA dv z) := by
  intro a j ha hne
  obtain ⟨a', rfl⟩ : ∃ a' : Fin n, a = Fin.castSucc a' := ⟨⟨a.val, ha⟩, Fin.ext rfl⟩
  induction j using Fin.lastCases with
  | last => simp [mkPtA]
  | cast k =>
    simp only [mkPtA, Fin.lastCases_castSucc]
    rw [if_neg]
    rintro rfl
    exact hne rfl

theorem prod_mkPtA (kap : Fin n → ℕ) (ν : Fin (n + 1) → ℕ) (dv : Fin n → ℂ) (z : Fin (n + 1) → ℂ) :
    ∏ v, mkPtA dv z v ^ (mStarA kap ν) v =
      (∏ a, dv a ^ kap a) * (∏ k : Fin n, z (Fin.castSucc k) ^ (ν (Fin.castSucc k) - kap k)) *
        z (Fin.last n) ^ ν (Fin.last n) := by
  have hpw : ∀ a' k : Fin n, (if k = a' then dv a' else 0) ^ (if k = a' then kap a' else 0) =
      if k = a' then dv a' ^ kap a' else 1 := by
    intro a' k
    split_ifs <;> simp
  rw [Fintype.prod_prod_type]
  simp [Fin.prod_univ_castSucc, mkPtA, hpw, mul_assoc]

end PI.WGB
