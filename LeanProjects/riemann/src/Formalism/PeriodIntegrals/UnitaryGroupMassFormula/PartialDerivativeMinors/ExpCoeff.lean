import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PartialDerivativeMinors.PMinorAff

noncomputable section

open scoped BigOperators
open Classical

namespace PI.EntAtD.W

open PI.EntAtD

namespace ExponentialCoefficients

variable {H : Type} [Fintype H] [DecidableEq H] {N0 N1 : ℕ}

abbrev JI (H : Type) (N0 N1 : ℕ) : Type := H × Fin N0 × Fin N1

def vX (s : Bool) (j : JI H N0 N1) : ZV H N0 N1 := ((s, j.1), j.2.1, j.2.2)

def eJ (j : JI H N0 N1) : ZV H N0 N1 →₀ ℕ :=
  Finsupp.single (vX false j) 1 + Finsupp.single (vX true j) 1

def eK (k : JI H N0 N1 → ℕ) : ZV H N0 N1 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun v => k (v.1.2, v.2))

theorem eK_apply (k : JI H N0 N1 → ℕ) (s : Bool) (t : H) (a : Fin N0) (b : Fin N1) :
    eK k ((s, t), a, b) = k (t, a, b) := by
  first
  | rfl
  | simp [eK]

theorem sum_eJ (k : JI H N0 N1 → ℕ) : ∑ j, k j • eJ j = eK k := by
  ext ⟨⟨s, t⟩, a, b⟩
  rw [eK_apply, Finsupp.finset_sum_apply, Finset.sum_eq_single (t, a, b)]
  · cases s <;> simp [eJ, vX, Finsupp.single_apply]
  · rintro ⟨t', a', b'⟩ _ hne
    simp only [eJ, vX, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
      Prod.mk.injEq]
    split_ifs <;> simp_all
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem eK_eq_iff (k : JI H N0 N1 → ℕ) (κ : ZV H N0 N1 →₀ ℕ) :
    κ = eK k ↔ (∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b)) ∧ k = fun j => κ (vX true j) := by
  constructor
  · rintro rfl
    refine ⟨fun t a b => by rw [eK_apply, eK_apply], ?_⟩
    funext ⟨t, a, b⟩
    exact (eK_apply k true t a b).symm
  · rintro ⟨h1, rfl⟩
    ext ⟨⟨s, t⟩, a, b⟩
    rw [eK_apply]
    cases s
    · exact h1 t a b
    · rfl

theorem prod_monomial' {σ ι R : Type*} [CommSemiring R] (s : Finset ι) (f : ι → σ →₀ ℕ) (a : ι → R) :
    ∏ i ∈ s, MvPowerSeries.monomial (f i) (a i) =
      MvPowerSeries.monomial (∑ i ∈ s, f i) (∏ i ∈ s, a i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [MvPowerSeries.monomial_zero_one]
  · intro i s hi ih
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPowerSeries.monomial_mul_monomial]

variable (p : ℕ) [Fact p.Prime]

theorem f_eq (S : ℂ_[p]) (ut : H → ℂ_[p]) :
    (-(S • ∑ t : H, ut t • ∑ a : Fin N0, ∑ b : Fin N1,
        (MvPowerSeries.X ((false, t), a, b) * MvPowerSeries.X ((true, t), a, b) :
          MvPowerSeries (ZV H N0 N1) ℂ_[p]))) =
      ∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1)) := by
  have key : ∀ (c : ℂ_[p]) (n : ZV H N0 N1 →₀ ℕ),
      c • (MvPowerSeries.monomial n (1 : ℂ_[p])) = MvPowerSeries.monomial n c := by
    intro c n
    rw [← map_smul, smul_eq_mul, mul_one]
  simp only [Finset.smul_sum, ← Finset.sum_neg_distrib, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ =>
    Finset.sum_congr rfl fun b _ => ?_
  rw [MvPowerSeries.X, MvPowerSeries.X, MvPowerSeries.monomial_mul_monomial, mul_one, smul_smul,
    ← neg_smul, key]
  rfl

theorem cc_zero (S : ℂ_[p]) (ut : H → ℂ_[p]) :
    MvPowerSeries.constantCoeff
      (∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1))) = 0 := by
  rw [map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_monomial, if_neg]
  intro h
  have h2 := DFunLike.congr_fun h (vX false j)
  simp [eJ, vX, Finsupp.single_apply] at h2

private theorem monomial_pow_lemma {σ R : Type*} [CommSemiring R] (n : σ →₀ ℕ) (a : R) (k : ℕ) :
    MvPowerSeries.monomial n a ^ k = MvPowerSeries.monomial (k • n) (a ^ k) := by
  induction k with
  | zero => simp [MvPowerSeries.monomial_zero_one]
  | succ k ih => rw [pow_succ, ih, MvPowerSeries.monomial_mul_monomial, succ_nsmul, pow_succ]

theorem coeff_pow (S : ℂ_[p]) (ut : H → ℂ_[p]) (κ : ZV H N0 N1 →₀ ℕ) (d : ℕ) :
    MvPowerSeries.coeff κ ((∑ j : JI H N0 N1, MvPowerSeries.monomial (eJ j) (-(S * ut j.1))) ^ d) =
      if (∀ t a b, κ ((false, t), a, b) = κ ((true, t), a, b)) ∧ ∑ j, κ (vX true j) = d then
        ((Nat.multinomial Finset.univ fun j => κ (vX true j) : ℕ) : ℂ_[p]) *
          ∏ j, (-(S * ut j.1)) ^ κ (vX true j)
      else 0 := by
  classical
  have hn : ∀ (n : ℕ) (m : ZV H N0 N1 →₀ ℕ) (c : ℂ_[p]),
      (n : MvPowerSeries (ZV H N0 N1) ℂ_[p]) * MvPowerSeries.monomial m c =
        MvPowerSeries.monomial m ((n : ℂ_[p]) * c) := by
    intro n m c
    rw [← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul]
  have hterm : ∀ k : JI H N0 N1 → ℕ,
      (Nat.multinomial Finset.univ k : MvPowerSeries (ZV H N0 N1) ℂ_[p]) *
          ∏ j, MvPowerSeries.monomial (eJ j) (-(S * ut j.1)) ^ k j =
        MvPowerSeries.monomial (eK k)
          ((Nat.multinomial Finset.univ k : ℂ_[p]) * ∏ j, (-(S * ut j.1)) ^ k j) := by
    intro k
    simp only [monomial_pow_lemma]
    rw [prod_monomial', sum_eJ, hn]
  rw [Finset.sum_pow_eq_sum_piAntidiag, map_sum]
  simp only [hterm, MvPowerSeries.coeff_monomial]
  split_ifs with h
  · rw [Finset.sum_eq_single (fun j => κ (vX true j))]
    · rw [if_pos ((eK_eq_iff _ _).2 ⟨h.1, rfl⟩)]
    · intro k _ hk
      rw [if_neg]
      intro he
      exact hk ((eK_eq_iff k κ).1 he).2
    · intro hn'
      exfalso
      apply hn'
      rw [Finset.mem_piAntidiag]
      exact ⟨h.2, fun i _ => Finset.mem_univ i⟩
  · refine Finset.sum_eq_zero fun k hk => ?_
    rw [if_neg]
    intro he
    apply h
    obtain ⟨h1, h2⟩ := (eK_eq_iff k κ).1 he
    refine ⟨h1, ?_⟩
    rw [Finset.mem_piAntidiag] at hk
    subst h2
    exact hk.1

end ExponentialCoefficients

theorem pExpCoeff : PExpCoeff := by
  intro H _ _ N0 N1 p _ S ut κ
  have hs : PowerSeries.HasSubst (∑ j : ExponentialCoefficients.JI H N0 N1,
      MvPowerSeries.monomial (ExponentialCoefficients.eJ j) (-(S * ut j.1))) :=
    PowerSeries.HasSubst.of_constantCoeff_zero (ExponentialCoefficients.cc_zero p S ut)
  rw [expS, ExponentialCoefficients.f_eq, PowerSeries.coeff_subst hs]
  simp only [ExponentialCoefficients.coeff_pow, PowerSeries.coeff_exp, smul_eq_mul]
  split_ifs with hbal
  · rw [finsum_eq_single _ (∑ j, κ (ExponentialCoefficients.vX true j)) ?_]
    · rw [if_pos ⟨hbal, rfl⟩]
      have hκ : (κ.prod fun _ k => (k.factorial : ℂ_[p])) =
          ∏ j : ExponentialCoefficients.JI H N0 N1, ((κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) ^ 2 := by
        rw [Finsupp.prod_fintype _ _ (fun _ => by simp)]
        let e : (Bool × ExponentialCoefficients.JI H N0 N1) ≃ ZV H N0 N1 :=
          { toFun := fun x => ExponentialCoefficients.vX x.1 x.2
            invFun := fun v => (v.1.1, v.1.2, v.2)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
        rw [← e.prod_comp, Fintype.prod_prod_type, Fintype.prod_bool, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun j _ => ?_
        obtain ⟨t, a, b⟩ := j
        simp only [e, Equiv.coe_fn_mk, ExponentialCoefficients.vX]
        rw [← hbal t a b, sq]
      have hR : (∏ t : H, ∏ a : Fin N0, ∏ b : Fin N1,
          ((κ ((true, t), a, b)).factorial : ℂ_[p]) * (-(S * ut t)) ^ κ ((true, t), a, b)) =
          ∏ j : ExponentialCoefficients.JI H N0 N1, ((κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) *
            (-(S * ut j.1)) ^ κ (ExponentialCoefficients.vX true j) := by
        simp only [Fintype.prod_prod_type] <;> rfl
      have hM := congrArg (Nat.cast (R := ℂ_[p]))
        (Nat.multinomial_spec Finset.univ (fun j => κ (ExponentialCoefficients.vX true j)))
      push_cast at hM
      have hD : ((∑ j, κ (ExponentialCoefficients.vX true j)).factorial : ℂ_[p]) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [hκ, hR, Finset.prod_mul_distrib, Finset.prod_pow, map_div₀, map_one, map_natCast]
      rw [← hM] at hD ⊢
      have hMne := right_ne_zero_of_mul hD
      field_simp
    · intro d hd
      rw [if_neg, mul_zero]
      rintro ⟨_, h⟩
      exact hd h.symm
  · rw [finsum_eq_zero_of_forall_eq_zero, mul_zero]
    intro d
    rw [if_neg, mul_zero]
    rintro ⟨h, _⟩
    exact hbal h

end PI.EntAtD.W
