import Formalism.LocalToGlobal.CharacterGerms.FirstVanishingAt
import Formalism.LocalToGlobal.CharacterGerms.CoeffLMulCvFrob

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace SelfAdjointCongruence

open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ PartialDerivEval MaximalIdealCongruence FirstVanishing

variable {C : Type} [Field C] [CharZero C] {V : VF C} {dd : ℕ}

def sub1 (γ : Fin dd → PowerSeries C) (P : PS C 1 dd) : PowerSeries C :=
  MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P

def FrobX (V : VF C) (P : PS C 1 dd) : Prop :=
  ∀ μ : Fin 1 × Fin dd →₀ ℕ, (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) → V.MM (MvPowerSeries.coeff μ P)

theorem coeff_l_frob {P : PS C 1 dd} (hP : IntS V P) (hPz : MvPowerSeries.constantCoeff P = 0) (hfrob : FrobX V P)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) :
    V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) -
      ∑ i, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => intS_cv (hγ j).2
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hγ0' : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := hγ0
  obtain ⟨D1, hD1def⟩ : ∃ D1 : PS C 1 dd, ∀ μ, MvPowerSeries.coeff μ D1 =
      if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0 :=
    ⟨fun μ => if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0, fun μ => rfl⟩
  obtain ⟨D3, hD3def⟩ : ∃ D3 : PS C 1 dd, D3 = ∑ i, MvPowerSeries.monomial (Finsupp.single ((0 : Fin 1), i) V.l)
      (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) := ⟨_, rfl⟩
  have hD1 : MMS V D1 := fun μ => by
    rw [hD1def]
    split_ifs with h
    · exact hfrob μ h
    · exact mm_zero
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  have hD2 : Agr (2 * V.l) (P - D1 - D3) 0 := by
    intro μ hμ
    rw [map_sub, map_sub, map_zero, hD1def, hD3def, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    by_cases hex : ∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)
    · rw [if_pos hex, sub_self, zero_sub, neg_eq_zero]
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      rintro rfl
      obtain ⟨i', hi'⟩ := hex
      apply hi'
      rw [Finsupp.single_apply]
      split_ifs
      · exact dvd_refl _
      · exact dvd_zero _
    · rw [if_neg hex, sub_zero]
      push Not at hex
      have hdiv : ∀ s, V.l ∣ μ s := fun s => by rw [hsq s]; exact hex s.2
      rcases FirstVanishing.divisible_small μ hdiv hμ with h0 | ⟨s, hs⟩
      · subst h0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz, zero_sub, neg_eq_zero]
        refine Finset.sum_eq_zero fun i _ => if_neg ?_
        intro h
        have := congrArg (fun f : Fin 1 × Fin dd →₀ ℕ => f ((0 : Fin 1), i)) h
        simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_eq_same] at this
        omega
      · subst hs
        rw [Finset.sum_eq_single s.2, if_pos (by rw [← hsq s]), ← hsq s, sub_self]
        · intro i _ hi
          rw [if_neg]
          intro h
          apply hi
          have := (Finsupp.single_left_inj (by omega : V.l ≠ 0)).1 h
          rw [this]
        · intro h
          exact absurd (Finset.mem_univ _) h
  have hz : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (0 : PS C 1 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hG, map_zero]
  have hsplit : P = D1 + (P - D1 - D3) + D3 := by ring
  have hdeg : (Finsupp.single () V.l).degree < 2 * V.l := by
    rw [Finsupp.degree_single]
    omega
  have hA2 := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) hD2)
    (Finsupp.single () V.l) hdeg
  rw [hz, map_zero] at hA2
  have hA2' : PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3)) = 0 :=
    hA2
  have hB1' : MMS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1) :=
    MMS.subst (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0' q.2) (fun q => hγI q.2) hD1
  have hB1 : V.MM (PowerSeries.coeff V.l (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1)) :=
    hB1' (Finsupp.single () V.l)
  have hD3 : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 =
      ∑ i, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) * γ i ^ V.l := by
    rw [hD3def, ← MvPowerSeries.coe_substAlgHom hG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hG, MvPowerSeries.subst_monomial hG, Finsupp.prod_single_index (by simp)]
    rfl
  have hfr : ∀ i, V.MM (PowerSeries.coeff V.l (γ i ^ V.l) - (PowerSeries.coeff 1 (γ i)) ^ V.l) := by
    intro i
    have h := mms_pow_frobTw (hγI i) (Finsupp.single () V.l)
    rw [map_sub, coeff_frobTw, if_pos (fun s => by simp)] at h
    have e : (Finsupp.single () V.l).mapRange (fun n => n / V.l) (Nat.zero_div V.l) = Finsupp.single () 1 := by
      rw [Finsupp.mapRange_single, Nat.div_self (by omega)]
    rw [e] at h
    exact h
  have eP : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1 +
        MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1 - D3) +
          MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 := by
    conv_lhs => rw [hsplit]
    rw [MvPowerSeries.subst_add hG, MvPowerSeries.subst_add hG]
  rw [eP, map_add, map_add, hA2', add_zero, hD3, map_sum]
  have e : ∀ (a : C) (s t : Fin dd → C),
      a + ∑ i, s i - ∑ i, t i = a + ∑ i, (s i - t i) := fun a s t => by
    rw [Finset.sum_sub_distrib]
    ring
  rw [e]
  refine mm_add hB1 (mm_sum _ _ fun i _ => ?_)
  rw [show PowerSeries.coeff V.l (MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P) *
      γ i ^ V.l) = MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) V.l) P * PowerSeries.coeff V.l (γ i ^ V.l) from
    MvPowerSeries.coeff_C_mul _ _ _, ← mul_sub]
  exact mm_mul_ge' (hP _) (hfr i)

theorem coeff_lt_frob {P : PS C 1 dd} (hPz : MvPowerSeries.constantCoeff P = 0) (hfrob : FrobX V P)
    {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) (n : ℕ) (hn : n < V.l) :
    V.MM (PowerSeries.coeff n (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P)) := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hγI : ∀ j, IntS V (γ j) := fun j => intS_cv (hγ j).2
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  obtain ⟨D1, hD1def⟩ : ∃ D1 : PS C 1 dd, ∀ μ, MvPowerSeries.coeff μ D1 =
      if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0 :=
    ⟨fun μ => if (∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)) then MvPowerSeries.coeff μ P else 0, fun μ => rfl⟩
  have hD1 : MMS V D1 := fun μ => by
    rw [hD1def]
    split_ifs with h
    · exact hfrob μ h
    · exact mm_zero
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  have hD2 : Agr V.l (P - D1) 0 := by
    intro μ hμ
    rw [map_sub, map_zero, hD1def]
    by_cases hex : ∃ i, ¬ V.l ∣ μ ((0 : Fin 1), i)
    · rw [if_pos hex, sub_self]
    · rw [if_neg hex, sub_zero]
      push Not at hex
      have hdiv : ∀ s, V.l ∣ μ s := fun s => by rw [hsq s]; exact hex s.2
      rcases FirstVanishing.divisible_small μ hdiv (by omega) with h0 | ⟨s, hs⟩
      · subst h0
        rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz]
      · subst hs
        rw [Finsupp.degree_single] at hμ
        omega
  have hz : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (0 : PS C 1 dd) = 0 := by
    rw [← MvPowerSeries.coe_substAlgHom hG, map_zero]
  have hA2 := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0 q.2) hD2)
    (Finsupp.single () n) (by rw [Finsupp.degree_single]; exact hn)
  rw [hz, map_zero] at hA2
  have hA2' : PowerSeries.coeff n (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1)) = 0 := hA2
  have hB1' : MMS V (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1) :=
    MMS.subst (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0 q.2) (fun q => hγI q.2) hD1
  have hB1 : V.MM (PowerSeries.coeff n (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1)) :=
    hB1' (Finsupp.single () n)
  have eP : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P =
      MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D1 +
        MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) (P - D1) := by
    conv_lhs => rw [show P = D1 + (P - D1) by ring]
    rw [MvPowerSeries.subst_add hG]
  rw [eP, map_add, hA2', add_zero]
  exact hB1

def LowMM (V : VF C) (f : PowerSeries C) : Prop := ∀ n ≤ V.l, V.MM (PowerSeries.coeff n f)

theorem LowMM.mul_int {f g : PowerSeries C} (hf : LowMM V f) (hg : IntS V g) : LowMM V (f * g) := by
  intro n hn
  rw [PowerSeries.coeff_mul]
  refine mm_sum _ _ fun p hp => mm_mul_ge (hf p.1 ?_) (hg (Finsupp.single () p.2))
  have := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  omega

theorem lowMM_subst {σ : Type} [Finite σ] {a : σ → PowerSeries C} (ha0 : ∀ s, MvPowerSeries.constantCoeff (a s) = 0)
    (haI : ∀ s, IntS V (a s)) (haL : ∀ s, LowMM V (a s)) {f : MvPowerSeries σ C} (hf : IntS V f)
    (hf0 : MvPowerSeries.constantCoeff f = 0) : LowMM V (MvPowerSeries.subst a f) := by
  intro n hn
  change V.MM (MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst a f))
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero ha0)]
  refine finsum_induction (fun x => V.MM x) mm_zero (fun x y hx hy => mm_add hx hy) fun e => ?_
  rw [smul_eq_mul]
  by_cases he : e = 0
  · subst he
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf0, zero_mul]
    exact mm_zero
  · obtain ⟨s, hs⟩ := Finsupp.ne_iff.mp he
    have hs' : e s ≠ 0 := by simpa using hs
    have hmem : s ∈ e.support := Finsupp.mem_support_iff.2 hs'
    have hp : LowMM V (e.prod fun s m => a s ^ m) := by
      unfold Finsupp.prod
      rw [← Finset.mul_prod_erase _ _ hmem]
      obtain ⟨m, hm⟩ : ∃ m, e s = m + 1 := ⟨e s - 1, by omega⟩
      rw [hm]
      show LowMM V (a s ^ (m + 1) * ∏ x ∈ e.support.erase s, a x ^ e x)
      rw [pow_succ', mul_assoc]
      refine (haL s).mul_int (intS_mul (intS_pow (haI s) _) ?_)
      exact Finset.prod_induction _ (IntS V) (fun _ _ h1 h2 => intS_mul h1 h2) intS_one fun t _ => intS_pow (haI t) _
    exact mm_mul_ge' (hf e) (hp n hn)

theorem coeff_one_subst_curve {P : PS C 1 dd} (hPz : MvPowerSeries.constantCoeff P = 0) {γ : Fin dd → PowerSeries C}
    (hγ0 : ∀ j, MvPowerSeries.constantCoeff (γ j) = 0) :
    PowerSeries.coeff 1 (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) =
      ∑ j, MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) P * PowerSeries.coeff 1 (γ j) := by
  have hG : MvPowerSeries.HasSubst (fun q : Fin 1 × Fin dd => γ q.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hγ0 q.2
  have hsq : ∀ (s : Fin 1 × Fin dd), s = ((0 : Fin 1), s.2) := fun s => Prod.ext (Subsingleton.elim _ _) rfl
  obtain ⟨D3, hD3def⟩ : ∃ D3 : PS C 1 dd, D3 = ∑ i, MvPowerSeries.monomial (Finsupp.single ((0 : Fin 1), i) 1)
      (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) P) := ⟨_, rfl⟩
  have hD2 : Agr 2 P D3 := by
    intro μ hμ
    rw [hD3def, map_sum]
    simp only [MvPowerSeries.coeff_monomial]
    rcases Nat.lt_succ_iff.1 hμ |>.lt_or_eq with h1 | h1
    · have h0 : μ = 0 := (Finsupp.degree_eq_zero_iff _).1 (by omega)
      subst h0
      rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hPz]
      symm
      refine Finset.sum_eq_zero fun i _ => if_neg ?_
      intro h
      have := congrArg (fun f : Fin 1 × Fin dd →₀ ℕ => f ((0 : Fin 1), i)) h
      simp at this
    · obtain ⟨s, hs⟩ := degree_one h1
      subst hs
      rw [Finset.sum_eq_single s.2, if_pos (by rw [← hsq s]), ← hsq s]
      · intro i _ hi
        rw [if_neg]
        intro h
        apply hi
        have := (Finsupp.single_left_inj (by omega : (1 : ℕ) ≠ 0)).1 h
        rw [this]
      · intro h
        exact absurd (Finset.mem_univ _) h
  have hA := (agr_subst_right (a := fun q : Fin 1 × Fin dd => γ q.2) (fun q => hγ0 q.2) hD2)
    (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  have hA' : PowerSeries.coeff 1 (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) P) =
      PowerSeries.coeff 1 (MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3) := hA
  have hD3 : MvPowerSeries.subst (fun q : Fin 1 × Fin dd => γ q.2) D3 =
      ∑ i, MvPowerSeries.C (MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), i) 1) P) * γ i ^ 1 := by
    rw [hD3def, ← MvPowerSeries.coe_substAlgHom hG, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [MvPowerSeries.coe_substAlgHom hG, MvPowerSeries.subst_monomial hG, Finsupp.prod_single_index (by simp)]
    rfl
  rw [hA', hD3, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_one]
  exact MvPowerSeries.coeff_C_mul _ _ _

end SelfAdjointCongruence

end Formalism.L2.FormalSeriesBounds
