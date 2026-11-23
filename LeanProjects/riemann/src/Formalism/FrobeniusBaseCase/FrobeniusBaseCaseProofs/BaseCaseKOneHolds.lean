import Formalism.FrobeniusBaseCase.Statement

open MvPowerSeries

namespace Formalism.BaseCaseIdentities

noncomputable section

open Classical

def ratVal (l : ℕ) [Fact l.Prime] : AddValuation ℚ (WithTop ℝ) :=
  AddValuation.of (fun x => if x = 0 then ⊤ else ((padicValRat l x : ℝ) : WithTop ℝ))
    (by simp) (by simp)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      by_cases hxy : x + y = 0
      · simp [hxy]
      simp only [hx, hy, hxy, if_false]
      have h := padicValRat.min_le_padicValRat_add (p := l) hxy
      rcases le_total (padicValRat l x) (padicValRat l y) with h1 | h1
      · rw [min_eq_left h1] at h
        refine le_trans (min_le_left _ _) ?_
        exact_mod_cast h
      · rw [min_eq_right h1] at h
        refine le_trans (min_le_right _ _) ?_
        exact_mod_cast h)
    (by
      intro x y
      by_cases hx : x = 0
      · simp [hx]
      by_cases hy : y = 0
      · simp [hy]
      simp only [hx, hy, mul_eq_zero, or_self, if_false]
      rw [padicValRat.mul hx hy]
      push_cast
      rfl)

theorem ratVal_apply (l : ℕ) [Fact l.Prime] {x : ℚ} (hx : x ≠ 0) :
    ratVal l x = ((padicValRat l x : ℝ) : WithTop ℝ) := by
  simp [ratVal, hx]

theorem ratVal_l (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ) = 1 := by
  rw [ratVal_apply l (by exact_mod_cast hl.out.ne_zero)]
  simp [padicValRat.self hl.out.one_lt]

theorem ratVal_l_inv (l : ℕ) [hl : Fact l.Prime] : ratVal l (l : ℚ)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := by
  have h0 : (l : ℚ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  rw [ratVal_apply l (inv_ne_zero h0), padicValRat.inv, padicValRat.self hl.out.one_lt]
  simp

def exData (l i : ℕ) (hl : l.Prime) (hl3 : 3 ≤ l) (hi : Odd i) : Data ℚ Unit (Fin 2) :=
  haveI : Fact l.Prime := ⟨hl⟩
  { v := ratVal l
    l := l
    l_prime := hl
    l_ge := hl3
    v_l := ratVal_l l
    i := i
    i_odd := hi
    good := fun _ => True
    lev := fun c => c.val
    pure_good := fun _ _ => trivial
    ι := fun _ => 0
    ι_inj := fun _ _ _ => rfl
    ι_lev := fun _ => rfl
    al := fun c j b => if c = 0 ∧ j = 2 ∧ b = 1 then (l : ℚ)⁻¹ else 0
    g := fun c b => if c = 0 ∧ b = 1 then 1 else 0
    lam := fun _ _ => 0
    al_all := by
      intro c j b
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-((2 : ℕ) : ℝ)) ≤ -1)
      · simp
    al_good := by
      intro c _ j b _
      split_ifs with h
      · obtain ⟨_, rfl, _⟩ := h
        rw [ratVal_l_inv]
        exact_mod_cast (by norm_num : (-(((2 : ℕ) : ℝ) - 1)) ≤ -1)
      · simp
    al_one := by
      intro c _ b
      simp
    al_two := by
      intro c _ b
      by_cases h : c = 0 ∧ b = 1
      · simp [h]
      · have : ¬ (c = 0 ∧ 2 = 2 ∧ b = 1) := by tauto
        simp [h]
    g_int := by
      intro c b
      split_ifs <;> simp
    lam_int := by
      intro c b
      simp
    g_supp := by
      intro c _ b hb
      by_cases h : c = 0 ∧ b = 1
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd rfl hb
      · simp [h] }

theorem coeff_frob_smul {k : Type*} [Field k] {Z : Type*} (N : ℕ) (hN : 1 ≤ N)
    (f : MvPowerSeries Z k) (A : Z →₀ ℕ) : coeff (N • A) (frob N f) = (coeff A f) ^ N := by
  have h1 : ∀ d, N ∣ (N • A) d := fun d => by simp
  have h2 : (N • A).mapRange (· / N) (Nat.zero_div N) = A := by
    ext d
    simp [Nat.mul_div_cancel_left _ hN]
  show (if ∀ d, N ∣ (N • A) d then
    (coeff ((N • A).mapRange (· / N) (Nat.zero_div N)) f) ^ N else 0) = _
  rw [if_pos h1, h2]

theorem base_case_false_holds : BaseCaseFalse := by
  intro l i hl hl3 hi hi3
  refine ⟨exData l i hl hl3 hi, rfl, rfl, ?_⟩
  have : Fact l.Prime := ⟨hl⟩
  intro hW
  have hK : (1 : ℕ) < Kn i := by
    unfold Kn
    omega
  have h1 := hW.1 (1 : Fin 2) hK
  have hq : 1 ≤ l ^ 2 := Nat.one_le_pow _ _ (by omega)

  have hz1 : (exData l i hl hl3 hi).zvec 1 = 0 := by
    simp [Data.zvec, exData]
  have hz0 : (exData l i hl hl3 hi).zvec 0 = X () := by
    simp [Data.zvec, exData]
  have hm : (exData l i hl hl3 hi).m 1 1 = MvPowerSeries.C (-(l : ℚ)⁻¹) * frob (l ^ 2) (X ()) := by
    show MvPowerSeries.C (-(l : ℚ)⁻¹) * ∑ c : Fin 2, frob (l ^ 2) ((exData l i hl hl3 hi).zvec c) *
      MvPowerSeries.C ((exData l i hl hl3 hi).g c 1) = _
    rw [Fin.sum_univ_two, hz0, hz1]
    simp [exData]
  have h2 := h1 ((l ^ 2) • Finsupp.single () 1)
  have hlev : (exData l i hl hl3 hi).lev 1 = 1 := rfl
  rw [hlev, hz1, hm, zero_sub, ← neg_mul, ← map_neg, neg_neg, coeff_C_mul,
    coeff_frob_smul _ hq] at h2
  have hX : coeff (Finsupp.single () 1) (X () : MvPowerSeries Unit ℚ) = 1 := by
    simp [coeff_X]
  rw [hX, one_pow, mul_one] at h2
  have hv : (exData l i hl hl3 hi).v (l : ℚ)⁻¹ = ((-1 : ℝ) : WithTop ℝ) := ratVal_l_inv l
  rw [hv, ← WithTop.coe_add, WithTop.coe_le_coe] at h2
  have hdeg : (((l ^ 2) • Finsupp.single () 1 : Unit →₀ ℕ).degree : ℕ) = l ^ 2 := by
    simp
  rw [hdeg] at h2
  simp only [Data.top, Data.rad] at h2
  have hl' : (exData l i hl hl3 hi).l = l := rfl
  have hi' : (exData l i hl hl3 hi).i = i := rfl
  rw [hl', hi'] at h2

  have hlR : (3 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hl3
  have hq1 : (0 : ℝ) < (l : ℝ) ^ 2 - 1 := by nlinarith
  have hrho : ((l ^ 2 : ℕ) : ℝ) * rho l = 1 + rho l := by
    unfold rho
    push_cast
    field_simp
    ring
  have hpow : (l : ℝ) ^ 3 ≤ (l : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi3
  have hLpos : (0 : ℝ) < (l : ℝ) ^ i := by positivity
  have hsg : ((l ^ 2 : ℕ) : ℝ) * sg l i < 1 := by
    unfold sg
    push_cast
    rw [mul_div_assoc', div_lt_one (by positivity)]
    nlinarith [sq_nonneg (l : ℝ)]
  nlinarith

theorem Data.base_case_k_one_holds {k : Type*} [Field k] {Z C : Type*} [Fintype Z] [Fintype C]
    (D : Data k Z C) : D.FrobeniusBaseCaseIdentity := by
  intro hi
  have hK : D.K = 1 := by simp [Data.K, Kn, hi]
  have hzero : ∀ w : ℝ, D.Wt w (0 : MvPowerSeries Z k) := by
    intro w A
    simp
  refine ⟨?_, ?_⟩
  · intro c hc
    rw [hK] at hc
    have : D.lev c = 0 := by omega
    rw [this]
    show D.Wt D.top (D.zvec c - D.zvec c)
    rw [sub_self]
    exact hzero _
  · intro c hc
    rw [hK] at hc
    have : D.zvec c = 0 := by
      unfold Data.zvec
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]
      rintro rfl
      rw [D.ι_lev] at hc
      omega
    rw [this]
    exact hzero _

end

end Formalism.BaseCaseIdentities
