import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ChartValueBoundRamified
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ChartValJ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.BiextChangeSecondFactor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.IntegralValueOfChartValues

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Jv

variable (T : CDVR) (e : ℕ)

theorem nval_alg_nonneg (r : T.V) : (0 : EReal) ≤ nval T.V e (algebraMap T.V T.Fr r) := by
  by_cases hr : algebraMap T.V T.Fr r = 0
  · rw [hr, nval_zero]
    exact le_top
  · rw [nval_of_ne hr]
    have hv0 : 0 ≤ vV T.V (algebraMap T.V T.Fr r) := by
      unfold Formalism.L2.Pj.vV Formalism.L2.Pj.valV
      have hle := IsDedekindDomain.HeightOneSpectrum.valuation_le_one (K := T.Fr)
        (IsDiscreteValuationRing.maximalIdeal T.V) r
      have hne : (IsDedekindDomain.HeightOneSpectrum.valuation T.Fr (IsDiscreteValuationRing.maximalIdeal T.V))
          (algebraMap T.V T.Fr r) ≠ 0 := (Valuation.ne_zero_iff _).mpr hr
      have hlog := (WithZero.log_le_log hne one_ne_zero).mpr hle
      rw [WithZero.log_one] at hlog
      linarith
    have hv : (0 : ℝ) ≤ (vV T.V (algebraMap T.V T.Fr r) : ℝ) := by exact_mod_cast hv0
    exact EReal.coe_nonneg.mpr (div_nonneg hv (Nat.cast_nonneg e))

def Jv (c : ℝ) : Submodule T.V T.Fr where
  carrier := {x | (((-c : ℝ)) : EReal) ≤ nval T.V e x}
  add_mem' := fun {a b} ha hb => le_trans (le_min ha hb) (nval_add e a b)
  zero_mem' := by
    show _ ≤ nval T.V e 0
    rw [nval_zero]
    exact le_top
  smul_mem' := fun r x hx => by
    show _ ≤ nval T.V e (r • x)
    rw [Algebra.smul_def, nval_mul]
    exact hx.trans (le_add_of_nonneg_left (nval_alg_nonneg T e r))

theorem one_mem_Jv {c : ℝ} (hc : 0 ≤ c) : (1 : T.Fr) ∈ Jv T e c := by
  show ((-c : ℝ) : EReal) ≤ nval T.V e 1
  have h1 := Formalism.L2.Pj.vV_mul (V := T.V) (K' := T.Fr) (x := 1) (y := 1) one_ne_zero one_ne_zero
  rw [mul_one] at h1
  have h0 : vV T.V (1 : T.Fr) = 0 := by omega
  rw [nval_of_ne one_ne_zero, h0]
  simp only [Int.cast_zero, zero_div]
  exact_mod_cast neg_nonpos.mpr hc

theorem mem_Jv_pow {c : ℝ} (_hc : 0 ≤ c) : ∀ (m : ℕ) (x : T.Fr), x ∈ Jv T e c ^ m →
    (((-((m : ℝ) * c)) : ℝ) : EReal) ≤ nval T.V e x := by
  intro m
  induction m with
  | zero =>
    intro x hx
    rw [pow_zero] at hx
    obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
    simp only [Nat.cast_zero, zero_mul, neg_zero, EReal.coe_zero]
    exact nval_alg_nonneg T e r
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun y z hy hz => ?_)
    · rw [nval_mul]
      have h1 := ih a ha
      have h2 : ((-c : ℝ) : EReal) ≤ nval T.V e b := hb
      calc (((-(((m + 1 : ℕ) : ℝ) * c)) : ℝ) : EReal)
          = (((-((m : ℝ) * c)) : ℝ) : EReal) + ((-c : ℝ) : EReal) := by
            rw [← EReal.coe_add]
            congr 1
            push_cast
            ring
        _ ≤ _ := add_le_add h1 h2
    · exact le_trans (le_min hy hz) (nval_add e y z)

end Jv

theorem two_pairMin_le {ι π : Type} [Fintype ι] [Fintype π] [DecidableEq π] (c : ι → π) (s : ι → Bool)
    (x : ι →₀ ℕ) : 2 * pairMin c s x ≤ ∑ l, x l := by
  unfold pairMin
  rw [Finset.mul_sum]
  calc ∑ q : π, 2 * min (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
      ≤ ∑ q : π, ((∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l) +
        (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)) := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        have h1 := min_le_left (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        have h2 := min_le_right (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = true), x l)
          (∑ l ∈ Finset.univ.filter (fun l => c l = q ∧ s l = false), x l)
        omega
    _ = ∑ l, x l := by
        simp only [Finset.sum_filter, ← Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.sum_eq_single (c l)]
        · cases s l <;> simp
        · intro b _ hb
          have hb' : c l ≠ b := fun h => hb h.symm
          simp [hb']
        · intro h
          exact absurd (Finset.mem_univ _) h

theorem sum_pairMin_le {T : Type} [Fintype T] (rr : T → ℕ) (n : ℕ) {π : Type} [Fintype π] [DecidableEq π]
    (c : T → π) (s : T → Bool) (a : T → ℕ → ℕ) (mo : Formalism.L2.Pj.Letter T rr n →₀ ℕ)
    (hrow : ∀ (σ : T) (i : Fin (rr σ)), ∑ b : Fin n, mo ⟨σ, i, b⟩ = a σ i) :
    ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      (∑ σ, ∑ i : Fin (rr σ), a σ i) / 2 := by
  have h2 : 2 * ∑ b, pairMin (fun ℓ : (Σ τ : T, Fin (rr τ)) => c ℓ.1) (fun ℓ => s ℓ.1) (colL rr n mo b) ≤
      ∑ σ, ∑ i : Fin (rr σ), a σ i := by
    rw [Finset.mul_sum]
    calc _ ≤ ∑ b : Fin n, ∑ ℓ : (Σ τ : T, Fin (rr τ)), colL rr n mo b ℓ :=
          Finset.sum_le_sum (fun b _ => two_pairMin_le _ _ _)
      _ = ∑ ℓ : (Σ τ : T, Fin (rr τ)), ∑ b : Fin n, mo ⟨ℓ.1, ℓ.2, b⟩ := by
          rw [Finset.sum_comm]
          rfl
      _ = ∑ σ, ∑ i : Fin (rr σ), a σ i := by
          rw [Fintype.sum_sigma]
          exact Finset.sum_congr rfl (fun σ _ => Finset.sum_congr rfl (fun i _ => hrow σ i))
  omega

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
