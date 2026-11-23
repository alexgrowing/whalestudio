import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOps

noncomputable section

open Classical

namespace PI.BeDiagZp

open MvPowerSeries

namespace IntegralPowerSeriesBall

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

def ballSub (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, norm_mul] at *
    exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by simp
  add_mem' {a b} ha hb := (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' {a} ha := by simpa using ha

theorem intMv_one : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) := fun n => by
  rw [coeff_one]; split_ifs
  · exact (ballSub p).one_mem
  · exact (ballSub p).zero_mem

theorem intMv_inv {F : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (h1 : constantCoeff F = 1) :
    ∃ G : MvPowerSeries σ ℂ_[p], IntegralMv G ∧ F * G = 1 := by
  let F' : MvPowerSeries σ (ballSub p) := fun n => ⟨coeff n F, hF n⟩
  have hmap : map (ballSub p).subtype F' = F := by
    ext n; rw [coeff_map]; rfl
  have hc : constantCoeff F' = 1 := by
    apply Subtype.val_injective
    have := constantCoeff_map (ballSub p).subtype F'
    rw [hmap, h1] at this
    simpa using this.symm
  have hG' : F' * invOfUnit F' 1 = 1 := mul_invOfUnit F' 1 (by rw [hc, Units.val_one])
  refine ⟨map (ballSub p).subtype (invOfUnit F' 1), fun n => ?_, ?_⟩
  · rw [coeff_map]; exact (coeff n (invOfUnit F' 1)).2
  · rw [← hmap, ← map_mul, hG', map_one]

def expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • f ^ n

theorem coeff_expMv (f : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    coeff α (expMv f) =
      ∑ n ∈ Finset.range (Finsupp.degree α + 1), coeff α (f ^ n) / (n.factorial : ℂ_[p]) := rfl

theorem coeff_expT (f : MvPowerSeries σ ℂ_[p]) (N : ℕ) (α : σ →₀ ℕ) :
    coeff α (expT f N) = ∑ n ∈ Finset.range N, coeff α (f ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [expT, map_sum, map_smul, smul_eq_mul, div_eq_inv_mul]

end IntegralPowerSeriesBall

open IntegralPowerSeriesBall

variable {p : ℕ} [Fact p.Prime] {σ : Type*}

theorem coeff_pow_eq_zero_of_lt {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {n : ℕ}
    {α : σ →₀ ℕ} (h : Finsupp.degree α < n) : coeff α (f ^ n) = 0 := by
  apply coeff_of_lt_order
  exact lt_of_lt_of_le (by exact_mod_cast h) (le_order_pow_of_constantCoeff_eq_zero n hf)

theorem coeff_pow_mul_pow_eq_zero_of_lt {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {m j : ℕ} {α : σ →₀ ℕ} (h : Finsupp.degree α < m + j) :
    coeff α (x ^ m * y ^ j) = 0 := by
  apply coeff_of_lt_order
  calc ((Finsupp.degree α : ℕ) : ℕ∞) < ((m + j : ℕ) : ℕ∞) := by exact_mod_cast h
    _ = (m : ℕ∞) + (j : ℕ∞) := by push_cast; rfl
    _ ≤ (x ^ m).order + (y ^ j).order :=
        add_le_add (le_order_pow_of_constantCoeff_eq_zero m hx)
          (le_order_pow_of_constantCoeff_eq_zero j hy)
    _ ≤ (x ^ m * y ^ j).order := le_order_mul

theorem coeff_expMv_eq_expT {f : MvPowerSeries σ ℂ_[p]} (hf : constantCoeff f = 0) {α : σ →₀ ℕ}
    {N : ℕ} (hN : Finsupp.degree α < N) : coeff α (expMv f) = coeff α (expT f N) := by
  rw [coeff_expMv, coeff_expT]
  apply Finset.sum_subset
  · intro n hn; simp only [Finset.mem_range] at *; omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [coeff_pow_eq_zero_of_lt hf (by omega), zero_div]

theorem inv_fact_mul_choose (n m : ℕ) (h : m ≤ n) :
    (n.factorial : ℂ_[p])⁻¹ * (n.choose m : ℂ_[p]) =
      (m.factorial : ℂ_[p])⁻¹ * ((n - m).factorial : ℂ_[p])⁻¹ := by
  have h1 := Nat.choose_mul_factorial_mul_factorial h
  have hn : (n.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hm : (m.factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have hk : ((n - m).factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : (n.choose m : ℂ_[p]) * m.factorial * (n - m).factorial = n.factorial := by
    exact_mod_cast h1
  field_simp
  exact h2

theorem expT_add (x y : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    expT (x + y) N = ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range (N - m),
      (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)) := by
  rw [← Finset.sum_range_diag_flip N
    (fun m j => (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)))]
  unfold expT
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [add_pow, Finset.smul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [← inv_fact_mul_choose n m hmn, mul_comm _ (n.choose m : ℂ_[p]), ← smul_smul,
    mul_comm _ ((n.choose m : ℕ) : MvPowerSeries σ ℂ_[p]), ← nsmul_eq_mul,
    Nat.cast_smul_eq_nsmul]
  exact smul_comm _ _ _

theorem expT_mul_expT (x y : MvPowerSeries σ ℂ_[p]) (N : ℕ) :
    expT x N * expT y N = ∑ m ∈ Finset.range N, ∑ j ∈ Finset.range N,
      (((m.factorial : ℂ_[p])⁻¹ * (j.factorial : ℂ_[p])⁻¹) • (x ^ m * y ^ j)) := by
  unfold expT
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun j _ => ?_
  rw [smul_mul_smul_comm]

theorem coeff_expT_add {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) {α : σ →₀ ℕ} {N : ℕ} (hN : Finsupp.degree α < N) :
    coeff α (expT (x + y) N) = coeff α (expT x N * expT y N) := by
  rw [expT_add, expT_mul_expT, map_sum, map_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [map_sum, map_sum]
  apply Finset.sum_subset
  · intro j hj; simp only [Finset.mem_range] at *; omega
  · intro j _ hj
    simp only [Finset.mem_range, not_lt] at hm hj
    rw [map_smul, coeff_pow_mul_pow_eq_zero_of_lt hx hy (by omega), smul_zero]

theorem expMv_add {x y : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (hy : constantCoeff y = 0) : expMv (x + y) = expMv x * expMv y := by
  ext α
  have hN : Finsupp.degree α < Finsupp.degree α + 1 := Nat.lt_succ_self _
  have hxy : constantCoeff (x + y) = 0 := by rw [map_add, hx, hy, add_zero]
  rw [coeff_expMv_eq_expT hxy hN, coeff_expT_add hx hy hN, coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun βγ hβγ => ?_
  have hd : Finsupp.degree α = Finsupp.degree βγ.1 + Finsupp.degree βγ.2 := by
    rw [← map_add, Finset.HasAntidiagonal.mem_antidiagonal.1 hβγ]
  rw [coeff_expMv_eq_expT (N := Finsupp.degree α + 1) hx (by omega),
    coeff_expMv_eq_expT (N := Finsupp.degree α + 1) hy (by omega)]

theorem expMv_zero : expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  ext α
  rw [coeff_expMv, Finset.sum_range_succ']
  simp

theorem constantCoeff_expMv (f : MvPowerSeries σ ℂ_[p]) : constantCoeff (expMv f) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_expMv]
  simp

theorem integral_mul {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := fun n => by
  rw [coeff_mul]
  exact (ballSub p).sum_mem fun x _ => (ballSub p).mul_mem (hF x.1) (hG x.2)

theorem integral_expMv_neg {x : MvPowerSeries σ ℂ_[p]} (hx : constantCoeff x = 0)
    (h : IntegralMv (expMv x)) : IntegralMv (expMv (-x)) := by
  obtain ⟨G, hG, hG1⟩ := intMv_inv h (constantCoeff_expMv x)
  have hnx : constantCoeff (-x) = 0 := by rw [map_neg, hx, neg_zero]
  have hmul : expMv (-x) * expMv x = 1 := by rw [← expMv_add hnx hx, neg_add_cancel, expMv_zero]
  have : expMv (-x) = G := by
    calc expMv (-x) = expMv (-x) * (expMv x * G) := by rw [hG1, mul_one]
      _ = G := by rw [← mul_assoc, hmul, one_mul]
  rw [this]; exact hG

theorem simeq_refl (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := by
  refine ⟨by rw [sub_self, map_zero], ?_⟩
  rw [sub_self, expMv_zero]; exact intMv_one

theorem simeq_symm {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f := by
  have e : g - f = -(f - g) := (neg_sub f g).symm
  refine ⟨by rw [e, map_neg, h.1, neg_zero], ?_⟩
  rw [e]; exact integral_expMv_neg h.1 h.2

theorem simeq_add {f g f' g' : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) (h' : Simeq f' g') :
    Simeq (f + f') (g + g') := by
  have e : f + f' - (g + g') = (f - g) + (f' - g') := add_sub_add_comm f f' g g'
  refine ⟨by rw [e, map_add, h.1, h'.1, add_zero], ?_⟩
  rw [e, expMv_add h.1 h'.1]; exact integral_mul h.2 h'.2

theorem simeq_trans {f g h : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g h) :
    Simeq f h := by
  have e : f - h = (f - g) + (g - h) := (sub_add_sub_cancel f g h).symm
  refine ⟨by rw [e, map_add, h1.1, h2.1, add_zero], ?_⟩
  rw [e, expMv_add h1.1 h2.1]; exact integral_mul h1.2 h2.2

theorem simeq_equivalence_additive : S0 := fun _ _ _ f _ _ _ _ =>
  ⟨simeq_refl f, simeq_symm, simeq_trans, simeq_add⟩

end PI.BeDiagZp
