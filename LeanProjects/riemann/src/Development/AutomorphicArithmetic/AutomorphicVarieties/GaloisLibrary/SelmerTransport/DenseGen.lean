import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem contMod (l : ℕ) [Fact l.Prime] (k : ℕ) {N : Type} [TopologicalSpace N] (c : ZMod (l ^ k) → N) :
    Continuous fun x : ℤ_[l] => c (PadicInt.toZModPow k x) := by
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hpos : (0 : ℝ) < (l : ℝ) ^ (-(k : ℤ)) :=
    zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hpos] with y hy
  have h1 : y - x ∈ Ideal.span {(l : ℤ_[l]) ^ k} := by
    rw [← PadicInt.norm_le_pow_iff_mem_span_pow]
    rw [Metric.mem_ball, dist_eq_norm] at hy
    exact hy.le
  rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1]

private theorem clopenEq {X N : Type} [TopologicalSpace X] [TopologicalSpace N] [DiscreteTopology N] {f g : X → N}
    (hf : Continuous f) (hg : Continuous g) : IsClopen {x | f x = g x} := by
  have h : {x | f x = g x} = (fun x => (f x, g x)) ⁻¹' {p : N × N | p.1 = p.2} := rfl
  rw [h]
  exact (isClopen_discrete _).preimage (hf.prodMk hg)

private theorem powGen (l : ℕ) [Fact l.Prime] (n : ℕ) :
    (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n = Multiplicative.ofAdd (n : ℤ_[l]) := by
  rw [← ofAdd_nsmul, nsmul_one]

private theorem denseGen (l : ℕ) [Fact l.Prime] :
    DenseRange fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n := by
  have h : (fun n : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ n) =
      fun n : ℕ => Multiplicative.ofAdd (n : ℤ_[l]) := funext (powGen l)
  rw [h]
  exact PadicInt.denseRange_natCast

private theorem tendGen (l : ℕ) [Fact l.Prime] :
    Filter.Tendsto (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) Filter.atTop (nhds 1) := by
  have h : (fun a : ℕ => (Multiplicative.ofAdd (1 : ℤ_[l])) ^ (l ^ a)) =
      fun a : ℕ => Multiplicative.ofAdd ((l : ℤ_[l]) ^ a) := by
    funext a
    rw [powGen]
    push_cast
    rfl
  rw [h]
  have h2 : ‖(l : ℤ_[l])‖ < 1 := by
    rw [PadicInt.norm_p]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one h2

private theorem solveGen (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N]
    [TopologicalSpace N] [DiscreteTopology N] (σ : Representation R (Multiplicative ℤ_[l]) N) (hσ : ContAction σ)
    (ht : ∀ m : N, ∃ n : ℕ, l ^ n • m = 0) (φ : Multiplicative ℤ_[l] → N) (hφ : Continuous φ) (m₀ : N) :
    ∃ C : Multiplicative ℤ_[l] → N, Continuous C ∧ C 1 = m₀ ∧
      ∀ x, C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x := by
  let γ : Multiplicative ℤ_[l] := Multiplicative.ofAdd 1
  let a : ℕ → N := fun n => Nat.rec (motive := fun _ => N) m₀ (fun k ak => σ γ ak - φ (γ ^ k)) n
  have ha0 : a 0 = m₀ := rfl
  have haS : ∀ n, a (n + 1) = σ γ (a n) - φ (γ ^ n) := fun n => rfl
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  have hper : ∀ m : N, ∀ᶠ k in Filter.atTop, σ (γ ^ (l ^ k)) m = m := by
    intro m
    have hc : Continuous fun g : Multiplicative ℤ_[l] => σ g m :=
      hσ'.comp (continuous_id.prodMk continuous_const)
    have ht2 := (hc.tendsto 1).comp (tendGen l)
    rw [map_one σ, Module.End.one_apply, nhds_discrete, Filter.tendsto_pure] at ht2
    exact ht2
  have hφper : ∀ᶠ k in Filter.atTop, ∀ x, φ (γ ^ (l ^ k) * x) = φ x := by
    have hev : ∀ᶠ y in nhds (1 : Multiplicative ℤ_[l]),
        ∀ x ∈ (Set.univ : Set (Multiplicative ℤ_[l])), φ (y * x) = φ x := by
      apply isCompact_univ.eventually_forall_of_forall_eventually
      intro x _
      have hopen : IsOpen {z : Multiplicative ℤ_[l] × Multiplicative ℤ_[l] | φ (z.1 * z.2) = φ z.2} :=
        (clopenEq (hφ.comp continuous_mul) (hφ.comp continuous_snd)).isOpen
      exact hopen.mem_nhds (by simp)
    filter_upwards [(tendGen l).eventually hev] with k hk x
    exact hk x (Set.mem_univ x)
  have L1 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) →
      ∀ n, a (n + q) - a n = σ (γ ^ n) (a q - a 0) := by
    intro q hq n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show n + 1 + q = n + q + 1 by omega, haS, haS, pow_succ', map_mul, Module.End.mul_apply,
        ← ih, map_sub]
      have h1 : φ (γ ^ (n + q)) = φ (γ ^ n) := by
        rw [pow_add, mul_comm (γ ^ n), hq]
      rw [h1]
      abel
  have L2 : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) →
      ∀ s, a (s * q) - a 0 = ∑ t ∈ Finset.range s, σ (γ ^ (t * q)) (a q - a 0) := by
    intro q hq s
    induction s with
    | zero => simp
    | succ s ih =>
      rw [Finset.sum_range_succ, ← ih, ← L1 q hq (s * q), add_one_mul]
      abel
  have Lmul : ∀ q : ℕ, (∀ x, φ (γ ^ q * x) = φ x) → ∀ s, ∀ x, φ (γ ^ (q * s) * x) = φ x := by
    intro q hq s
    induction s with
    | zero => intro x; simp
    | succ s ih => intro x; rw [Nat.mul_succ, pow_add, mul_assoc, ih, hq]
  obtain ⟨k, hk⟩ := hφper.exists
  obtain ⟨A, hA⟩ := Filter.eventually_atTop.mp (hper (a (l ^ k) - a 0))
  have hK1 : l ^ (max A k) = l ^ k * l ^ (max A k - k) := by
    rw [← pow_add, Nat.add_sub_cancel' (le_max_right A k)]
  have hφQ : ∀ x, φ (γ ^ (l ^ (max A k)) * x) = φ x := by
    rw [hK1]
    exact Lmul _ hk _
  have hdQ : a (l ^ (max A k)) - a 0 =
      ∑ t ∈ Finset.range (l ^ (max A k - k)), σ (γ ^ (t * l ^ k)) (a (l ^ k) - a 0) := by
    rw [← L2 _ hk, hK1, mul_comm (l ^ k)]
  have hfixQ : σ (γ ^ (l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := by
    rw [hdQ, map_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← Module.End.mul_apply, ← map_mul, mul_comm (γ ^ (l ^ (max A k))), map_mul,
      Module.End.mul_apply, hA (max A k) (le_max_left A k)]
  obtain ⟨j, hj⟩ := ht (a (l ^ (max A k)) - a 0)
  have hφK : ∀ x, φ (γ ^ (l ^ (max A k + j)) * x) = φ x := by
    rw [pow_add]
    exact Lmul _ hφQ _
  have haK : a (l ^ (max A k + j)) = a 0 := by
    have h2 := L2 _ hφQ (l ^ j)
    have h3 : ∀ t ∈ Finset.range (l ^ j),
        σ (γ ^ (t * l ^ (max A k))) (a (l ^ (max A k)) - a 0) = a (l ^ (max A k)) - a 0 := by
      intro t _
      rw [mul_comm t, pow_mul, map_pow, Module.End.pow_apply, Function.iterate_fixed hfixQ]
    rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, hj] at h2
    rw [pow_add, mul_comm]
    exact sub_eq_zero.mp h2
  have hperiod : ∀ n, a (n + l ^ (max A k + j)) = a n := by
    intro n
    have h4 := L1 _ hφK n
    rw [haK, sub_self, map_zero, sub_eq_zero] at h4
    exact h4
  have hperiod' : ∀ s n, a (n + l ^ (max A k + j) * s) = a n := by
    intro s
    induction s with
    | zero => intro n; simp
    | succ s ih => intro n; rw [Nat.mul_succ, ← add_assoc, hperiod, ih]
  have hmod : ∀ n, a (n % l ^ (max A k + j)) = a n := by
    intro n
    conv_rhs => rw [← Nat.mod_add_div n (l ^ (max A k + j))]
    rw [hperiod']
  let C : Multiplicative ℤ_[l] → N :=
    fun x => a (PadicInt.toZModPow (max A k + j) (Multiplicative.toAdd x)).val
  have hCc : Continuous C :=
    (contMod l (max A k + j) (fun i : ZMod (l ^ (max A k + j)) => a i.val)).comp continuous_toAdd
  have hCn : ∀ n : ℕ, C (γ ^ n) = a n := by
    intro n
    simp only [C, γ, powGen, toAdd_ofAdd, map_natCast, ZMod.val_natCast]
    exact hmod n
  refine ⟨C, hCc, ?_, ?_⟩
  · have h5 : C 1 = a 0 := by
      simp only [C, toAdd_one, map_zero, ZMod.val_zero]
    rw [h5, ha0]
  · intro x
    refine (denseGen l).induction_on
      (p := fun x => C (Multiplicative.ofAdd 1 * x) = σ (Multiplicative.ofAdd 1) (C x) - φ x) x ?_ ?_
    · exact (clopenEq (hCc.comp (continuous_mul_left _))
        ((continuous_of_discreteTopology
          (f := fun pr : N × N => σ (Multiplicative.ofAdd 1) pr.1 - pr.2)).comp
          (hCc.prodMk hφ))).isClosed
    · intro n
      show C (γ * γ ^ n) = σ γ (C (γ ^ n)) - φ (γ ^ n)
      rw [← pow_succ', hCn, hCn, haS]

theorem UpperTheory.V.Base.h2Zl :
    ∀ (l : ℕ) [Fact l.Prime] (R N : Type) [CommRing R] [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
      [ContinuousConstSMul R N] [DiscreteTopology N] (σ : Representation R (Multiplicative ℤ_[l]) N), ContAction σ →
      (∀ m : N, ∃ n : ℕ, l ^ n • m = 0) → Subsingleton (H2 σ) := by
  intro l _ R N _ _ _ _ _ _ _ σ hσ ht
  refine subsingleton_of_forall_eq 0 ?_
  intro x
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  show f.1 ∈ B2 σ
  rw [separated_dvr_second_cohomology_mem]
  have hf : Continuous f.1 := f.2.1
  have hcoc := f.2.2
  have hφ : Continuous fun y => f.1 (Multiplicative.ofAdd (1 : ℤ_[l]), y) :=
    hf.comp (continuous_const.prodMk continuous_id)
  obtain ⟨C, hC, hC1, hCeq⟩ := solveGen l R N σ hσ ht _ hφ (f.1 (1, 1))
  refine ⟨C, hC, ?_⟩
  funext pr
  obtain ⟨g, h⟩ := pr
  show σ g (C h) - C (g * h) + C g = f.1 (g, h)
  have hf1 : ∀ k, f.1 (1, k) = f.1 (1, 1) := by
    intro k
    have h0 := hcoc 1 1 k
    simp only [map_one, one_mul, Module.End.one_apply, sub_self, zero_add] at h0
    exact sub_eq_zero.mp h0
  have hσ' : Continuous fun p : Multiplicative ℤ_[l] × N => σ p.1 p.2 := hσ
  refine (denseGen l).induction_on (p := fun g => σ g (C h) - C (g * h) + C g = f.1 (g, h)) g ?_ ?_
  · exact (clopenEq
      (((hσ'.comp (continuous_id.prodMk continuous_const)).sub
        (hC.comp (continuous_mul_right h))).add hC)
      (hf.comp (continuous_id.prodMk continuous_const))).isClosed
  · intro n
    induction n with
    | zero =>
      simp only [pow_zero, map_one, Module.End.one_apply, one_mul, sub_self, zero_add]
      rw [hC1, hf1 h]
    | succ n ih =>
      rw [pow_succ', mul_assoc, hCeq, hCeq, map_mul, Module.End.mul_apply]
      have hc := hcoc (Multiplicative.ofAdd 1) (Multiplicative.ofAdd 1 ^ n) h
      rw [← ih, map_add, map_sub] at hc
      rw [← sub_eq_zero]
      convert hc using 1
      abel
