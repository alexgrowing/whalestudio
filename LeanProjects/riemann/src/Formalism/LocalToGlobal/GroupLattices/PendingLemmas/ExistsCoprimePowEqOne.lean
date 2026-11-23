import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.CoeffOneLNe

open Filter Topology

noncomputable section

namespace Formalism.L2.G.Pend

variable (p : ℕ) [hp : Fact p.Prime]

theorem norm_wToC_pow_mul (N : ℕ) (b : WW p) : ‖wToC p ((p : WW p) ^ N * b)‖ ≤ ((p : ℝ)⁻¹) ^ N := by
  rw [map_mul, map_pow, map_natCast, norm_mul, norm_pow, norm_p_C]
  exact mul_le_of_le_one_right (pow_nonneg (r_nonneg p) N) (norm_wToC_le p b)

theorem norm_wToC_unit (u : (WW p)ˣ) : ‖wToC p (u : WW p)‖ = 1 := by
  refine le_antisymm (norm_wToC_le p _) ?_
  have h1 : wToC p (u : WW p) * wToC p ((u⁻¹ : (WW p)ˣ) : WW p) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 := congrArg norm h1
  rw [norm_mul, norm_one] at h2
  calc (1 : ℝ) = ‖wToC p (u : WW p)‖ * ‖wToC p ((u⁻¹ : (WW p)ˣ) : WW p)‖ := h2.symm
    _ ≤ ‖wToC p (u : WW p)‖ * 1 := mul_le_mul_of_nonneg_left (norm_wToC_le p _) (norm_nonneg _)
    _ = _ := mul_one _

theorem r_pos : 0 < ((p : ℝ)⁻¹) := by
  have : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  positivity

theorem dvd_of_norm_le {x : WW p} {N : ℕ} (h : ‖wToC p x‖ ≤ ((p : ℝ)⁻¹) ^ N) : (p : WW p) ^ N ∣ x := by
  by_cases hx : x = 0
  · rw [hx]; exact dvd_zero _
  obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx (WittVector.irreducible p (k := kb p))
  rw [hu, map_mul, map_pow, map_natCast, norm_mul, norm_wToC_unit, one_mul, norm_pow, norm_p_C] at h
  have hNk : N ≤ k := (pow_le_pow_iff_right_of_lt_one₀ (r_pos p) (r_lt_one p)).1 h
  rw [hu]
  exact Dvd.dvd.mul_left (pow_dvd_pow _ hNk) _

theorem mem_range_of_closure {y : ℂ_[p]} (hy : y ∈ closure (Set.range (wToC p))) : y ∈ Set.range (wToC p) := by
  have h1 : ∀ N : ℕ, ∃ x : WW p, ‖y - wToC p x‖ ≤ ((p : ℝ)⁻¹) ^ N := by
    intro N
    obtain ⟨_, ⟨x, rfl⟩, hx⟩ := Metric.mem_closure_iff.1 hy _ (pow_pos (r_pos p) N)
    exact ⟨x, by rw [← dist_eq_norm]; exact hx.le⟩
  choose xs hxs using h1
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : WW p)}) xs (by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    apply dvd_of_norm_le
    rw [map_sub]
    have : wToC p (xs m) - wToC p (xs n) = (y - wToC p (xs n)) - (y - wToC p (xs m)) := by ring
    rw [this]
    exact nsub p ((hxs n).trans (pow_le_pow_of_le_one (r_nonneg p) (r_lt_one p).le hmn)) (hxs m))
  refine ⟨L, (eq_of_close p fun N => ?_).symm⟩
  have h2 := hL N
  rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  have : y - wToC p L = (y - wToC p (xs N)) + wToC p (xs N - L) := by rw [map_sub]; ring
  rw [this, hc]
  exact nadd p (hxs N) (norm_wToC_pow_mul p N c)

theorem exists_coprime_pow_eq_one {y : kb p} (hy : y ≠ 0) : ∃ m : ℕ, 0 < m ∧ Nat.Coprime m p ∧ y ^ m = 1 := by
  obtain ⟨q, hq, hyq⟩ := exists_pow_eq p y
  have h1 : y ^ (q - 1) = 1 := by
    have : y ^ (q - 1) * y = 1 * y := by rw [← pow_succ, Nat.sub_add_cancel hq.le, hyq, one_mul]
    exact mul_right_cancel₀ hy this
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := q - 1) (by omega) p hp.out.ne_one
  refine ⟨m, Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero _)),
    ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm, ?_⟩
  rw [hn, mul_comm, pow_mul] at h1
  apply iterateFrobenius_inj (kb p) p a
  rw [iterateFrobenius_def, iterateFrobenius_def, h1, one_pow]

abbrev muP : Set ℂ_[p] := {ζ : ℂ_[p] | ∃ n : ℕ, 0 < n ∧ Nat.Coprime n p ∧ ζ ^ n = 1}

theorem wToC_teich_mem (y : kb p) : wToC p (WittVector.teichmuller p y) ∈ Subring.closure (muP p) := by
  by_cases hy : y = 0
  · rw [hy, WittVector.teichmuller_zero, map_zero]
    exact Subring.zero_mem _
  · obtain ⟨m, hm, hc, h1⟩ := exists_coprime_pow_eq_one p hy
    exact Subring.subset_closure ⟨m, hm, hc, by rw [← map_pow, ← map_pow, h1, map_one, map_one]⟩

theorem teich_injective : Function.Injective (WittVector.teichmuller p : kb p →* WW p) := by
  intro a b h
  have := congrArg (fun x : WW p => x.coeff 0) h
  simpa [WittVector.teichmuller_coeff_zero] using this

theorem root_mem_range {ζ : ℂ_[p]} {n : ℕ} (hn : 0 < n) (hc : Nat.Coprime n p) (hζ : ζ ^ n = 1) :
    ζ ∈ Set.range (wToC p) := by
  have : NeZero ((n : ℕ) : kb p) := ⟨by
    intro h0
    rw [CharP.cast_eq_zero_iff (kb p) p] at h0
    exact hp.out.ne_one (hc.symm.eq_one_of_dvd h0)⟩
  have : NeZero n := ⟨hn.ne'⟩
  obtain ⟨η, hη⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (kb p) n
  have h1 : IsPrimitiveRoot (WittVector.teichmuller p η) n := hη.map_of_injective (teich_injective p)
  have h2 : IsPrimitiveRoot (wToC p (WittVector.teichmuller p η)) n := h1.map_of_injective (wToC_injective p)
  obtain ⟨i, _, hi⟩ := h2.eq_pow_of_pow_eq_one hζ
  exact ⟨WittVector.teichmuller p η ^ i, by rw [map_pow, hi]⟩

theorem wToC_mem_Wp (x : WW p) : wToC p x ∈ Formalism.MainNotions.GL3Theta.Wp p := by
  show wToC p x ∈ closure ((Subring.closure (muP p) : Subring ℂ_[p]) : Set ℂ_[p])
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε (r_lt_one p)
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  refine ⟨wToC p (∑ i ∈ Finset.Iic N, (WittVector.teichmuller p
        (((_root_.frobeniusEquiv (kb p) p).symm ^ i) (x.coeff i)) * (p : WW p) ^ i)), ?_, ?_⟩
  · rw [map_sum]
    refine Subring.sum_mem _ fun i _ => ?_
    rw [map_mul, map_pow, map_natCast]
    exact Subring.mul_mem _ (wToC_teich_mem p _) (Subring.pow_mem _ (natCast_mem _ p) i)
  · rw [dist_eq_norm, ← map_sub, hc]
    refine lt_of_le_of_lt (norm_wToC_pow_mul p (N + 1) c) (lt_of_le_of_lt ?_ hN)
    exact pow_le_pow_of_le_one (r_nonneg p) (r_lt_one p).le (Nat.le_succ N)

theorem Wp_le_range : Formalism.MainNotions.GL3Theta.Wp p ≤ (wToC p).range := by
  apply Subring.topologicalClosure_minimal
  · rw [Subring.closure_le]
    rintro ζ ⟨n, hn, hc, hζ⟩
    exact root_mem_range p hn hc hζ
  · rw [RingHom.coe_range]
    exact isClosed_of_closure_subset fun y hy => mem_range_of_closure p hy

theorem range_wToC : Set.range (wToC p) = (Formalism.MainNotions.GL3Theta.Wp p : Set ℂ_[p]) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact wToC_mem_Wp p x
  · intro hy
    exact Wp_le_range p hy

theorem mem_Wp_iff (y : ℂ_[p]) : y ∈ Formalism.MainNotions.GL3Theta.Wp p ↔ ∃ x : WW p, wToC p x = y := by
  have := Set.ext_iff.1 (range_wToC p) y
  exact this.symm

section Rat

open MvPowerSeries Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.J

variable {p}

theorem pC_ne : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero

theorem inWf_iff (x : ℂ_[p]) : InWf x ↔ ∃ z : K0 p, k0ToC p z = x := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨w, hw⟩ := (mem_Wp_iff p _).1 hk
    refine ⟨algebraMap (WW p) (K0 p) w / (p : K0 p) ^ k, ?_⟩
    rw [map_div₀, witt_fraction_to_Cp_algebraMap, hw, map_pow, map_natCast, mul_div_cancel_left₀ _ (pow_ne_zero _ pC_ne)]
  · rintro ⟨z, rfl⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := WW p) z
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    obtain ⟨k, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 (WittVector.irreducible p (k := kb p))
    refine ⟨k, (mem_Wp_iff p _).2 ⟨a * ((u⁻¹ : (WW p)ˣ) : WW p), ?_⟩⟩
    have hu1 : wToC p (u : WW p) * wToC p ((u⁻¹ : (WW p)ˣ) : WW p) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have hu0 : wToC p (u : WW p) ≠ 0 := left_ne_zero_of_mul_eq_one hu1
    rw [map_div₀, witt_fraction_to_Cp_algebraMap, witt_fraction_to_Cp_algebraMap, hu, map_mul, map_mul, map_pow, map_natCast, eq_inv_of_mul_eq_one_right hu1]
    have := pow_ne_zero k (pC_ne (p := p))
    field_simp

theorem coefWf_iff {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    CoefWf F ↔ ∃ b : MvPowerSeries σ (K0 p), map (k0ToC p) b = F := by
  constructor
  · intro h
    choose b hb using fun n => (inWf_iff _).1 (h n)
    exact ⟨b, by ext n; exact hb n⟩
  · rintro ⟨b, rfl⟩ n
    rw [coeff_map]
    exact (inWf_iff _).2 ⟨_, rfl⟩

theorem integralW_iff {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    IntegralW F ↔ ∃ b : MvPowerSeries σ (WW p), map (wToC p) b = F := by
  constructor
  · intro h
    choose b hb using fun n => (mem_Wp_iff p _).1 (h n)
    exact ⟨b, by ext n; exact hb n⟩
  · rintro ⟨b, rfl⟩ n
    rw [coeff_map]
    exact (mem_Wp_iff p _).2 ⟨_, rfl⟩

theorem beRat_of (g : G1 p) (hex : PowerSeries.constantCoeff g.ex = 0)
    (hB : CoefWf (g.be (X 0) (X 1) : MvPowerSeries (Fin 2) ℂ_[p]))
    (hE : CoefWf (g.ex : MvPowerSeries Unit ℂ_[p])) (e : K0 p) : BeRat g (k0ToC p e) := by
  obtain ⟨B0, hB0⟩ := (coefWf_iff _).1 hB
  obtain ⟨E0, hE0⟩ := (coefWf_iff _).1 hE
  have hE00 : PowerSeries.constantCoeff (E0 : PowerSeries (K0 p)) = 0 := by
    apply (k0ToC p).injective
    rw [map_zero, ← hex, ← hE0]
    rfl
  have h0 : ∀ i : Fin 2, constantCoeff (C e⁻¹ * X i : MvPowerSeries (Fin 2) (K0 p)) = 0 := by
    intro i
    rw [map_mul, constantCoeff_X, mul_zero]
  have h0' : ∀ i : Fin 2, constantCoeff (C (k0ToC p e)⁻¹ * X i : MvPowerSeries (Fin 2) ℂ_[p]) = 0 := by
    intro i
    rw [map_mul, constantCoeff_X, mul_zero]
  let a : Fin 2 → MvPowerSeries (Fin 2) (K0 p) := fun i => PowerSeries.subst (C e⁻¹ * X i) (E0 : PowerSeries (K0 p))
  have ha0 : ∀ i, constantCoeff (a i) = 0 := fun i => PowerSeries.constantCoeff_subst_eq_zero (h0 i) _ hE00
  have ha : HasSubst a := hasSubst_of_constantCoeff_zero ha0
  have hai : ∀ i, map (k0ToC p) (a i) = g.pt (C (k0ToC p e)⁻¹ * X i) := by
    intro i
    show map (k0ToC p) (PowerSeries.subst _ _) = _
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero (h0 i)), map_mul, map_C, map_X, map_inv₀]
    unfold G1.pt
    congr 1
  have hT : HasSubst (fun i : Fin 2 => g.pt (C (k0ToC p e)⁻¹ * X i : MvPowerSeries (Fin 2) ℂ_[p])) :=
    hasSubst_of_constantCoeff_zero fun i => cc_pt g hex (h0' i)
  refine ⟨subst a B0, ?_⟩
  rw [map_subst ha, hB0]
  simp only [hai]
  rw [be_subst g hex hT (constantCoeff_X 0) (constantCoeff_X 1), subst_X hT, subst_X hT]
  rfl

end Rat

section LT

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.J

variable {p}

theorem isUnit_of_norm_eq_one {x : WW p} (h : ‖wToC p x‖ = 1) : IsUnit x := by
  by_contra hx
  have h1 : (p : WW p) ∣ x := by
    have : x ∈ IsLocalRing.maximalIdeal (WW p) := (IsLocalRing.mem_maximalIdeal x).2 hx
    rwa [(WittVector.irreducible p (k := kb p)).maximalIdeal_eq, Ideal.mem_span_singleton] at this
  obtain ⟨c, rfl⟩ := h1
  have := norm_wToC_pow_mul p 1 c
  rw [pow_one, pow_one, h] at this
  exact absurd this (not_le.2 (r_lt_one p))

theorem logF_map : PowerSeries.map (k0ToC p) (Formalism.MainNotions.FormalGroupSystem.logF p) = Formalism.MainNotions.GL3Theta.logF p := by
  ext n
  rw [PowerSeries.coeff_map]
  unfold Formalism.MainNotions.FormalGroupSystem.logF Formalism.MainNotions.GL3Theta.logF
  rw [PowerSeries.coeff_mk, PowerSeries.coeff_mk, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem cc_logF : PowerSeries.constantCoeff (Formalism.MainNotions.GL3Theta.logF p) = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold Formalism.MainNotions.GL3Theta.logF
  rw [PowerSeries.coeff_mk]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [if_neg]
  exact (pow_pos hp.out.pos _).ne

theorem lg_pt (g : G1 p) (hex : PowerSeries.constantCoeff g.ex = 0) (hinv : PowerSeries.subst g.ex g.l = PowerSeries.X)
    {a : PowerSeries ℂ_[p]} (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.subst (PowerSeries.subst a g.ex) g.l = a := by
  rw [← PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hex)
    (PowerSeries.HasSubst.of_constantCoeff_zero' ha), hinv,
    PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' ha)]

theorem ltIso_of (g : G1 p) (hOk : g.Ok) {c : ℂ_[p]} (hc : c ∈ Wp p) (hc1 : ‖c‖ = 1)
    (hΘ : IntegralW (g.pt (MvPowerSeries.C c * Formalism.MainNotions.GL3Theta.logF p) : MvPowerSeries Unit ℂ_[p]))
    (hΘ1 : ‖PowerSeries.coeff 1 (g.pt (MvPowerSeries.C c * Formalism.MainNotions.GL3Theta.logF p) : PowerSeries ℂ_[p])‖ = 1) :
    LTIso g := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  have hA0 : PowerSeries.constantCoeff (c • Formalism.MainNotions.GL3Theta.logF p) = 0 := by
    rw [PowerSeries.smul_eq_C_mul, map_mul, cc_logF, mul_zero]
  have hAe : (MvPowerSeries.C c * Formalism.MainNotions.GL3Theta.logF p : MvPowerSeries Unit ℂ_[p]) = c • Formalism.MainNotions.GL3Theta.logF p :=
    (MvPowerSeries.smul_eq_C_mul _ _).symm
  rw [hAe] at hΘ hΘ1
  obtain ⟨c0, hc0⟩ := (mem_Wp_iff p c).1 hc
  have hu0 : IsUnit c0 := isUnit_of_norm_eq_one (by rw [hc0]; exact hc1)
  obtain ⟨Θ0, hΘ0'⟩ : ∃ Θ0 : PowerSeries (WW p),
      PowerSeries.map (wToC p) Θ0 = PowerSeries.subst (c • Formalism.MainNotions.GL3Theta.logF p) g.ex := (integralW_iff _).1 hΘ
  have hcc : PowerSeries.constantCoeff (PowerSeries.subst (c • Formalism.MainNotions.GL3Theta.logF p) g.ex : PowerSeries ℂ_[p]) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hA0 _ hex
  have hΘ00 : PowerSeries.constantCoeff Θ0 = 0 := by
    apply wToC_injective p
    rw [map_zero, ← hcc, ← hΘ0', ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map]
  have hΘ01 : IsUnit (PowerSeries.coeff 1 Θ0) := by
    apply isUnit_of_norm_eq_one
    rw [← PowerSeries.coeff_map, hΘ0']
    exact hΘ1
  refine ⟨hu0.unit⁻¹, Θ0.substInvOfIsUnit hΘ01,
    PowerSeries.constantCoeff_substInvOfIsUnit _ _, ?_, ?_⟩
  · rw [PowerSeries.coeff_one_substInvOfIsUnit]
    exact Units.isUnit _
  · set th := Θ0.substInvOfIsUnit hΘ01 with hth
    have hth0 : PowerSeries.constantCoeff th = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
    have hT0 : PowerSeries.constantCoeff (PowerSeries.map (wToC p) th) = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hth0, map_zero]
    have hT : PowerSeries.HasSubst (PowerSeries.map (wToC p) th) := PowerSeries.HasSubst.of_constantCoeff_zero' hT0

    have h1 : PowerSeries.subst (PowerSeries.map (wToC p) th)
        (PowerSeries.subst (c • Formalism.MainNotions.GL3Theta.logF p) g.ex : PowerSeries ℂ_[p]) = PowerSeries.X := by
      have h2 : PowerSeries.subst th Θ0 = PowerSeries.X :=
        PowerSeries.subst_substInvOfIsUnit_right _ hΘ00 hΘ01
      have h3 := congrArg (PowerSeries.map (wToC p)) h2
      have h3' : PowerSeries.map (wToC p) (PowerSeries.subst th Θ0) =
          PowerSeries.subst (PowerSeries.map (wToC p) th) (PowerSeries.map (wToC p) Θ0) :=
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hth0) Θ0
      rw [h3', hΘ0', PowerSeries.map_X] at h3
      exact h3

    have h4 := lg_pt g hex hinv hA0
    have h5 := congrArg (PowerSeries.subst (PowerSeries.map (wToC p) th)) h4
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hcc) hT, h1,
      PowerSeries.X_subst, PowerSeries.subst_smul hT] at h5
    rw [logF_map]
    have hcne : c ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hc1
      exact zero_ne_one hc1
    have hep : wToC p ((hu0.unit⁻¹ : (WW p)ˣ) : WW p) = c⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← hc0]
      nth_rewrite 2 [← hu0.unit_spec]
      rw [← map_mul, Units.inv_mul, map_one]
    rw [hep, h5, ← PowerSeries.smul_eq_C_mul, smul_smul, inv_mul_cancel₀ hcne, one_smul]

end LT

section Lin

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.J

variable {p}

theorem coeff_one_subst {R : Type*} [CommRing R] (a f : PowerSeries R) (ha : PowerSeries.constantCoeff a = 0) :
    PowerSeries.coeff 1 (PowerSeries.subst a f) = PowerSeries.coeff 1 f * PowerSeries.coeff 1 a := by
  rw [PowerSeries.coeff_subst' (PowerSeries.HasSubst.of_constantCoeff_zero' ha), finsum_eq_single _ 1, pow_one, smul_eq_mul]
  intro d hd
  obtain ⟨a', ha'⟩ := PowerSeries.X_dvd_iff.2 ha
  rcases Nat.lt_or_gt_of_ne hd with h | h
  · have : d = 0 := by omega
    subst this
    rw [pow_zero, PowerSeries.coeff_one, if_neg one_ne_zero, smul_zero]
  · rw [ha', mul_pow, PowerSeries.coeff_X_pow_mul', if_neg (by omega), smul_zero]

theorem coeff_one_logF : PowerSeries.coeff 1 (Formalism.MainNotions.GL3Theta.logF p) = 1 := by
  unfold Formalism.MainNotions.GL3Theta.logF
  rw [PowerSeries.coeff_mk, Finset.sum_eq_single 0]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    have h2 : 1 < p ^ (2 * j) := Nat.one_lt_pow (by omega) hp.out.one_lt
    omega
  · intro h
    simp at h

theorem coeff_one_l (g : G1 p) (hW : IsWq g.W g.wq) : PowerSeries.coeff 1 g.l = 1 := by
  have h0 : PowerSeries.constantCoeff g.wq = 1 := by
    have := congrArg PowerSeries.constantCoeff hW
    simpa using this
  unfold G1.l flog
  rw [PowerSeries.coeff_mk, if_neg one_ne_zero, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  unfold omegaW
  simp only [map_mul, map_sub, map_add, map_neg, map_pow, PowerSeries.constantCoeff_inv, PowerSeries.constantCoeff_X, h0]
  simp
  rw [show PowerSeries.constantCoeff (2 : PowerSeries ℂ_[p]) = 2 from map_ofNat _ 2]
  exact mul_inv_cancel₀ two_ne_zero

theorem coeff_one_theta (g : G1 p) (hOk : g.Ok) (c : ℂ_[p]) :
    PowerSeries.coeff 1 (g.pt (MvPowerSeries.C c * Formalism.MainNotions.GL3Theta.logF p) : PowerSeries ℂ_[p]) = c := by
  have hA0 : PowerSeries.constantCoeff (c • Formalism.MainNotions.GL3Theta.logF p) = 0 := by
    rw [PowerSeries.smul_eq_C_mul, map_mul, cc_logF, mul_zero]
  have hAe : (MvPowerSeries.C c * Formalism.MainNotions.GL3Theta.logF p : MvPowerSeries Unit ℂ_[p]) = c • Formalism.MainNotions.GL3Theta.logF p :=
    (MvPowerSeries.smul_eq_C_mul _ _).symm
  rw [hAe]
  have h4 := congrArg (PowerSeries.coeff 1) (lg_pt g hOk.2.2.1 hOk.2.2.2 hA0)
  rw [coeff_one_subst _ _ (PowerSeries.constantCoeff_subst_eq_zero hA0 _ hOk.2.2.1), coeff_one_l g hOk.2.1, one_mul,
    PowerSeries.coeff_smul, coeff_one_logF, smul_eq_mul, mul_one] at h4
  exact h4

theorem ltIso_of' (g : G1 p) (hOk : g.Ok) {c : ℂ_[p]} (hc1 : ‖c‖ = 1)
    (hΘ : IntegralW (g.pt (MvPowerSeries.C c * Formalism.MainNotions.GL3Theta.logF p) : MvPowerSeries Unit ℂ_[p])) : LTIso g := by
  have h1 := coeff_one_theta g hOk c
  have hc : c ∈ Wp p := by
    have : PowerSeries.coeff 1 (g.pt (MvPowerSeries.C c * Formalism.MainNotions.GL3Theta.logF p) : PowerSeries ℂ_[p]) ∈ Wp p :=
      hΘ (Finsupp.single () 1)
    rwa [h1] at this
  exact ltIso_of g hOk hc hc1 hΘ (by rw [h1]; exact hc1)

def ExRat (g : G1 p) : Prop := CoefWf (g.ex : MvPowerSeries Unit ℂ_[p])

end Lin

section ExR

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.MainNotions.J

def ratSub : Subring (PowerSeries ℂ_[p]) := (PowerSeries.map (k0ToC p)).range

variable {p}

theorem mem_ratSub {f : PowerSeries ℂ_[p]} : f ∈ ratSub p ↔ ∀ n, ∃ z : K0 p, k0ToC p z = PowerSeries.coeff n f := by
  constructor
  · rintro ⟨b, rfl⟩ n
    exact ⟨PowerSeries.coeff n b, (PowerSeries.coeff_map _ _ _).symm⟩
  · intro h
    choose b hb using h
    exact ⟨PowerSeries.mk b, by ext n; rw [PowerSeries.coeff_map, PowerSeries.coeff_mk]; exact hb n⟩

theorem C_mem_ratSub {a : ℂ_[p]} (ha : a ∈ Wp p) : algebraMap ℂ_[p] (PowerSeries ℂ_[p]) a ∈ ratSub p := by
  obtain ⟨x, rfl⟩ := (mem_Wp_iff p a).1 ha
  exact ⟨PowerSeries.C (algebraMap (WW p) (K0 p) x), by rw [PowerSeries.map_C, witt_fraction_to_Cp_algebraMap]; rfl⟩

theorem X_mem_ratSub : (PowerSeries.X : PowerSeries ℂ_[p]) ∈ ratSub p := ⟨PowerSeries.X, PowerSeries.map_X _⟩

theorem two_mem_ratSub : (2 : PowerSeries ℂ_[p]) ∈ ratSub p := by
  have := Subring.add_mem _ (Subring.one_mem (ratSub p)) (Subring.one_mem _)
  rwa [one_add_one_eq_two] at this

theorem cc_map (b : PowerSeries (K0 p)) :
    PowerSeries.constantCoeff (PowerSeries.map (k0ToC p) b) = k0ToC p (PowerSeries.constantCoeff b) := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem inv_mem_ratSub {f : PowerSeries ℂ_[p]} (hf : f ∈ ratSub p) : f⁻¹ ∈ ratSub p := by
  obtain ⟨b, rfl⟩ := hf
  refine ⟨b⁻¹, ?_⟩
  by_cases h0 : PowerSeries.constantCoeff b = 0
  · rw [PowerSeries.inv_eq_zero.2 h0, map_zero]
    symm
    rw [PowerSeries.inv_eq_zero, cc_map, h0, map_zero]
  · have h1 : PowerSeries.constantCoeff (PowerSeries.map (k0ToC p) b) ≠ 0 := by
      rw [cc_map]
      exact (map_ne_zero _).2 h0
    rw [PowerSeries.eq_inv_iff_mul_eq_one h1, ← map_mul, PowerSeries.inv_mul_cancel _ h0, map_one]

theorem dX_mem_ratSub {f : PowerSeries ℂ_[p]} (hf : f ∈ ratSub p) : dX f ∈ ratSub p := by
  rw [mem_ratSub] at hf ⊢
  intro n
  obtain ⟨z, hz⟩ := hf (n + 1)
  exact ⟨((n : K0 p) + 1) * z, by unfold dX; rw [PowerSeries.coeff_mk, map_mul, map_add, map_natCast, map_one, hz]⟩

theorem wq_mem_ratSub {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hW : IsWq W wq)
    (h1 : W.a₁ ∈ Wp p) (h2 : W.a₂ ∈ Wp p) (h3 : W.a₃ ∈ Wp p) (h4 : W.a₄ ∈ Wp p) (h6 : W.a₆ ∈ Wp p) :
    wq ∈ ratSub p := by
  rw [mem_ratSub]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    choose! b hb using ih
    set wn : PowerSeries ℂ_[p] := PowerSeries.mk fun m => if m < n then PowerSeries.coeff m wq else 0 with hwn_def
    have hwn : wn ∈ ratSub p := mem_ratSub.2 fun m => by
      rw [hwn_def, PowerSeries.coeff_mk]
      split_ifs with h
      · exact ⟨b m, hb m h⟩
      · exact ⟨0, map_zero _⟩
    have hd : (PowerSeries.X : PowerSeries ℂ_[p]) ^ n ∣ wq - wn := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      rw [map_sub, hwn_def, PowerSeries.coeff_mk, if_pos hm, sub_self]
    obtain ⟨r, hr⟩ := hd
    let c := algebraMap ℂ_[p] (PowerSeries ℂ_[p])
    let Φ : PowerSeries ℂ_[p] → PowerSeries ℂ_[p] := fun w =>
      1 + c W.a₁ * PowerSeries.X * w + c W.a₂ * PowerSeries.X ^ 2 * w + c W.a₃ * PowerSeries.X ^ 3 * w ^ 2 +
        c W.a₄ * PowerSeries.X ^ 4 * w ^ 2 + c W.a₆ * PowerSeries.X ^ 6 * w ^ 3
    have hΦ : wq = Φ wq := hW
    have e1 : Φ wq - Φ wn = PowerSeries.X * (wq - wn) * (c W.a₁ + c W.a₂ * PowerSeries.X +
        c W.a₃ * PowerSeries.X ^ 2 * (wq + wn) + c W.a₄ * PowerSeries.X ^ 3 * (wq + wn) +
        c W.a₆ * PowerSeries.X ^ 5 * (wq ^ 2 + wq * wn + wn ^ 2)) := by
      simp only [Φ]
      ring
    have e2 : PowerSeries.coeff n (Φ wq - Φ wn) = 0 := by
      rw [e1, hr]
      have : ∀ Q : PowerSeries ℂ_[p], PowerSeries.X * (PowerSeries.X ^ n * r) * Q = PowerSeries.X ^ (n + 1) * (r * Q) := by
        intro Q
        ring
      rw [this, PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
    have e3 : PowerSeries.coeff n wq = PowerSeries.coeff n (Φ wn) := by
      rw [map_sub, sub_eq_zero] at e2
      rw [← e2, ← hΦ]
    have hmem : Φ wn ∈ ratSub p := by
      have hX := X_mem_ratSub (p := p)
      simp only [Φ]
      exact Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ (Subring.add_mem _ (Subring.one_mem _)
        (Subring.mul_mem _ (Subring.mul_mem _ (C_mem_ratSub h1) hX) hwn))
        (Subring.mul_mem _ (Subring.mul_mem _ (C_mem_ratSub h2) (Subring.pow_mem _ hX 2)) hwn))
        (Subring.mul_mem _ (Subring.mul_mem _ (C_mem_ratSub h3) (Subring.pow_mem _ hX 3)) (Subring.pow_mem _ hwn 2)))
        (Subring.mul_mem _ (Subring.mul_mem _ (C_mem_ratSub h4) (Subring.pow_mem _ hX 4)) (Subring.pow_mem _ hwn 2)))
        (Subring.mul_mem _ (Subring.mul_mem _ (C_mem_ratSub h6) (Subring.pow_mem _ hX 6)) (Subring.pow_mem _ hwn 3))
    rw [e3]
    exact mem_ratSub.1 hmem n

theorem omega_mem_ratSub {W : WeierstrassCurve ℂ_[p]} {wq : PowerSeries ℂ_[p]} (hwq : wq ∈ ratSub p)
    (h1 : W.a₁ ∈ Wp p) (h3 : W.a₃ ∈ Wp p) : omegaW W wq ∈ ratSub p := by
  have hX := X_mem_ratSub (p := p)
  show (-(2 : PowerSeries ℂ_[p]) * wq - PowerSeries.X * dX wq) *
    (wq * (algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₁ * PowerSeries.X +
      algebraMap ℂ_[p] (PowerSeries ℂ_[p]) W.a₃ * PowerSeries.X ^ 3 * wq - 2))⁻¹ ∈ ratSub p
  exact Subring.mul_mem _
    (Subring.sub_mem _ (Subring.mul_mem _ (Subring.neg_mem _ two_mem_ratSub) hwq) (Subring.mul_mem _ hX (dX_mem_ratSub hwq)))
    (inv_mem_ratSub (Subring.mul_mem _ hwq (Subring.sub_mem _ (Subring.add_mem _ (Subring.mul_mem _ (C_mem_ratSub h1) hX)
      (Subring.mul_mem _ (Subring.mul_mem _ (C_mem_ratSub h3) (Subring.pow_mem _ hX 3)) hwq)) two_mem_ratSub)))

theorem l_mem_ratSub (g : G1 p) (hW : IsWq g.W g.wq) (hM : ModelOverW g.lam g.abelian₂ g.C) : g.l ∈ ratSub p := by
  have hω : omegaW g.W g.wq ∈ ratSub p :=
    omega_mem_ratSub (wq_mem_ratSub hW hM.1 hM.2.1 hM.2.2.1 hM.2.2.2.1 hM.2.2.2.2) hM.1 hM.2.2.1
  rw [mem_ratSub] at hω ⊢
  intro n
  unfold G1.l flog
  rw [PowerSeries.coeff_mk]
  split_ifs with h
  · exact ⟨0, map_zero _⟩
  · obtain ⟨z, hz⟩ := hω (n - 1)
    exact ⟨z / (n : K0 p), by rw [map_div₀, map_natCast, hz]⟩

theorem exRat_of (g : G1 p) (hOk : g.Ok) (hM : ModelOverW g.lam g.abelian₂ g.C) : ExRat g := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  obtain ⟨l0, hl0⟩ := l_mem_ratSub g hOk.2.1 hM
  have hl00 : PowerSeries.constantCoeff l0 = 0 := by
    apply (k0ToC p).injective
    rw [map_zero, ← cc_map]
    exact (congrArg PowerSeries.constantCoeff hl0).trans (cc_l g)
  have hl01 : IsUnit (PowerSeries.coeff 1 l0) := by
    apply IsUnit.mk0
    intro h0
    have h1 := coeff_one_l g hOk.2.1
    have h2 : PowerSeries.coeff 1 (PowerSeries.map (k0ToC p) l0) = PowerSeries.coeff 1 g.l := congrArg _ hl0
    rw [PowerSeries.coeff_map, h0, map_zero, h1] at h2
    exact zero_ne_one h2
  have he00 : PowerSeries.constantCoeff (l0.substInvOfIsUnit hl01) = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hE0 : PowerSeries.constantCoeff (PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)) = 0 := by
    rw [cc_map, he00, map_zero]
  have hE1 : PowerSeries.HasSubst (PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hE0
  have hL : PowerSeries.HasSubst g.l := PowerSeries.HasSubst.of_constantCoeff_zero' (cc_l g)
  have h3 : PowerSeries.subst (PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)) g.l = PowerSeries.X := by
    have h2 : PowerSeries.subst (l0.substInvOfIsUnit hl01) l0 = PowerSeries.X :=
      PowerSeries.subst_substInvOfIsUnit_right _ hl00 hl01
    have h4 := congrArg (PowerSeries.map (k0ToC p)) h2
    have h4' : PowerSeries.map (k0ToC p) (PowerSeries.subst (l0.substInvOfIsUnit hl01) l0) =
        PowerSeries.subst (PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)) (PowerSeries.map (k0ToC p) l0) :=
      PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' he00) l0
    rw [h4', PowerSeries.map_X] at h4
    rw [← h4]
    exact congrArg _ hl0.symm
  have h5 : PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01) = g.ex := by
    calc PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)
        = PowerSeries.subst (PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)) (PowerSeries.X : PowerSeries ℂ_[p]) :=
          (PowerSeries.subst_X hE1).symm
      _ = PowerSeries.subst (PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)) (PowerSeries.subst g.l g.ex) := by
          rw [ex_l g hex hinv]
      _ = PowerSeries.subst (PowerSeries.subst (PowerSeries.map (k0ToC p) (l0.substInvOfIsUnit hl01)) g.l) g.ex :=
          PowerSeries.subst_comp_subst_apply hL hE1 _
      _ = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[p]) g.ex := by rw [h3]
      _ = g.ex := PowerSeries.X_subst _
  exact (coefWf_iff _).2 ⟨l0.substInvOfIsUnit hl01, h5⟩

end ExR

end Formalism.L2.G.Pend
