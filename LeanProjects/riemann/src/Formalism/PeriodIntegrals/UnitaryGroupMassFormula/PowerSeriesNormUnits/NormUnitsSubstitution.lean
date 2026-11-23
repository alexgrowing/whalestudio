import Mathlib
import Formalism.PeriodIntegrals.PhNormUnits
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PowerSeriesNormUnits.Development
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerBis

noncomputable section

open Classical Filter Topology

namespace PI.PhNormUnits.UnitaryGroupMassFormula

open PI.PhNormUnits

namespace PAdicPowerSeriesCoefficients

variable {p : ℕ} [Fact p.Prime]

noncomputable def intRing (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] :=
  _root_.UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing p

theorem integral_iff {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    IntegralMv F ↔ ∃ G : MvPowerSeries σ (intRing p), MvPowerSeries.map (intRing p).subtype G = F := by
  constructor
  · intro h
    refine ⟨fun e => ⟨MvPowerSeries.coeff e F, h e⟩, ?_⟩
    ext e
    rfl
  · rintro ⟨G, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e G).2

theorem integral_mul {σ : Type*} {F G : MvPowerSeries σ ℂ_[p]} (hF : IntegralMv F) (hG : IntegralMv G) :
    IntegralMv (F * G) := by
  obtain ⟨F', rfl⟩ := (integral_iff F).1 hF
  obtain ⟨G', rfl⟩ := (integral_iff G).1 hG
  exact (integral_iff _).2 ⟨F' * G', map_mul _ _ _⟩

theorem integral_one {σ : Type*} : IntegralMv (1 : MvPowerSeries σ ℂ_[p]) :=
  (integral_iff _).2 ⟨1, map_one _⟩

theorem constantCoeff_lift {σ : Type*} (G : MvPowerSeries σ (intRing p)) :
    ((MvPowerSeries.constantCoeff G : intRing p) : ℂ_[p]) =
      MvPowerSeries.constantCoeff (MvPowerSeries.map (intRing p).subtype G) := by
  rw [MvPowerSeries.constantCoeff_map]
  rfl

theorem integral_of_mul_eq_one {σ : Type*} {W V : MvPowerSeries σ ℂ_[p]} (hW : IntegralMv W)
    (h1 : MvPowerSeries.constantCoeff W = 1) (hWV : W * V = 1) : IntegralMv V := by
  obtain ⟨W', rfl⟩ := (integral_iff W).1 hW
  have hc : MvPowerSeries.constantCoeff W' = 1 := by
    apply Subtype.ext
    rw [constantCoeff_lift, h1]
    rfl
  have hu : IsUnit W' := MvPowerSeries.isUnit_iff_constantCoeff.2 (by rw [hc]; exact isUnit_one)
  obtain ⟨U, hU⟩ : ∃ U, W' * U = 1 := ⟨↑hu.unit⁻¹, hu.mul_val_inv⟩
  refine (integral_iff V).2 ⟨U, ?_⟩
  have h2 : MvPowerSeries.map (intRing p).subtype W' * MvPowerSeries.map (intRing p).subtype U = 1 := by
    rw [← map_mul, hU, map_one]
  linear_combination V * h2 - (MvPowerSeries.map (intRing p).subtype U) * hWV

theorem integral_subst {σ τ : Type*} [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p])
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (haI : ∀ i, IntegralMv (a i))
    {f : MvPowerSeries σ ℂ_[p]} (hf : IntegralMv f) : IntegralMv (MvPowerSeries.subst a f) := by
  choose a' ha' using fun i => (integral_iff (a i)).1 (haI i)
  obtain ⟨f', rfl⟩ := (integral_iff f).1 hf
  have h0 : ∀ i, MvPowerSeries.constantCoeff (a' i) = 0 := by
    intro i
    apply Subtype.ext
    rw [constantCoeff_lift, ha', ha0]
    rfl
  have hs : MvPowerSeries.HasSubst a' := MvPowerSeries.hasSubst_of_constantCoeff_zero h0
  refine (integral_iff _).2 ⟨MvPowerSeries.subst a' f', ?_⟩
  rw [MvPowerSeries.map_subst hs]
  simp only [ha']

theorem coeff_pow_eq_zero {σ R : Type*} [CommRing R] {F : MvPowerSeries σ R}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    ∀ (d : ℕ) (α : σ →₀ ℕ), Finsupp.degree α < d → MvPowerSeries.coeff α (F ^ d) = 0 := by
  intro d
  induction d with
  | zero => intro α h; omega
  | succ d ih =>
    intro α h
    rw [pow_succ', MvPowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    rintro ⟨β, γ⟩ hβγ
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hβγ
    dsimp only
    by_cases hβ : β = 0
    · subst hβ
      simp [hF]
    · have hb : Finsupp.degree β ≠ 0 := fun h0 => hβ ((Finsupp.degree_eq_zero_iff β).1 h0)
      have hdeg : Finsupp.degree α = Finsupp.degree β + Finsupp.degree γ := by
        rw [← hβγ, map_add]
      rw [ih γ (by omega), mul_zero]

theorem coeff_expMv {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (expMv F) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1), MvPowerSeries.coeff α (F ^ n) / (n.factorial : ℂ_[p]) :=
  rfl

theorem sum_eq_degree {σ : Type*} (α : σ →₀ ℕ) : (α.sum fun _ k => k) = Finsupp.degree α := rfl

theorem constantCoeff_expMv {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) :
    MvPowerSeries.constantCoeff (expMv F) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_expMv]
  simp

theorem expMv_eq {σ : Type*} {F : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv F = PowerSeries.subst F (PowerSeries.exp ℂ_[p]) := by
  ext α
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1)), coeff_expMv]
  · apply Finset.sum_congr rfl
    intro d _
    rw [PowerSeries.coeff_exp, smul_eq_mul, map_div₀, map_one, map_natCast]
    ring
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hd
    rw [coeff_pow_eq_zero hF d α (by rw [← sum_eq_degree]; omega), smul_zero]

theorem exp_X0_add_X1 :
    PowerSeries.subst (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p])
        (PowerSeries.exp ℂ_[p]) =
      PowerSeries.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) (PowerSeries.exp ℂ_[p]) *
        PowerSeries.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) (PowerSeries.exp ℂ_[p]) := by
  ext e
  rw [PowerSeries.coeff_subst_X_zero_add_X_one, PowerSeries.coeff_subst_X_zero_subst_mul_X_one]
  simp only [PowerSeries.coeff_exp, map_div₀, map_one, map_natCast]
  rw [Nat.cast_add_choose]
  have h1 : ((e 0).factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h2 : ((e 1).factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  have h3 : ((e 0 + e 1).factorial : ℂ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  field_simp

theorem subst_exp {σ τ : Type*} {b : σ → MvPowerSeries τ ℂ_[p]} (hb : MvPowerSeries.HasSubst b)
    {a : MvPowerSeries σ ℂ_[p]} (ha : MvPowerSeries.constantCoeff a = 0) :
    MvPowerSeries.subst b (PowerSeries.subst a (PowerSeries.exp ℂ_[p])) =
      PowerSeries.subst (MvPowerSeries.subst b a) (PowerSeries.exp ℂ_[p]) := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero ha).const hb]

theorem exp_add {σ : Type*} {F G : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) :
    PowerSeries.subst (F + G) (PowerSeries.exp ℂ_[p]) =
      PowerSeries.subst F (PowerSeries.exp ℂ_[p]) * PowerSeries.subst G (PowerSeries.exp ℂ_[p]) := by
  have hb : MvPowerSeries.HasSubst ![F, G] :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun i => by fin_cases i <;> simp [hF, hG])
  have h0 : MvPowerSeries.subst ![F, G] (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) ℂ_[p]) = F := by
    rw [MvPowerSeries.subst_X hb]; rfl
  have h1 : MvPowerSeries.subst ![F, G] (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) = G := by
    rw [MvPowerSeries.subst_X hb]; rfl
  have h01 : MvPowerSeries.subst ![F, G] (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) ℂ_[p]) =
      F + G := by
    rw [MvPowerSeries.subst_add hb, h0, h1]
  rw [← h01, ← subst_exp hb (by simp), exp_X0_add_X1, MvPowerSeries.subst_mul hb,
    subst_exp hb (by simp), subst_exp hb (by simp), h0, h1]

theorem expMv_add {σ : Type*} {F G : MvPowerSeries σ ℂ_[p]} (hF : MvPowerSeries.constantCoeff F = 0)
    (hG : MvPowerSeries.constantCoeff G = 0) : expMv (F + G) = expMv F * expMv G := by
  rw [expMv_eq (by rw [map_add, hF, hG, add_zero]), expMv_eq hF, expMv_eq hG, exp_add hF hG]

theorem expMv_zero {σ : Type*} : expMv (0 : MvPowerSeries σ ℂ_[p]) = 1 := by
  have h := expMv_add (F := (0 : MvPowerSeries σ ℂ_[p])) (G := 0) (map_zero _) (map_zero _)
  rw [add_zero] at h

  have hu : IsUnit (expMv (0 : MvPowerSeries σ ℂ_[p])) :=
    MvPowerSeries.isUnit_iff_constantCoeff.2 (by rw [constantCoeff_expMv]; exact isUnit_one)
  have h' : expMv (0 : MvPowerSeries σ ℂ_[p]) * 1 = expMv 0 * expMv 0 := by rw [mul_one]; exact h
  exact (hu.mul_left_cancel h').symm

theorem simeq_refl {σ : Type*} (f : MvPowerSeries σ ℂ_[p]) : Simeq f f := by
  refine ⟨by simp, ?_⟩
  rw [sub_self, expMv_zero]
  exact integral_one

theorem simeq_symm {σ : Type*} {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq g f := by
  obtain ⟨h0, hI⟩ := h
  have h0' : MvPowerSeries.constantCoeff (g - f) = 0 := by
    rw [show g - f = -(f - g) by ring, map_neg, h0, neg_zero]
  refine ⟨h0', integral_of_mul_eq_one hI (constantCoeff_expMv _) ?_⟩
  rw [← expMv_add h0 h0', show f - g + (g - f) = 0 by ring, expMv_zero]

theorem simeq_trans {σ : Type*} {f g h : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq g h) :
    Simeq f h := by
  have e : f - h = (f - g) + (g - h) := by ring
  refine ⟨by rw [e, map_add, h1.1, h2.1, add_zero], ?_⟩
  rw [e, expMv_add h1.1 h2.1]
  exact integral_mul h1.2 h2.2

theorem simeq_add {σ : Type*} {f g h k : MvPowerSeries σ ℂ_[p]} (h1 : Simeq f g) (h2 : Simeq h k) :
    Simeq (f + h) (g + k) := by
  have e : f + h - (g + k) = (f - g) + (h - k) := by ring
  refine ⟨by rw [e, map_add, h1.1, h2.1, add_zero], ?_⟩
  rw [e, expMv_add h1.1 h2.1]
  exact integral_mul h1.2 h2.2

theorem simeq_neg {σ : Type*} {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) : Simeq (-f) (-g) := by
  have h' := simeq_symm h
  have e : -f - -g = g - f := by ring
  exact ⟨by rw [e]; exact h'.1, by rw [e]; exact h'.2⟩

theorem simeq_iff_sub {σ : Type*} {f g : MvPowerSeries σ ℂ_[p]} : Simeq f g ↔ Simeq (f - g) 0 := by
  simp only [Simeq, sub_zero]

theorem simeq_subst {σ τ : Type*} [Finite σ] (a : σ → MvPowerSeries τ ℂ_[p])
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (haI : ∀ i, IntegralMv (a i))
    {f g : MvPowerSeries σ ℂ_[p]} (h : Simeq f g) :
    Simeq (MvPowerSeries.subst a f) (MvPowerSeries.subst a g) := by
  have hs : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  unfold Simeq
  rw [← MvPowerSeries.subst_sub hs]
  have h0 : MvPowerSeries.constantCoeff (MvPowerSeries.subst a (f - g)) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hs ha0 h.1
  refine ⟨h0, ?_⟩
  rw [expMv_eq h0, ← subst_exp hs h.1, ← expMv_eq h.1]
  exact integral_subst a ha0 haI h.2

theorem tendsto_coeff_mul {σ : Type*} {F G : ℕ → MvPowerSeries σ ℂ_[p]} {f g : MvPowerSeries σ ℂ_[p]}
    (hF : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k)) atTop (𝓝 (MvPowerSeries.coeff e f)))
    (hG : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (G k)) atTop (𝓝 (MvPowerSeries.coeff e g)))
    (e : σ →₀ ℕ) :
    Tendsto (fun k => MvPowerSeries.coeff e (F k * G k)) atTop (𝓝 (MvPowerSeries.coeff e (f * g))) := by
  simp only [MvPowerSeries.coeff_mul]
  exact tendsto_finsetSum _ fun i _ => (hF i.1).mul (hG i.2)

theorem tendsto_coeff_pow {σ : Type*} {F : ℕ → MvPowerSeries σ ℂ_[p]} {f : MvPowerSeries σ ℂ_[p]}
    (hF : ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k)) atTop (𝓝 (MvPowerSeries.coeff e f)))
    (n : ℕ) :
    ∀ e, Tendsto (fun k => MvPowerSeries.coeff e (F k ^ n)) atTop (𝓝 (MvPowerSeries.coeff e (f ^ n))) := by
  induction n with
  | zero => intro e; simp only [pow_zero]; exact tendsto_const_nhds
  | succ n ih => intro e; simp only [pow_succ]; exact tendsto_coeff_mul ih hF e

theorem continuous_zc : Continuous (zc (p := p)) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

end PAdicPowerSeriesCoefficients

open PAdicPowerSeriesCoefficients

theorem norm_units_equivalence : CalcEquiv := by
  intro p _ σ f g h k
  exact ⟨simeq_refl f, simeq_symm, simeq_trans, simeq_add, simeq_neg, simeq_iff_sub⟩

theorem norm_units_substitution : CalcSubst := by
  intro p _ σ τ _ a ha0 haI
  exact ⟨fun f g h => simeq_subst a ha0 haI h, fun f hf => integral_subst a ha0 haI hf⟩

theorem norm_units_closed_form : CalcClosed := by
  intro p _ σ F f hF
  refine ⟨fun h => ⟨?_, fun α => ?_⟩, fun h e => ?_⟩
  · rw [sub_zero, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    have hz : ∀ k, MvPowerSeries.coeff 0 (F k) = 0 := fun k => by
      have := (h k).1
      rwa [sub_zero, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply] at this
    refine tendsto_nhds_unique (hF 0) ?_
    simp only [hz]
    exact tendsto_const_nhds
  · have hk : ∀ k, ‖MvPowerSeries.coeff α (expMv (F k))‖ ≤ 1 := fun k => by
      have := (h k).2 α
      rw [sub_zero] at this
      exact this
    have ht : Tendsto (fun k => MvPowerSeries.coeff α (expMv (F k))) atTop
        (𝓝 (MvPowerSeries.coeff α (expMv f))) := by
      simp only [coeff_expMv]
      exact tendsto_finsetSum _ fun n _ => (tendsto_coeff_pow hF n α).div_const _
    show ‖MvPowerSeries.coeff α (expMv (f - 0))‖ ≤ 1
    rw [sub_zero]
    exact le_of_tendsto' ht.norm hk
  · exact le_of_tendsto' (hF e).norm fun k => h k e

theorem natCast_dense_p_adic : NatDense := by
  intro p _ n
  have hn : n ∈ closure (Set.range (Nat.cast : ℕ → ℤ_[p])) := PadicInt.denseRange_natCast n
  obtain ⟨x, hx, hlim⟩ := mem_closure_iff_seq_limit.1 hn
  choose u hu using hx
  refine ⟨u, ?_⟩
  have e : (fun k => ((u k : ℕ) : ℂ_[p])) = fun k => zc (x k) := by
    funext k
    rw [← hu k]
    simp [zc]
  rw [e]
  exact (continuous_zc.tendsto n).comp hlim

theorem norm_units_zp_scaling : CalcZpScale := by
  intro p _ σ f g n h
  have hD : Simeq (f - g) 0 := simeq_iff_sub.1 h
  have hm : ∀ m : ℕ, Simeq (MvPowerSeries.C (m : ℂ_[p]) * (f - g)) 0 := by
    intro m
    induction m with
    | zero =>
      simp only [Nat.cast_zero, map_zero, zero_mul]
      exact simeq_refl _
    | succ m ih =>
      have := simeq_add ih hD
      rw [add_zero] at this
      convert this using 1
      push_cast
      rw [map_add, map_one]
      ring
  obtain ⟨u, hu⟩ := natCast_dense_p_adic p n
  have hlim := (norm_units_closed_form p σ (fun k => MvPowerSeries.C (u k : ℂ_[p]) * (f - g))
    (MvPowerSeries.C (zc n) * (f - g)) (fun e => by
      simp only [MvPowerSeries.coeff_C_mul]
      exact hu.mul_const _)).1 (fun k => hm (u k))
  rw [simeq_iff_sub, ← mul_sub]
  exact hlim

end PI.PhNormUnits.UnitaryGroupMassFormula
