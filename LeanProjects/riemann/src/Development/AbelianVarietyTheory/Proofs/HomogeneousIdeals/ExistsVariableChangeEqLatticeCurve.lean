import Mathlib

open UpperHalfPlane ModularForm MatrixGroups Filter EisensteinSeries
open scoped Real Topology

noncomputable section

namespace GlobalTheory

def latticeCurve (L : PeriodPair) : WeierstrassCurve ℂ := ⟨0, 0, 0, -L.g₂ / 4, -L.g₃ / 4⟩

lemma latticeCurve_Δ (L : PeriodPair) : (latticeCurve L).Δ = L.g₂ ^ 3 - 27 * L.g₃ ^ 2 := by
  simp only [latticeCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma latticeCurve_c₄ (L : PeriodPair) : (latticeCurve L).c₄ = 12 * L.g₂ := by
  simp only [latticeCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

def periodPairOfTau (τ : ℍ) : PeriodPair where
  ω₁ := τ
  ω₂ := 1
  indep := by
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h1 := congrArg Complex.im h
    have h2 := congrArg Complex.re h
    simp [τ.im_ne_zero] at h1
    simp [h1] at h2
    exact ⟨h1, h2⟩

lemma mem_lattice_periodPairOfTau (τ : ℍ) (x : ℂ) :
    x ∈ (periodPairOfTau τ).lattice ↔ ∃ m n : ℤ, 1 * (m * (τ : ℂ) + n) = x := by
  simp [PeriodPair.mem_lattice, periodPairOfTau]

theorem exists_lattice_eq_mul_tau (L : PeriodPair) :
    ∃ (a : ℂ) (τ : ℍ), a ≠ 0 ∧ ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  have hi := LinearIndependent.pair_iff.mp L.indep
  have h2 : L.ω₂ ≠ 0 := fun h ↦ by simpa using (hi 0 1 (by simp [h])).2
  have him : (L.ω₁ / L.ω₂).im ≠ 0 := fun h ↦ by
    have h3 : L.ω₁ / L.ω₂ = ((L.ω₁ / L.ω₂).re : ℂ) := Complex.ext (by simp) (by simpa using h)
    have := (hi 1 (-(L.ω₁ / L.ω₂).re) (by
      simp only [Complex.real_smul, Complex.ofReal_neg, ← h3]
      field_simp
      simp)).1
    simp at this
  rcases lt_or_gt_of_ne him with h | h
  · refine ⟨L.ω₂, ⟨-(L.ω₁ / L.ω₂), by simpa using h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨-m, n, by push_cast; field_simp⟩
  · refine ⟨L.ω₂, ⟨L.ω₁ / L.ω₂, h⟩, h2, fun x ↦ ?_⟩
    rw [PeriodPair.mem_lattice]
    constructor
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩
    · rintro ⟨m, n, rfl⟩
      exact ⟨m, n, by field_simp⟩

section

variable {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
  (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x)
include ha h

theorem latticeG_eq_E {k : ℕ} (hk : 3 ≤ k) :
    L.G k = 2 * riemannZeta k * E hk τ / a ^ k := by
  let e : (Fin 2 → ℤ) → L.lattice := fun v ↦ ⟨a * (v 0 * (τ : ℂ) + v 1), (h _).mpr ⟨_, _, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro v w hvw
      have h0 : (v 0 * (τ : ℂ) + v 1) = w 0 * (τ : ℂ) + w 1 :=
        mul_left_cancel₀ ha (congrArg Subtype.val hvw)
      have h1 := congrArg Complex.im h0
      simp [τ.im_ne_zero] at h1
      rw [h1, add_right_inj] at h0
      ext i
      fin_cases i
      · exact h1
      · exact_mod_cast h0
    · rintro ⟨x, hx⟩
      obtain ⟨m, n, rfl⟩ := (h x).mp hx
      exact ⟨![m, n], rfl⟩
  have h1 := tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ
  have h2 : E hk τ = (1 / 2 : ℂ) * eisensteinSeries (N := 1) 0 k τ := rfl
  rw [PeriodPair.G, ← (Equiv.ofBijective e he).tsum_eq, h2]
  have h3 : ∀ v, (((Equiv.ofBijective e he v : L.lattice) : ℂ) ^ k)⁻¹ =
      (a ^ k)⁻¹ * eisSummand k v τ := fun v ↦ by
    simp [e, eisSummand, mul_pow, mul_comm]
  simp_rw [h3]
  rw [tsum_mul_left, h1]
  field_simp

theorem g₂_eq_E₄ : L.g₂ = 4 * π ^ 4 / 3 * E₄ τ / a ^ 4 := by
  have := latticeG_eq_E ha h (k := 4) (by norm_num)
  rw [PeriodPair.g₂, this, Nat.cast_ofNat, riemannZeta_four]
  ring

theorem g₃_eq_E₆ : L.g₃ = 8 * π ^ 6 / 27 * E₆ τ / a ^ 6 := by
  have := latticeG_eq_E ha h (k := 6) (by norm_num)
  have h6 : riemannZeta 6 = π ^ 6 / 945 := by
    have := riemannZeta_two_mul_nat (k := 3) (by norm_num)
    rw [show bernoulli (2 * 3) = 1 / 42 by decide +kernel] at this
    norm_num [Nat.factorial] at this
    rw [this]
    ring
  rw [PeriodPair.g₃, this, Nat.cast_ofNat, h6]
  ring

theorem latticeCurve_Δ_eq_discriminant :
    (latticeCurve L).Δ = (2 * π / a) ^ 12 * discriminant τ := by
  rw [latticeCurve_Δ, g₂_eq_E₄ ha h, g₃_eq_E₆ ha h, discriminant_eq_E₄_cube_sub_E₆_sq]
  field_simp
  ring

end

theorem latticeCurve_Δ_ne_zero (L : PeriodPair) : (latticeCurve L).Δ ≠ 0 := by
  obtain ⟨a, τ, ha, h⟩ := exists_lattice_eq_mul_tau L
  rw [latticeCurve_Δ_eq_discriminant ha h]
  have := discriminant_ne_zero τ
  have := Real.pi_ne_zero
  simp [*]

instance latticeCurve_isElliptic (L : PeriodPair) : (latticeCurve L).IsElliptic :=
  ⟨(latticeCurve_Δ_ne_zero L).isUnit⟩

theorem latticeCurve_j {L : PeriodPair} {a : ℂ} {τ : ℍ} (ha : a ≠ 0)
    (h : ∀ x, x ∈ L.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x) :
    (latticeCurve L).j = E₄ τ ^ 3 / discriminant τ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    latticeCurve_Δ_eq_discriminant ha h, latticeCurve_c₄, g₂_eq_E₄ ha h]
  have := discriminant_ne_zero τ
  have : (π : ℂ) ≠ 0 := by simpa using Real.pi_ne_zero
  field_simp
  ring

lemma tendsto_E₄_atImInfty : Tendsto (E₄ : ℍ → ℂ) atImInfty (𝓝 1) := by
  have h0 : valueAtInfty E₄ = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero E₄ one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL)]
    exact E_qExpansion_coeff_zero _ ⟨2, rfl⟩
  obtain ⟨c, hc, h⟩ := ModularFormClass.exp_decay_sub_atImInfty' (E₄)
  rw [h0] at h
  have h2 : Tendsto (fun τ : ℍ ↦ Real.exp (-c * τ.im)) atImInfty (𝓝 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    exact Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_comap
  simpa using (h.trans_tendsto h2).add_const 1

theorem exists_E₄_cube_div_discriminant_eq (c : ℂ) :
    ∃ τ : ℍ, E₄ τ ^ 3 / discriminant τ = c := by
  by_contra! hc
  let g : ModularForm 𝒮ℒ 12 := ModularForm.mcast (by decide) (E₄.pow 3) -
    c • (CuspForm.discriminant : ModularForm 𝒮ℒ 12)
  have hg : ∀ τ, g τ = E₄ τ ^ 3 - c * discriminant τ := fun τ ↦ by
    simp [g]
    rfl
  have hg0 : ∀ τ, g τ ≠ 0 := fun τ h ↦ hc τ (by
    rw [hg] at h
    rw [div_eq_iff (discriminant_ne_zero τ)]
    linear_combination h)
  have hlim : Tendsto (g : ℍ → ℂ) atImInfty (𝓝 1) := by
    have := (tendsto_E₄_atImInfty.pow 3).sub
      ((show Tendsto discriminant atImInfty (𝓝 0) from discriminant_isZeroAtImInfty).const_mul c)
    simpa [funext hg] using this
  have hsl : ∀ γ : SL(2, ℤ),
      ((1 : ℍ → ℂ) / g) ∣[(0 : ℤ) - 12] γ = (1 : ℍ → ℂ) / g := fun γ ↦ by
    have hγ : (γ : GL (Fin 2) ℝ) ∈ 𝒮ℒ := ⟨γ, rfl⟩
    rw [div_slash_SL2, is_invariant_one, SL_slash, SlashInvariantForm.slash_action_eqn _ _ hγ]
  let f : ModularForm 𝒮ℒ ((0 : ℤ) - 12) :=
    { toFun := (1 : ℍ → ℂ) / g
      slash_action_eq' := fun _ ⟨γ, hγ⟩ ↦ hγ ▸ hsl γ
      holo' := mdifferentiable_const.div g.holo' hg0
      bdd_at_cusps' := fun {c} hc ↦ by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
        rw [OnePoint.isBoundedAt_iff_forall_SL2Z hc]
        intro γ _
        rw [hsl γ]
        exact ((tendsto_const_nhds (x := (1 : ℂ))).div hlim one_ne_zero).isBigO_one ℝ }
  have := congrFun (ModularFormClass.levelOne_neg_weight_eq_zero (by norm_num) f) UpperHalfPlane.I
  have h3 : (1 : ℂ) / g UpperHalfPlane.I = 0 := this
  simp [hg0] at h3

theorem exists_variableChange_eq_latticeCurve (W : WeierstrassCurve ℂ) [W.IsElliptic] :
    ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ), C • W = latticeCurve L := by
  obtain ⟨τ, hτ⟩ := exists_E₄_cube_div_discriminant_eq W.j
  refine ⟨periodPairOfTau τ, W.exists_variableChange_of_j_eq _ ?_⟩
  rw [latticeCurve_j one_ne_zero (mem_lattice_periodPairOfTau τ), hτ]

end GlobalTheory
