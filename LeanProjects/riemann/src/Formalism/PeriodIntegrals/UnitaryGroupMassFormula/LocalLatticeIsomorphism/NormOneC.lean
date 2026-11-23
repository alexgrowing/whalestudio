import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.NormOneB

noncomputable section
open scoped BigOperators
open NumberField

namespace PI.KLW.NO

theorem generic_pair {K : Type} [Field K] [NumberField K] {c : K →+* K} (hc : ∀ x, c (c x) = x)
    {p : ℕ} (hp : p.Prime) {ι : Type} [Fintype ι] {L : Set (ι → K)} (hU : Unimod K c p L)
    {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) (v₀ : ι → K) :
    ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
  have key : ∀ q : ℕ, Nat.Coprime q p → q ≠ 0 → (q : K) * hf c v₀ x ≠ 1 → hf c v₀ y ≠ (q : K) →
      ∃ x₁ ∈ L, ∃ y₁ ∈ L, hf c x₁ y₁ = 1 ∧ hf c v₀ x₁ ≠ 1 ∧ hf c v₀ y₁ ≠ 1 := by
    intro q hq hq0 hX hY
    have hqK : (q : K) ≠ 0 := by exact_mod_cast hq0
    refine ⟨(q : K) • x, hU.smul_mem (Rp_natCast q) hx, (q : K)⁻¹ • y,
      hU.smul_mem (Rp_inv_natCast hq) hy, ?_, ?_, ?_⟩
    · rw [hf_smul_left, hf_smul_right, hxy, map_inv₀, map_natCast, mul_one, mul_inv_cancel₀ hqK]
    · rw [hf_smul_right, map_natCast]; exact hX
    · rw [hf_smul_right, map_inv₀, map_natCast]
      intro h; apply hY
      rw [inv_mul_eq_iff_eq_mul₀ hqK, mul_one] at h
      exact h
  have hp2 := hp.two_le
  have hp1 : Nat.Coprime (p + 1) p := Nat.coprime_self_add_left.2 (Nat.coprime_one_left p)
  have h1 : ((p + 1 : ℕ) : K) ≠ 1 := by exact_mod_cast (show p + 1 ≠ 1 by omega)
  have h2 : ((p + 1 : ℕ) : K) ^ 2 ≠ 1 := by
    exact_mod_cast (show (p + 1) ^ 2 ≠ 1 by intro h; nlinarith)
  have h3 : ((p + 1 : ℕ) : K) ≠ ((p + 1 : ℕ) : K) ^ 2 := by
    exact_mod_cast (show p + 1 ≠ (p + 1) ^ 2 by intro h; nlinarith)
  rcases pick (hf c v₀ x) (hf c v₀ y) ((p + 1 : ℕ) : K) h1 h2 h3 with h | h | h
  · exact key 1 (Nat.coprime_one_left p) one_ne_zero (by simpa using h.1) (by simpa using h.2)
  · exact key (p + 1) hp1 (Nat.succ_ne_zero p) h.1 h.2
  · exact key ((p + 1) ^ 2) (Nat.Coprime.pow_left 2 hp1) (pow_ne_zero _ (Nat.succ_ne_zero p))
      (by exact_mod_cast h.1) (by exact_mod_cast h.2)

theorem rp_two {K : Type} [Field K] [NumberField K] {p : ℕ} : Rp K p (2 : K) := by
  simpa using Rp_natCast (K := K) (p := p) 2

theorem rp_four {K : Type} [Field K] [NumberField K] {p : ℕ} : Rp K p (4 : K) := by
  simpa using Rp_natCast (K := K) (p := p) 4

theorem normOne_of_pair {K : Type} [Field K] [NumberField K] (c : K →+* K) (p : ℕ) {ι : Type}
    [Fintype ι] [Nonempty ι] (L : Set (ι → K)) (hK : Module.finrank ℚ K = 2)
    (hc : ∀ x, c (c x) = x) (hp : p.Prime) (hs : SplitK c p) (hU : Unimod K c p L)
    (hS : Spans K L) {x y : ι → K} (hx : x ∈ L) (hy : y ∈ L) (hxy : hf c x y = 1) :
    ∃ e ∈ L, hf c e e = 1 := by
  classical
  have hne := ne_of_split c hs
  obtain ⟨i0⟩ := ‹Nonempty ι›
  obtain ⟨v₀, hv₀def⟩ : ∃ v₀ : ι → K, v₀ = Pi.single i0 1 := ⟨_, rfl⟩
  have hv₀ : hf c v₀ v₀ = 1 := by rw [hv₀def, hf_single_left]; simp
  obtain ⟨x₁, hx₁, y₁, hy₁, hxy₁, hX, hY⟩ := generic_pair hc hp hU hx hy hxy v₀
  obtain ⟨N, hN0, hNv⟩ := hS v₀
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN0
  have hp0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have bound : ∀ z ∈ L, Rp K p ((N : K) * (1 - hf c v₀ z)) := by
    intro z hz
    have h1 := hU.hf_mem hz hNv
    rw [hf_smul_right, map_natCast, hf_symm c hc v₀ z] at h1
    have h2 := Rp_map c h1
    rw [map_mul, map_natCast, hc] at h2
    rw [mul_sub, mul_one]; exact Rp_sub (Rp_natCast N) h2
  obtain ⟨X, hXdef⟩ : ∃ X : K, X = hf c v₀ x₁ := ⟨_, rfl⟩
  obtain ⟨Y, hYdef⟩ : ∃ Y : K, Y = hf c v₀ y₁ := ⟨_, rfl⟩
  have hX1 : (1 : K) - X ≠ 0 := sub_ne_zero.2 (by rw [hXdef]; exact Ne.symm hX)
  have hY1 : (1 : K) - Y ≠ 0 := sub_ne_zero.2 (by rw [hYdef]; exact Ne.symm hY)
  have hbX : Rp K p ((N : K) * (1 - X)) := by rw [hXdef]; exact bound x₁ hx₁
  have hbY : Rp K p ((N : K) * (1 - Y)) := by rw [hYdef]; exact bound y₁ hy₁
  obtain ⟨J₁, hJ₁⟩ := dvd_pow_p c hc hK hne hp hbY (mul_ne_zero hNK hY1)
  obtain ⟨J₂, hJ₂⟩ := dvd_pow_p c hc hK hne hp hbX (mul_ne_zero hNK hX1)
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = J₁ + J₂ := ⟨_, rfl⟩
  obtain ⟨α', hα'def⟩ : ∃ α' : K, α' = (p : K) ^ J / (1 - Y) := ⟨_, rfl⟩
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : K, γ' = (p : K) ^ J / (1 - X) := ⟨_, rfl⟩
  have hα : Rp K p α' := by
    have : α' = (N : K) * (p : K) ^ J₂ * ((p : K) ^ J₁ / (N * (1 - Y))) := by
      rw [hα'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₂)) hJ₁
  have hγ : Rp K p γ' := by
    have : γ' = (N : K) * (p : K) ^ J₁ * ((p : K) ^ J₂ / (N * (1 - X))) := by
      rw [hγ'def, hJ, pow_add]; field_simp
    rw [this]; exact Rp_mul (Rp_mul (Rp_natCast N) (rp_pow (Rp_natCast p) J₁)) hJ₂

  obtain ⟨ε, hε, hsum, hδ⟩ := eps c hc hK hp hs (J + 1 + 2 * N)
  have hce : c ε = 1 - ε := by linear_combination hsum
  have hcε : Rp K p (c ε) := Rp_map c hε
  obtain ⟨e', he'def⟩ : ∃ e' : ι → K, e' = ε • x₁ + c ε • y₁ := ⟨_, rfl⟩
  have he' : e' ∈ L := by rw [he'def]; exact hU.add_mem (hU.smul_mem hε hx₁) (hU.smul_mem hcε hy₁)
  obtain ⟨Z, hZdef⟩ : ∃ Z : K, Z = 2 - hf c x₁ x₁ - hf c y₁ y₁ := ⟨_, rfl⟩
  have hZ : Rp K p Z := by
    rw [hZdef]; exact Rp_sub (Rp_sub rp_two (hU.hf_mem hx₁ hx₁)) (hU.hf_mem hy₁ hy₁)
  have hcZ : c Z = Z := by
    rw [hZdef, map_sub, map_sub, map_ofNat, ← hf_symm c hc x₁ x₁, ← hf_symm c hc y₁ y₁]
  have hyx : hf c y₁ x₁ = 1 := by rw [hf_symm c hc x₁ y₁, hxy₁, map_one]
  obtain ⟨d, hddef⟩ : ∃ d : K, d = ε * c ε * Z / 2 := ⟨_, rfl⟩
  have hu : hf c e' e' = 1 - 2 * d := by
    rw [he'def, hddef, hZdef]
    simp only [hf_add_left, hf_add_right, hf_smul_left, hf_smul_right, hc, hxy₁, hyx]
    linear_combination (ε + c ε + 1) * hsum
  have hd : c d = d := by
    rw [hddef, map_div₀, map_mul, map_mul, hc, hcZ, map_ofNat]; ring
  have hB : hf c v₀ e' = c ε * X + ε * Y := by
    rw [he'def, hXdef, hYdef]; simp only [hf_add_right, hf_smul_right, hc]
  obtain ⟨β, hβdef⟩ : ∃ β : K, β = 1 - hf c v₀ e' - d := ⟨_, rfl⟩
  obtain ⟨Γ, hΓdef⟩ : ∃ Γ : K, Γ = ε * α' + c ε * γ' := ⟨_, rfl⟩
  have hΓ : Rp K p Γ := by rw [hΓdef]; exact Rp_add (Rp_mul hε hα) (Rp_mul hcε hγ)
  obtain ⟨C, hCdef⟩ : ∃ C : K, C = ε * c ε / (2 * N * (p : K) ^ (J + 1)) := ⟨_, rfl⟩
  have hC : Rp K p C := by
    have e1 : C = ε * c ε / (p : K) ^ (J + 1 + 2 * N) * ((p : K) ^ (2 * N) / ((2 * N : ℕ) : K)) := by
      rw [hCdef, show (p : K) ^ (J + 1 + 2 * N) = (p : K) ^ (J + 1) * (p : K) ^ (2 * N) by rw [pow_add]]
      push_cast; field_simp
    rw [e1]
    exact Rp_mul hδ (rp_pow_div hp (by omega) le_rfl)
  obtain ⟨ω, hωdef⟩ : ∃ ω : K, ω = C * ((2 * ((N : K) * (1 - Y)) * γ' + 2 * ((N : K) * (1 - X)) * α')
      - ((N : K) * Z * Γ + 4 * N * (p : K) ^ J)) := ⟨_, rfl⟩
  have hω : Rp K p ω := by
    rw [hωdef]
    refine Rp_mul hC (Rp_sub (Rp_add (Rp_mul (Rp_mul rp_two hbY) hγ) (Rp_mul (Rp_mul rp_two hbX) hα))
      (Rp_add (Rp_mul (Rp_mul (Rp_natCast N) hZ) hΓ)
        (Rp_mul (Rp_mul rp_four (Rp_natCast N)) (rp_pow (Rp_natCast p) J))))
  have hβΓ : β * Γ = (p : K) ^ J * (1 + (p : K) * ω) := by
    rw [hβdef, hB, hωdef, hCdef, hΓdef, hα'def, hγ'def, hddef, hce]
    field_simp
    ring
  obtain ⟨hne1, hinv⟩ := one_add_p_unit c hc hK hne hp hω
  have hPne : (p : K) ^ J * (1 + (p : K) * ω) ≠ 0 := mul_ne_zero (pow_ne_zero _ hp0) hne1
  have hβ0 : β ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, zero_mul]
  have hΓ0 : Γ ≠ 0 := by rintro h; apply hPne; rw [← hβΓ, h, mul_zero]
  obtain ⟨η, hηdef⟩ : ∃ η : K, η = d / β := ⟨_, rfl⟩
  have hβ' : β = (p : K) ^ J * (1 + (p : K) * ω) / Γ := by rw [eq_div_iff hΓ0]; exact hβΓ
  have hηN : Rp K p (η / N) := by
    have e1 : η / N = ((p : K) * C) * (Z * Γ) * (1 + (p : K) * ω)⁻¹ := by
      rw [hηdef, hβ', hddef, hCdef, pow_succ]
      field_simp
    rw [e1]
    exact Rp_mul (Rp_mul (Rp_mul (Rp_natCast p) hC) (Rp_mul hZ hΓ)) hinv
  have hη : Rp K p η := by
    have : η = (N : K) * (η / N) := by field_simp
    rw [this]; exact Rp_mul (Rp_natCast N) hηN
  refine ⟨(1 + η) • e' - η • v₀, ?_, refl_norm c hc hv₀ hu hd hβdef hβ0 hηdef⟩
  have hv : η • v₀ = (η / N) • ((N : K) • v₀) := by rw [smul_smul, div_mul_cancel₀ _ hNK]
  rw [hv]
  exact hU.sub_mem (hU.smul_mem (Rp_add Rp_one hη) he') (hU.smul_mem hηN hNv)

end PI.KLW.NO

namespace PI.KLW

theorem normOne_of (h : PairOne) : NormOne := by
  intro K _ _ c p ι _ _ L hK hc hp hs hU hS
  obtain ⟨x, hx, y, hy, hxy⟩ := h K c p ι L hK hc hp hs hU hS
  exact NO.normOne_of_pair c p L hK hc hp hs hU hS hx hy hxy

end PI.KLW
