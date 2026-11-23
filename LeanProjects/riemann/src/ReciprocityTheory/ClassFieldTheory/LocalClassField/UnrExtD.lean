import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrExtC

namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1

namespace UnramifiedExtensions

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem qK_pow_sub_one_ne_zero (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    qK p K ^ n - 1 ≠ 0 := by
  have := Nat.one_lt_pow hn.ne' (one_lt_qK K hK)
  omega

theorem pow_apply_root {n : ℕ} {φ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K) (i : ℕ) :
    ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → (φ ^ i) ζ = ζ ^ (qK p K ^ i) := by
  induction i with
  | zero => intro ζ _; simp
  | succ i ih =>
    intro ζ hζ
    rw [pow_succ, AlgEquiv.mul_apply, h ζ hζ, map_pow, ih ζ hζ, ← pow_mul, pow_succ]

theorem eqOn_Kn_of_primitive {n : ℕ} (h0 : qK p K ^ n - 1 ≠ 0) {ζ₀ : PadicAlgCl p}
    (hζ₀ : IsPrimitiveRoot ζ₀ (qK p K ^ n - 1)) {σ τ : GK p K} (h : σ ζ₀ = τ ζ₀) {x : PadicAlgCl p}
    (hx : x ∈ Kn p K n) : σ x = τ x := by
  have : NeZero (qK p K ^ n - 1) := ⟨h0⟩
  refine eqOn_Kn K (fun ζ hζ => ?_) hx
  obtain ⟨k, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [map_pow, map_pow, h]

theorem pow_sub_one_dvd_iff {q : ℕ} (hq : 1 < q) {n : ℕ} (i : ℕ) :
    q ^ n - 1 ∣ q ^ i - 1 ↔ n ∣ i := by
  constructor
  · intro h
    have h1 := Nat.gcd_eq_left h
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at h1
    have h2 : 1 ≤ q ^ Nat.gcd n i := Nat.one_le_pow _ _ (by omega)
    have h3 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
    have h4 : q ^ Nat.gcd n i = q ^ n := by omega
    have h5 := Nat.pow_right_injective (show 2 ≤ q by omega) h4
    exact Nat.gcd_eq_left_iff_dvd.1 h5
  · intro h
    exact Nat.pow_sub_one_dvd_pow_sub_one _ h

end UnramifiedExtensions

variable (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))

theorem isFrobOn_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (φ : GK p K) :
    IsFrobOn p K n φ ↔ ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → φ ζ = ζ ^ qK p K := by
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  constructor
  · intro h ζ hζ
    by_contra hne
    have h1 := UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ
    have h2 := h ζ (mem_Kn_of_pow p K hζ) h1.le
    have h3 := norm_sub_eq_one_of_pow_eq_one p (UnramifiedExtensions.not_dvd_qK_pow_sub_one K hK hn)
      (ζ := φ ζ) (ξ := ζ ^ qK p K) (by rw [← map_pow, hζ, map_one])
      (by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]) hne
    rw [h3] at h2
    exact lt_irrefl _ h2
  · intro h x hx hx1
    have hex : ∃ ζ : PadicAlgCl p, φ ζ = ζ ^ qK p K ∧ ‖ζ‖ ≤ 1 ∧ ‖x - ζ‖ < 1 := by
      rcases lt_or_eq_of_le hx1 with h1 | h1
      · exact ⟨0, by rw [map_zero, zero_pow (by omega)], by simp, by simpa using h1⟩
      · obtain ⟨ζ, -, hζ, hxζ⟩ := exists_teichmuller p (Kn p K n) (finiteDimensional_Kn p K hK hn) hx h1
        rw [qK_Kn p K hK hn] at hζ
        exact ⟨ζ, h ζ hζ, (UnramifiedExtensions.norm_eq_one_of_pow hm0 hζ).le, hxζ⟩
    obtain ⟨ζ, h1, h2, h3⟩ := hex
    have h4 : UnramifiedExtensions.red x = UnramifiedExtensions.red ζ := (UnramifiedExtensions.red_eq_iff hx1 h2).2 h3
    have h5 : ‖φ x‖ ≤ 1 := by rw [norm_GK]; exact hx1
    have h6 : ‖x ^ qK p K‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx1
    rw [← UnramifiedExtensions.red_eq_iff h5 h6, ← UnramifiedExtensions.sigBar_red φ hx1, h4, UnramifiedExtensions.sigBar_red φ h2, h1,
      UnramifiedExtensions.red_pow h2, UnramifiedExtensions.red_pow hx1, h4]

theorem exists_isFrobOn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) :
    ∃ φ : GK p K, IsFrobOn p K n φ := by
  classical
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  have : NeZero (qK p K ^ n - 1) := ⟨hm0⟩
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hζ1 := hζ₀.pow_eq_one
  let E : IntermediateField K (PadicAlgCl p) := IntermediateField.extendScalars (le_Kn p K n)
  have hgal : IsGalois K E := isGalois_Kn p K hK hn
  have hfr : Module.finrank K E = n := finrank_extendScalars_Kn p K hK hn
  have hfd : FiniteDimensional K E := Module.finite_of_finrank_pos (by rw [hfr]; exact hn)
  have hcard : Nat.card (E ≃ₐ[K] E) = n := by rw [IsGalois.card_aut_eq_finrank, hfr]
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) (PadicAlgCl p)
  have hex : ∀ τ : E ≃ₐ[K] E, ∃ i : Fin n, ∃ σ : GK p K,
      AlgEquiv.restrictNormalHom E σ = τ ∧ σ ζ₀ = ζ₀ ^ (qK p K ^ (i : ℕ)) := by
    intro τ
    obtain ⟨σ, hσ⟩ := hsurj τ
    obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ1
    exact ⟨⟨i, hi⟩, σ, hσ, h⟩
  choose f g hg1 hg2 using hex
  have hinj : Function.Injective f := by
    intro τ1 τ2 h
    rw [← hg1 τ1, ← hg1 τ2]
    ext x
    rw [AlgEquiv.restrictNormalHom_apply, AlgEquiv.restrictNormalHom_apply]
    exact UnramifiedExtensions.eqOn_Kn_of_primitive hm0 hζ₀ (by rw [hg2, hg2, h]) x.2
  have hbij : Function.Bijective f := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_fin])
  obtain ⟨τ, hτ⟩ := hbij.2 ⟨1 % n, Nat.mod_lt _ hn⟩
  refine ⟨g τ, (isFrobOn_iff p K hK hn _).2 ?_⟩
  have h0 : g τ ζ₀ = ζ₀ ^ qK p K := by
    rw [hg2, hτ]
    rcases Nat.lt_or_ge 1 n with h | h
    · simp only [Nat.mod_eq_of_lt h, pow_one]
    · obtain rfl : n = 1 := by omega
      have h1 := UnramifiedExtensions.pow_pow_succ_sub (q := qK p K) (n := 1) (by omega) hζ1
      simp only [Nat.mod_self, pow_zero, pow_one] at h1 ⊢
      exact h1.symm
  intro ζ hζ
  obtain ⟨k, -, rfl⟩ := hζ₀.eq_pow_of_pow_eq_one hζ
  rw [map_pow, h0, ← pow_mul, ← pow_mul, mul_comm]

theorem IsFrobOn.eqOn (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ ψ : GK p K}
    (hφ : IsFrobOn p K n φ) (hψ : IsFrobOn p K n ψ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    φ x = ψ x := by
  rw [isFrobOn_iff p K hK hn] at hφ hψ
  exact UnramifiedExtensions.eqOn_Kn K (fun ζ hζ => by rw [hφ ζ hζ, hψ ζ hζ]) hx

theorem IsFrobOn.exists_pow (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (σ : GK p K) : ∃ i < n, ∀ x ∈ Kn p K n, σ x = (φ ^ i) x := by
  rw [isFrobOn_iff p K hK hn] at hφ
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  obtain ⟨i, hi, h⟩ := UnramifiedExtensions.exists_pow_of_GK hK hn σ hζ₀.pow_eq_one
  refine ⟨i, hi, fun x hx => UnramifiedExtensions.eqOn_Kn_of_primitive hm0 hζ₀ ?_ hx⟩
  rw [h, UnramifiedExtensions.pow_apply_root hφ i ζ₀ hζ₀.pow_eq_one]

theorem IsFrobOn.pow_fixes_iff (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) (i : ℕ) : (∀ x ∈ Kn p K n, (φ ^ i) x = x) ↔ n ∣ i := by
  rw [isFrobOn_iff p K hK hn] at hφ
  have hm0 := UnramifiedExtensions.qK_pow_sub_one_ne_zero hK hn
  have hq := one_lt_qK p K hK
  obtain ⟨ζ₀, hζ₀⟩ := UnramifiedExtensions.exists_primitiveRoot (p := p) hm0
  have hζ1 := hζ₀.pow_eq_one
  have hζ0 : ζ₀ ≠ 0 := hζ₀.ne_zero hm0
  have h1 : 1 ≤ qK p K ^ i := Nat.one_le_pow _ _ (by omega)
  have key : (φ ^ i) ζ₀ = ζ₀ ↔ n ∣ i := by
    rw [UnramifiedExtensions.pow_apply_root hφ i ζ₀ hζ1, ← UnramifiedExtensions.pow_sub_one_dvd_iff hq, ← hζ₀.pow_eq_one_iff_dvd]
    have h2 : ζ₀ ^ (qK p K ^ i) = ζ₀ ^ (qK p K ^ i - 1) * ζ₀ := by
      rw [← pow_succ, Nat.sub_add_cancel h1]
    rw [h2]
    constructor
    · intro h
      exact mul_right_cancel₀ hζ0 (by rw [h, one_mul])
    · intro h
      rw [h, one_mul]
  rw [← key]
  constructor
  · intro h
    exact h ζ₀ (mem_Kn_of_pow p K hζ1)
  · intro h x hx
    exact UnramifiedExtensions.eqOn_Kn_of_primitive (τ := 1) hm0 hζ₀ h hx

theorem IsFrobOn.of_dvd (hK : FiniteDimensional ℚ_[p] K) {m n : ℕ} (h : m ∣ n) {φ : GK p K}
    (hφ : IsFrobOn p K n φ) : IsFrobOn p K m φ :=
  fun x hx hx1 => hφ x (Kn_mono p K hK h hx) hx1

end ReciprocityTheory.DiscreteGroups.LocalClassField
