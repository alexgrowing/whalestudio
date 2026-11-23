import ReciprocityTheory.ClassFieldTheory.LocalClassField.MemOfPowQKSubOne

namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions

open _root_.Neutral.B1 ReciprocityTheory.DiscreteGroups.LocalClassField Polynomial

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

noncomputable def sigO (σ : GK p K) : Obar p →+* Obar p :=
  ((σ : PadicAlgCl p →+* PadicAlgCl p).comp (Obar p).subtype).codRestrict (Obar p)
    (fun x => mem_Obar_iff.2 (by
      change ‖σ (x : PadicAlgCl p)‖ ≤ 1
      rw [norm_GK]; exact norm_le_one x))

theorem coe_sigO (σ : GK p K) (x : Obar p) : ((sigO σ x : Obar p) : PadicAlgCl p) = σ x := rfl

noncomputable def sigBar (σ : GK p K) : kbar p →+* kbar p :=
  Ideal.Quotient.lift (IsLocalRing.maximalIdeal (Obar p)) (res.comp (sigO σ)) (by
    intro a ha
    have h1 : res a = 0 := (IsLocalRing.residue_eq_zero_iff a).2 ha
    rw [res_eq_zero_iff] at h1
    change res (sigO σ a) = 0
    rw [res_eq_zero_iff, coe_sigO, norm_GK]
    exact h1)

theorem sigBar_res (σ : GK p K) (x : Obar p) : sigBar σ (res x) = res (sigO σ x) := rfl

theorem sigBar_red (σ : GK p K) {x : PadicAlgCl p} (hx : ‖x‖ ≤ 1) : sigBar σ (red x) = red (σ x) := by
  rw [red_of_le hx, sigBar_res, ← red_coe, coe_sigO]

theorem sigBar_of_mem (σ : GK p K) {c : kbar p} (hc : c ∈ resK p K) : sigBar σ c = c := by
  obtain ⟨x, hx, rfl⟩ := (mem_resK_iff K c).1 hc
  rw [sigBar_res]
  congr 1
  apply Subtype.ext
  rw [coe_sigO]
  exact σ.commutes ⟨x, hx⟩

theorem pow_pow_succ_sub {R : Type*} [Monoid R] {q n : ℕ} (hq : 0 < q) {c : R} (h : c ^ (q ^ n - 1) = 1) :
    c ^ (q ^ n) = c := by
  have h1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ hq
  have : q ^ n = (q ^ n - 1) + 1 := by omega
  rw [this, pow_succ, h, one_mul]

theorem exists_pow_of_GK (hK : FiniteDimensional ℚ_[p] K) {n : ℕ} (hn : 0 < n) (σ : GK p K)
    {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ∃ i < n, σ ζ = ζ ^ (qK p K ^ i) := by
  obtain ⟨f, hf, hqf⟩ := qK_eq_pow K hK
  have hq := one_lt_qK K hK
  set q := qK p K with hqdef
  have hnd : ¬ p ∣ q ^ n - 1 := not_dvd_qK_pow_sub_one K hK hn
  have hm0 : q ^ n - 1 ≠ 0 := by rintro h; exact hnd (h ▸ dvd_zero p)
  have h1 := norm_eq_one_of_pow hm0 hζ
  set c := red ζ with hc
  have hcn : c ^ (q ^ n) = c := by
    rw [hc, ← red_pow h1.le, pow_pow_succ_sub (by omega) hζ]
  have : ExpChar (kbar p) p := ExpChar.prime Fact.out
  let φ : kbar p →+* kbar p := iterateFrobenius (kbar p) p f
  have hφ : ∀ x, φ x = x ^ q := fun x => by rw [hqf]; rfl
  let g : ℕ → (kbar p)[X] := fun i => X - C (c ^ (q ^ i))
  set h : (kbar p)[X] := ∏ i ∈ Finset.range n, g i with hh
  have hg : ∀ i, (g i).map φ = g (i + 1) := by
    intro i
    simp only [g, Polynomial.map_sub, map_X, map_C, hφ]
    rw [← pow_mul, ← pow_succ]
  have hmap : h.map φ = h := by
    rw [hh, Polynomial.map_prod]
    simp only [hg]
    have e1 := Finset.prod_range_succ g n
    have e2 := Finset.prod_range_succ' g n
    have e3 : g n = g 0 := by simp only [g, hcn, pow_zero, pow_one]
    have e4 : g 0 ≠ 0 := X_sub_C_ne_zero _
    rw [e1, e3] at e2
    exact (mul_right_cancel₀ e4 e2).symm
  have hcoef : ∀ k, h.coeff k ∈ resK p K := by
    intro k
    apply mem_resK_of_pow K hK
    rw [← hφ, ← coeff_map, hmap]
  have hmapσ : h.map (sigBar σ) = h := by
    ext k
    rw [coeff_map, sigBar_of_mem σ (hcoef k)]
  have h0 : h.eval c = 0 := by
    rw [hh, eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_range.2 hn)
    simp [g]
  have h2 : h.eval (sigBar σ c) = 0 := by
    conv_lhs => rw [← hmapσ]
    rw [eval_map, eval₂_at_apply, h0, map_zero]
  rw [hh, eval_prod, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, hi, h3⟩ := h2
  refine ⟨i, Finset.mem_range.1 hi, ?_⟩
  simp only [g, eval_sub, eval_X, eval_C, sub_eq_zero] at h3
  rw [hc, sigBar_red σ h1.le, ← red_pow h1.le] at h3
  by_contra hne
  have hσζ : (σ ζ) ^ (q ^ n - 1) = 1 := by rw [← map_pow, hζ, map_one]
  have hζi : (ζ ^ (q ^ i)) ^ (q ^ n - 1) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have h4 := norm_sub_eq_one_of_pow_eq_one hnd hσζ hζi hne
  have h5 := (red_eq_iff (norm_eq_one_of_pow hm0 hσζ).le (norm_eq_one_of_pow hm0 hζi).le).1 h3
  exact absurd h4 (ne_of_lt h5)

variable (K)

theorem le_Kn (n : ℕ) : K ≤ Kn p K n := le_sup_left

theorem mem_Kn_of_pow {n : ℕ} {ζ : PadicAlgCl p} (hζ : ζ ^ (qK p K ^ n - 1) = 1) : ζ ∈ Kn p K n :=
  (le_sup_right : _ ≤ Kn p K n) (IntermediateField.subset_adjoin _ _ hζ)

theorem Kn_le {n : ℕ} {S : IntermediateField ℚ_[p] (PadicAlgCl p)} (h1 : K ≤ S)
    (h2 : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → ζ ∈ S) : Kn p K n ≤ S :=
  sup_le h1 (IntermediateField.adjoin_le_iff.2 h2)

theorem map_mem_Kn (n : ℕ) (σ : GK p K) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by
  have h : Kn p K n ≤ (Kn p K n).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) := by
    apply Kn_le
    · intro y hy
      change σ y ∈ Kn p K n
      have : σ y = y := σ.commutes ⟨y, hy⟩
      rw [this]; exact le_Kn K n hy
    · intro ζ hζ
      change σ ζ ∈ Kn p K n
      apply mem_Kn_of_pow
      rw [← map_pow, hζ, map_one]
  exact h hx

noncomputable def eqField (σ τ : GK p K) : IntermediateField ℚ_[p] (PadicAlgCl p) where
  toSubalgebra := AlgHom.equalizer
    ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
    ((τ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p)
  inv_mem' := by
    intro x hx
    have hx' : σ x = τ x := hx
    change σ x⁻¹ = τ x⁻¹
    rw [map_inv₀, map_inv₀, hx']

theorem eqOn_Kn {n : ℕ} {σ τ : GK p K}
    (h : ∀ ζ : PadicAlgCl p, ζ ^ (qK p K ^ n - 1) = 1 → σ ζ = τ ζ) {x : PadicAlgCl p} (hx : x ∈ Kn p K n) :
    σ x = τ x := by
  have h1 : Kn p K n ≤ eqField K σ τ := by
    apply Kn_le
    · intro y hy
      change σ y = τ y
      exact (σ.commutes ⟨y, hy⟩).trans (τ.commutes ⟨y, hy⟩).symm
    · exact h
  exact h1 hx

theorem Kn_mono {m n : ℕ} (h : m ∣ n) : Kn p K m ≤ Kn p K n := by
  apply Kn_le K (le_Kn K n)
  intro ζ hζ
  apply mem_Kn_of_pow
  obtain ⟨k, rfl⟩ := h
  obtain ⟨d, hd⟩ : qK p K ^ m - 1 ∣ qK p K ^ (m * k) - 1 := by
    rw [pow_mul]
    simpa using Nat.sub_dvd_pow_sub_pow (qK p K ^ m) 1 k
  rw [hd, pow_mul, hζ, one_pow]

end ReciprocityTheory.DiscreteGroups.LocalClassField.UnramifiedExtensions
