import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.IsAdmissiblePrimeListNil
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.GalBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.V.Odd UpperTheory.V.Stick UpperTheory.V.ML
open scoped nonZeroDivisors Pointwise

section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω]

private def Cg (A : ValuationSubring Ω) (u v : Ω) : Prop :=
  A.valuation u = 1 ∧ A.valuation v = 1 ∧ A.valuation (u - v) < 1

private theorem cg_of (A : ValuationSubring Ω) {u v : Ω} (hu : A.valuation u = 1) (h : A.valuation (u - v) < 1) :
    Cg A u v := by
  refine ⟨hu, ?_, h⟩
  have h1 : A.valuation (-(u - v)) < A.valuation u := by rw [Valuation.map_neg, hu]; exact h
  have h2 := A.valuation.map_add_eq_of_lt_left h1
  have h3 : u + -(u - v) = v := by ring
  rw [h3, hu] at h2
  exact h2

private theorem cg_mul {A : ValuationSubring Ω} {u v u' v' : Ω} (h : Cg A u v) (h' : Cg A u' v') :
    Cg A (u * u') (v * v') := by
  refine ⟨by rw [map_mul, h.1, h'.1, one_mul], by rw [map_mul, h.2.1, h'.2.1, one_mul], ?_⟩
  have : u * u' - v * v' = u * (u' - v') + (u - v) * v' := by ring
  rw [this]
  refine A.valuation.map_add_lt ?_ ?_
  · rw [map_mul, h.1, one_mul]; exact h'.2.2
  · rw [map_mul, h'.2.1, mul_one]; exact h.2.2

private theorem cg_pow {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) (n : ℕ) : Cg A (u ^ n) (v ^ n) := by
  induction n with
  | zero => exact ⟨by simp, by simp, by simp⟩
  | succ n ih => rw [pow_succ, pow_succ]; exact cg_mul ih h

private theorem cg_inv {A : ValuationSubring Ω} {u v : Ω} (h : Cg A u v) : Cg A u⁻¹ v⁻¹ := by
  have hu : u ≠ 0 := fun h0 => by have := h.1; rw [h0, map_zero] at this; exact zero_ne_one this
  have hv : v ≠ 0 := fun h0 => by have := h.2.1; rw [h0, map_zero] at this; exact zero_ne_one this
  refine ⟨by rw [map_inv₀, h.1, inv_one], by rw [map_inv₀, h.2.1, inv_one], ?_⟩
  have : u⁻¹ - v⁻¹ = -((u - v) * u⁻¹ * v⁻¹) := by field_simp; ring
  rw [this, Valuation.map_neg, map_mul, map_mul, map_inv₀, map_inv₀, h.1, h.2.1, inv_one, mul_one, mul_one]
  exact h.2.2

variable [Algebra ℚ Ω]

private theorem opP_mul (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u * v) = opP δ a u * opP δ a v := by
  simp only [opP, map_mul, mul_pow, mul_div_mul_comm]

private theorem opP_div (δ : G ℚ Ω) (a : ℕ) (u v : Ω) : opP δ a (u / v) = opP δ a u / opP δ a v := by
  simp only [opP, map_div₀, div_pow]
  rw [div_div_div_comm]

private theorem opP_pow (δ : G ℚ Ω) (a : ℕ) (u : Ω) (n : ℕ) : opP δ a (u ^ n) = opP δ a u ^ n := by
  simp only [opP, map_pow, div_pow]
  rw [← pow_mul, ← pow_mul, mul_comm]

private theorem map_opP (δ g : G ℚ Ω) (a : ℕ) (u : Ω) (h : g (δ u) = δ (g u)) :
    g (opP δ a u) = opP δ a (g u) := by
  simp only [opP, map_div₀, map_pow, h]

private theorem opP_root (δ : G ℚ Ω) (a N : ℕ) (hN : N ≠ 0) (hδ : Pows N a δ) (ζ : Ω) (h : ζ ^ N = 1) :
    opP δ a ζ = 1 := by
  have h0 : ζ ≠ 0 := fun h0 => by rw [h0, zero_pow hN] at h; exact zero_ne_one h
  rw [opP, hδ ζ h, div_self (pow_ne_zero _ h0)]

private theorem nrm_opP (δ τ : G ℚ Ω) (a q n : ℕ) (u : Ω) (h : ∀ g : G ℚ Ω, g (δ u) = δ (g u)) :
    nrm q τ (opP δ a u ^ n) = opP δ a (nrm q τ u) ^ n := by
  simp only [nrm, map_pow, opP, map_div₀, h, map_prod]
  rw [Finset.prod_pow, Finset.prod_div_distrib, Finset.prod_pow]

end SlopeTestRemainingChoices

private theorem admissible_of_integral_conj_le {l F r q d : ℕ} (h : ML.admitted l F r (q * d)) : ML.admitted l F r d :=
  ⟨h.1.squarefree_of_dvd (Dvd.intro_left q rfl), fun p hp hd => h.2 p hp (hd.mul_left q)⟩

private theorem admissible_prime_coprime {l F r q : ℕ} (h : AdmP l F r q) : q.Coprime r := by
  have hq := h.1
  rw [Nat.Prime.coprime_iff_not_dvd hq]
  intro hd
  haveI : Fact q.Prime := ⟨hq⟩
  apply h.2.2.2
  have : (r : ZMod q) = 0 := (ZMod.natCast_eq_zero_iff r q).2 hd
  rw [this, orderOf_zero]
  exact dvd_zero l

theorem UpperTheory.V.ML.sysOfLax :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l N₀ m F r a : ℕ), l.Prime → l ≠ 2 → N₀.Coprime l → 1 ≤ m → F = N₀ * l ^ m → ∀ (X : ℕ → Ω) (s : ℕ → ℕ → ℕ), Lax l F r X s →
    ∀ δ : G ℚ Ω, Pows (l ^ m) a δ → Sys l F r (fun d => opP δ a (X d) ^ (2 * N₀ * d)) fun d q => q * s d q := by
  intro Ω _ _ _ l N₀ m F r a hl _ hN hm hF X s hX δ hδ
  have hN0 : N₀ ≠ 0 := by
    rintro rfl
    rw [Nat.coprime_zero_left] at hN
    exact hl.one_lt.ne' hN
  have hlm : l ^ m ≠ 0 := pow_ne_zero _ hl.ne_zero
  have hF0 : F ≠ 0 := hF ▸ mul_ne_zero hN0 hlm
  have hFd : ∀ d, ML.admitted l F r d → F * d ≠ 0 := fun d hd => mul_ne_zero hF0 hd.1.ne_zero
  have hcomm : ∀ d, ML.admitted l F r d → ∀ g h : G ℚ Ω, g (h (X d)) = h (g (X d)) := fun d hd =>
    (galBasic Ω (F * d) (hFd d hd)).2.2.2.2.2.1 (X d) (hX.fix d hd)
  obtain ⟨-, -, -, hcop, -, -, -, -, -, hact⟩ := placeBasic Ω
  have hlt : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) < 1 ↔ (δ⁻¹ • A).valuation y < 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.1 y
    rwa [smul_inv_smul] at this
  have heq : ∀ (A : ValuationSubring Ω) (y : Ω), A.valuation (δ y) = 1 ↔ (δ⁻¹ • A).valuation y = 1 := fun A y => by
    have := (hact (δ⁻¹ • A) δ).2.2.2.2 y
    rwa [smul_inv_smul] at this
  have hov : ∀ (A : ValuationSubring Ω) (n : ℕ), Over (δ⁻¹ • A) n ↔ Over A n := fun A n => by
    have := hlt A (n : Ω)
    rw [map_natCast] at this
    exact this.symm
  have hδu : ∀ d, ML.admitted l F r d → ∀ A : ValuationSubring Ω, ¬ Over A r → A.valuation (δ (X d)) = 1 :=
    fun d hd A hA => (heq A _).2 (hX.unit d hd _ fun h => hA ((hov A r).1 h))
  have hζ : ∀ (n : ℕ) (ζ : Ω), ζ ^ (2 * F * n) = 1 → opP δ a ζ ^ (2 * N₀ * n) = 1 := fun n ζ h => by
    rw [← opP_pow]
    refine opP_root δ a (l ^ m) hlm hδ _ ?_
    rw [← pow_mul, ← h, hF]
    congr 1
    ring
  refine ⟨fun d hd => ?_, fun d hd g hg => ?_, fun d hd A hA => ?_, fun d q hq hd => ?_,
    fun d q hq hd τ hτ hgen φ hφ => ?_, fun d q hq hd φ hφ A hA => ?_⟩
  · refine pow_ne_zero _ (div_ne_zero ?_ (pow_ne_zero _ (hX.ne d hd)))
    exact (map_ne_zero δ).2 (hX.ne d hd)
  · rw [map_pow, map_opP δ g a _ (hcomm d hd g δ), hX.fix d hd g hg]
  · rw [map_pow, opP, map_div₀, map_pow, hδu d hd A hA, hX.unit d hd A hA]
    simp
  · intro h
    rcases (Nat.Prime.dvd_mul hl).1 h with h | h
    · have h1 := (hd.2 q hq (Dvd.intro d rfl)).2.1
      have hlF : l ∣ F := hF ▸ Dvd.dvd.mul_left (dvd_pow_self l (by omega)) N₀
      have h2 : l ∣ 1 := ((h1.of_dvd hlF).dvd_iff dvd_rfl).1 h
      exact hl.one_lt.ne' (Nat.dvd_one.1 h2)
    · exact hX.cop d q hq hd h
  · obtain ⟨ζ, h1, h2⟩ := hX.norm d q hq hd τ hτ hgen φ hφ
    rw [nrm_opP δ τ a q _ _ (fun g => hcomm _ hd g δ), h2, opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, opP_div,
      map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← div_pow, ← pow_mul, ← pow_mul]
    congr 1
    ring
  · obtain ⟨ζ, h1, h2⟩ := hX.cong d q hq hd φ hφ
    have hr : ¬ Over A r := hcop A q r (admissible_prime_coprime (hd.2 q hq (Dvd.intro d rfl))) hA
    have c1 := cg_of A (hX.unit _ hd A hr) (h2 A hA)
    have h3 := (hlt A _).2 (h2 _ ((hov A q).2 hA))
    rw [map_sub] at h3
    have c2 := cg_of A (hδu _ hd A hr) h3
    have c3 := cg_pow (cg_mul c2 (cg_inv (cg_pow c1 a))) (2 * N₀ * (q * d))
    rw [← div_eq_mul_inv, ← div_eq_mul_inv] at c3
    have c4 : A.valuation (opP δ a (X (q * d)) ^ (2 * N₀ * (q * d)) -
      opP δ a (ζ * φ⁻¹ (X d) ^ s d q) ^ (2 * N₀ * (q * d))) < 1 := c3.2.2
    rw [opP_mul, mul_pow, hζ _ ζ h1, one_mul, opP_pow, ← pow_mul] at c4
    rw [map_pow, map_opP δ φ⁻¹ a _ (hcomm d (admissible_of_integral_conj_le hd) _ δ), ← pow_mul]
    have e : 2 * N₀ * d * (q * s d q) = s d q * (2 * N₀ * (q * d)) := by ring
    rw [e]
    exact c4
