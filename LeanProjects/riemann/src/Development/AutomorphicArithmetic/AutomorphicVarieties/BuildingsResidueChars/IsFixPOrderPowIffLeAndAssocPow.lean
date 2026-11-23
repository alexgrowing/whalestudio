import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

section
variable {O K : Type} [CommRing O] [Field K] [Algebra O K] {τ : K}

private theorem ord_mem {y z : Etau K τ} :
    z ∈ Ord O y ↔ ∃ p q : O, (algebraMap O K p) • (1 : Etau K τ) + (algebraMap O K q) • y = z := by
  simp only [PK.Ord, SetLike.mem_coe, Submodule.mem_span_pair, algebraMap_smul]

private theorem pair_im (a b a' b' : K) (y : Etau K τ) :
    ((a • (1 : Etau K τ) + b • y) * star (a' • (1 : Etau K τ) + b' • y)).im = (b * a' - a * b') * y.im := by
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]
  ring

private theorem comb_im (a b : K) (y : Etau K τ) : (a • (1 : Etau K τ) + b • y).im = b * y.im := by
  simp [QuadraticAlgebra.im_one]

private theorem comb_re (a b : K) (y : Etau K τ) : (a • (1 : Etau K τ) + b • y).re = a + b * y.re := by
  simp [QuadraticAlgebra.re_one]

private theorem coord {y : Etau K τ} (hy : y.im ≠ 0) (z : Etau K τ) :
    ∃ a b : K, a • (1 : Etau K τ) + b • y = z := by
  refine ⟨z.re - z.im / y.im * y.re, z.im / y.im, ?_⟩
  ext
  · rw [comb_re]
    ring
  · rw [comb_im]
    field_simp

private theorem mul_two_dim_algebra_stable (w y : Etau K τ) (a b c d p q : K) (h1 : w = a • (1 : Etau K τ) + b • y)
    (h2 : w * y = c • (1 : Etau K τ) + d • y) :
    w * (p • (1 : Etau K τ) + q • y) = (p * a + q * c) • (1 : Etau K τ) + (p * b + q * d) • y := by
  rw [mul_add, mul_smul_comm, mul_smul_comm, mul_one, h2, h1]
  module
end

theorem UpperTheory.isFixP_order_pow_iff_le_and_assoc_pow :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → ∀ (t : K) (m : ℕ), IsFixP O τ t (Ord O (yy π m x)) ↔ m ≤ n ∧ ∃ u : Oˣ, t * algebraMap O K (π ^ m) = algebraMap O K u * algebraMap O K (π ^ n) := by
  intro O K _ _ _ _ _ Δ τ hL hτ π n e h x hc t m
  classical
  have hfr := hL.frac
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hπ0 : π ≠ 0 := hc.irr.ne_zero
  have hπu : ¬ IsUnit π := hc.irr.not_isUnit
  have hA1 : ∀ r : O, algebraMap O (Etau K τ) r = algebraMap O K r • (1 : Etau K τ) := by
    intro r
    rw [algebraMap_etau, Algebra.algebraMap_eq_smul_one]
  have hxim : algebraMap O K (π ^ n) * x.im = 1 := by
    have := congrArg QuadraticAlgebra.im hc.om
    simp [yy, algebraMap_etau, QuadraticAlgebra.omega_im] at this
    rw [map_pow]
    exact this.symm
  have hx0 : x.im ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hxim
    exact zero_ne_one hxim
  have hAπ : algebraMap O K π ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ hinj]
    exact hπ0
  have hy0 : (yy π m x).im = algebraMap O K (π ^ m) * x.im := by
    simp [yy]
  have hy0ne : (yy π m x).im ≠ 0 := by
    rw [hy0]
    exact mul_ne_zero (by rw [map_pow]; exact pow_ne_zero _ hAπ) hx0
  set y0 := yy π m x with hy0def
  have uniq : ∀ a b a' b' : K, a • (1 : Etau K τ) + b • y0 = a' • 1 + b' • y0 → a = a' ∧ b = b' := by
    intro a b a' b' hab
    have him := congrArg QuadraticAlgebra.im hab
    have hre := congrArg QuadraticAlgebra.re hab
    rw [comb_im, comb_im] at him
    rw [comb_re, comb_re] at hre
    have hb : b = b' := mul_right_cancel₀ hy0ne him
    subst hb
    exact ⟨add_right_cancel hre, rfl⟩
  have memc : ∀ a b : K, a • (1 : Etau K τ) + b • y0 ∈ PK.Ord O y0 ↔
      a ∈ (algebraMap O K).range ∧ b ∈ (algebraMap O K).range := by
    intro a b
    rw [ord_mem]
    constructor
    · rintro ⟨p, q, hpq⟩
      obtain ⟨h1, h2⟩ := uniq _ _ _ _ hpq
      exact ⟨⟨p, h1⟩, ⟨q, h2⟩⟩
    · rintro ⟨⟨p, rfl⟩, ⟨q, rfl⟩⟩
      exact ⟨p, q, rfl⟩
  set c := t * y0.im with hcdef
  have dualc : ∀ a' b' : K, (∀ s ∈ PK.Ord O y0,
      t * (s * star (a' • (1 : Etau K τ) + b' • y0)).im ∈ (algebraMap O K).range) ↔
      (a' * c ∈ (algebraMap O K).range ∧ b' * c ∈ (algebraMap O K).range) := by
    intro a' b'
    constructor
    · intro H
      have h1 := H _ ((memc 1 0).2 ⟨⟨1, map_one _⟩, ⟨0, map_zero _⟩⟩)
      have h2 := H _ ((memc 0 1).2 ⟨⟨0, map_zero _⟩, ⟨1, map_one _⟩⟩)
      rw [pair_im] at h1 h2
      constructor
      · have e1 : a' * c = t * ((1 * a' - 0 * b') * y0.im) := by
          rw [hcdef]
          ring
        rw [e1]
        exact h2
      · have e2 : b' * c = -(t * ((0 * a' - 1 * b') * y0.im)) := by
          rw [hcdef]
          ring
        rw [e2]
        exact neg_mem h1
    · rintro ⟨ha, hb⟩ s hs
      obtain ⟨p, q, rfl⟩ := ord_mem.1 hs
      rw [pair_im]
      have e : t * ((algebraMap O K q * a' - algebraMap O K p * b') * y0.im) =
          algebraMap O K q * (a' * c) - algebraMap O K p * (b' * c) := by
        rw [hcdef]
        ring
      rw [e]
      exact sub_mem (mul_mem ⟨q, rfl⟩ ha) (mul_mem ⟨p, rfl⟩ hb)
  have dual_iff : (∀ y : Etau K τ, y ∈ PK.Ord O y0 ↔
      ∀ s ∈ PK.Ord O y0, t * (s * star y).im ∈ (algebraMap O K).range) ↔
      ∀ v : K, v ∈ (algebraMap O K).range ↔ v * c ∈ (algebraMap O K).range := by
    constructor
    · intro H v
      have hv := H (v • (1 : Etau K τ) + (0 : K) • y0)
      rw [memc, dualc] at hv
      constructor
      · intro hv'
        exact (hv.1 ⟨hv', zero_mem _⟩).1
      · intro hv'
        exact (hv.2 ⟨hv', by rw [zero_mul]; exact zero_mem _⟩).1
    · intro H y
      obtain ⟨a, b, rfl⟩ := coord hy0ne y
      rw [memc, dualc, H a, H b]
  have unit_iff : (∀ v : K, v ∈ (algebraMap O K).range ↔ v * c ∈ (algebraMap O K).range) ↔
      ∃ u : Oˣ, c = algebraMap O K u := by
    constructor
    · intro H
      obtain ⟨r, hr⟩ := (H 1).1 ⟨1, map_one _⟩
      have hcr : c = algebraMap O K r := by
        rw [hr, one_mul]
      by_cases hr0 : r = 0
      · exfalso
        obtain ⟨s, hs⟩ := (H (algebraMap O K π)⁻¹).2
          (by rw [hcr, hr0, map_zero, mul_zero]; exact zero_mem _)
        apply hπu
        refine isUnit_iff_exists_inv.2 ⟨s, hinj ?_⟩
        rw [map_mul, hs, map_one, mul_inv_cancel₀ hAπ]
      · have hAr : algebraMap O K r ≠ 0 := by
          rw [Ne, map_eq_zero_iff _ hinj]
          exact hr0
        obtain ⟨s, hs⟩ := (H (algebraMap O K r)⁻¹).2
          (by rw [hcr, inv_mul_cancel₀ hAr]; exact one_mem _)
        have hu : IsUnit r :=
          isUnit_iff_exists_inv.2 ⟨s, hinj (by rw [map_mul, hs, map_one, mul_inv_cancel₀ hAr])⟩
        exact ⟨hu.unit, by rw [IsUnit.unit_spec, hcr]⟩
    · rintro ⟨u, hu⟩ v
      constructor
      · intro hv
        rw [hu]
        exact mul_mem hv ⟨u, rfl⟩
      · intro hv
        have e : v = (v * c) * algebraMap O K ↑u⁻¹ := by
          rw [hu, mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]
        rw [e]
        exact mul_mem hv ⟨_, rfl⟩
  have c_iff : ∀ u : Oˣ, c = algebraMap O K u ↔
      t * algebraMap O K (π ^ m) = algebraMap O K u * algebraMap O K (π ^ n) := by
    intro u
    constructor
    · intro hu
      calc t * algebraMap O K (π ^ m)
          = t * algebraMap O K (π ^ m) * (algebraMap O K (π ^ n) * x.im) := by rw [hxim, mul_one]
        _ = c * algebraMap O K (π ^ n) := by rw [hcdef, hy0]; ring
        _ = algebraMap O K u * algebraMap O K (π ^ n) := by rw [hu]
    · intro hu
      calc c = t * algebraMap O K (π ^ m) * x.im := by rw [hcdef, hy0]; ring
        _ = algebraMap O K u * (algebraMap O K (π ^ n) * x.im) := by rw [hu]; ring
        _ = algebraMap O K u := by rw [hxim, mul_one]
  have stab_iff : (∀ s ∈ PK.Ord O y0, ω * s ∈ PK.Ord O y0) ↔ m ≤ n := by
    constructor
    · intro H
      have h1mem : (1 : Etau K τ) ∈ PK.Ord O y0 :=
        Submodule.subset_span (Set.mem_insert _ _)
      have hω := H 1 h1mem
      rw [mul_one, ord_mem] at hω
      obtain ⟨p, q, hpq⟩ := hω
      have him := congrArg QuadraticAlgebra.im hpq
      rw [comb_im, QuadraticAlgebra.omega_im, hy0] at him
      have hq : algebraMap O K (q * π ^ m) = algebraMap O K (π ^ n) := by
        apply mul_right_cancel₀ hx0
        rw [map_mul, mul_assoc, him, hxim]
      have hd : π ^ m ∣ π ^ n := ⟨q, by rw [mul_comm]; exact (hinj hq).symm⟩
      exact (pow_dvd_pow_iff hπ0 hπu).1 hd
    · intro hmn s hs
      obtain ⟨p, q, rfl⟩ := ord_mem.1 hs
      have hω : (ω : Etau K τ) = algebraMap O K h • (1 : Etau K τ) + algebraMap O K (π ^ (n - m)) • y0 := by
        rw [hc.om, hy0def, hA1]
        simp only [yy, smul_smul, ← map_mul, ← pow_add, Nat.sub_add_cancel hmn]
      have hωy : (ω : Etau K τ) * y0 =
          algebraMap O K (π ^ m * π ^ n * e) • (1 : Etau K τ) + algebraMap O K h • y0 := by
        rw [hy0def, hc.om]
        simp only [yy, hA1, add_mul, smul_mul_assoc, mul_smul_comm, one_mul, hc.sq, smul_smul, map_mul]
        module
      rw [mul_two_dim_algebra_stable ω y0 _ _ _ _ _ _ hω hωy, ord_mem]
      exact ⟨p * h + q * (π ^ m * π ^ n * e), p * π ^ (n - m) + q * h, by simp only [map_add, map_mul]⟩
  constructor
  · intro hF
    obtain ⟨u, hu⟩ := unit_iff.1 (dual_iff.1 hF.dual)
    exact ⟨stab_iff.1 hF.stab, u, (c_iff u).1 hu⟩
  · rintro ⟨hmn, u, hu⟩
    exact ⟨⟨{1, y0}, by simp [PK.Ord]⟩, dual_iff.2 (unit_iff.2 ⟨u, (c_iff u).2 hu⟩), stab_iff.2 hmn⟩
