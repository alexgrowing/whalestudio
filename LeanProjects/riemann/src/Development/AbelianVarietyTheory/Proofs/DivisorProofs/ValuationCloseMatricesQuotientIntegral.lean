import Mathlib

namespace GlobalTheory

open Matrix

theorem inv_mul_congr_of_entries_congr_of_det_unit
    {K : Type} [Field K] (w : AbsoluteValue K ℝ) (O : ValuationSubring K)
    (hO : ∀ x, x ∈ O ↔ w x ≤ 1)
    {N : ℕ} (Γa Γb Aa Ab : Matrix (Fin N) (Fin N) K) (hΓa : ∀ i k, w (Γa i k) ≤ 1)
    (hΓb : ∀ i k, w (Γb i k) ≤ 1)
    (hdet : w Γa.det = 1) (ha : ∀ i k, w (Aa i k - Γa i k) < 1)
    (hb : ∀ i k, w (Ab i k - Γb i k) < 1) :
    w Aa.det = 1 ∧ ∀ i k, w ((Aa⁻¹ * Ab) i k - (Γa⁻¹ * Γb) i k) < 1 := by

  have hle : ∀ a b : K, w a ≤ w b → w (a + b) ≤ w b := by
    intro a b h
    rcases eq_or_ne b 0 with hb0 | hb0
    · subst hb0
      simp only [map_zero] at h
      simpa using h
    · have h1 : a / b ∈ O := (hO _).2 (by
        rw [map_div₀]; exact (div_le_one (w.pos hb0)).2 h)
      have h3 := (hO _).1 (O.add_mem _ _ O.one_mem h1)
      have e : a + b = b * (1 + a / b) := by field_simp; ring
      rw [e, map_mul]
      calc w b * w (1 + a / b) ≤ w b * 1 := mul_le_mul_of_nonneg_left h3 (w.nonneg _)
        _ = w b := mul_one _
  have hna : ∀ a b : K, w (a + b) ≤ max (w a) (w b) := by
    intro a b
    rcases le_total (w a) (w b) with h | h
    · exact (hle a b h).trans (le_max_right _ _)
    · rw [add_comm]; exact (hle b a h).trans (le_max_left _ _)

  have hunit : ∀ x : O, IsUnit x ↔ w (x : K) = 1 := by
    intro x
    constructor
    · rintro ⟨u, rfl⟩
      have h1 : w ((u : O) : K) ≤ 1 := (hO _).1 (u : O).2
      have h2 : w (((u⁻¹ : Oˣ) : O) : K) ≤ 1 := (hO _).1 ((u⁻¹ : Oˣ) : O).2
      have e : ((u : O) : K) * (((u⁻¹ : Oˣ) : O) : K) = 1 := by
        exact congrArg Subtype.val u.mul_inv
      have h3 : w ((u : O) : K) * w (((u⁻¹ : Oˣ) : O) : K) = 1 := by
        rw [← map_mul, e, map_one]
      nlinarith [mul_le_mul_of_nonneg_left h2 (w.nonneg ((u : O) : K)), w.nonneg ((u : O) : K),
        w.nonneg (((u⁻¹ : Oˣ) : O) : K)]
    · intro h
      have hx0 : (x : K) ≠ 0 := by
        intro h0; rw [h0, map_zero] at h; norm_num at h
      have hinv : (x : K)⁻¹ ∈ O := (hO _).2 (by rw [map_inv₀, h, inv_one])
      exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (by simp [hx0])⟩

  have hres : ∀ x y : O, IsLocalRing.residue O x = IsLocalRing.residue O y ↔ w ((x : K) - y) < 1 := by
    intro x y
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, hunit]
    have hle1 : w ((x - y : O) : K) ≤ 1 := (hO _).1 (x - y).2
    have ec : ((x - y : O) : K) = (x : K) - y := rfl
    rw [ec] at hle1 ⊢
    exact ⟨fun h => lt_of_le_of_ne hle1 h, fun h => ne_of_lt h⟩

  have hAa : ∀ i k, w (Aa i k) ≤ 1 := fun i k => by
    have := hna (Aa i k - Γa i k) (Γa i k)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (ha i k).le (hΓa i k))
  have hAb : ∀ i k, w (Ab i k) ≤ 1 := fun i k => by
    have := hna (Ab i k - Γb i k) (Γb i k)
    rw [sub_add_cancel] at this
    exact this.trans (max_le (hb i k).le (hΓb i k))
  let f : O →+* K := O.toSubring.subtype
  let r : O →+* IsLocalRing.ResidueField O := IsLocalRing.residue O
  let Ga' : Matrix (Fin N) (Fin N) O := Matrix.of fun i k => ⟨Γa i k, (hO _).2 (hΓa i k)⟩
  let Gb' : Matrix (Fin N) (Fin N) O := Matrix.of fun i k => ⟨Γb i k, (hO _).2 (hΓb i k)⟩
  let Aa' : Matrix (Fin N) (Fin N) O := Matrix.of fun i k => ⟨Aa i k, (hO _).2 (hAa i k)⟩
  let Ab' : Matrix (Fin N) (Fin N) O := Matrix.of fun i k => ⟨Ab i k, (hO _).2 (hAb i k)⟩
  have fGa : Ga'.map f = Γa := by ext i k; rfl
  have fGb : Gb'.map f = Γb := by ext i k; rfl
  have fAa : Aa'.map f = Aa := by ext i k; rfl
  have fAb : Ab'.map f = Ab := by ext i k; rfl
  have rA : Aa'.map r = Ga'.map r := by
    ext i k; exact (hres _ _).2 (ha i k)
  have rB : Ab'.map r = Gb'.map r := by
    ext i k; exact (hres _ _).2 (hb i k)

  have hmapinv : ∀ {R S : Type} [CommRing R] [CommRing S] (g : R →+* S)
      (M : Matrix (Fin N) (Fin N) R), IsUnit M.det → (M.map g)⁻¹ = M⁻¹.map g := by
    intro R S _ _ g M hM
    apply Matrix.inv_eq_left_inv
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hM, Matrix.map_one _ (map_zero g) (map_one g)]
  have detf : ∀ M : Matrix (Fin N) (Fin N) O, f M.det = (M.map f).det := fun M => RingHom.map_det f M
  have detr : ∀ M : Matrix (Fin N) (Fin N) O, r M.det = (M.map r).det := fun M => RingHom.map_det r M
  have uGa : IsUnit Ga'.det := by
    rw [hunit]; show w (f Ga'.det) = 1; rw [detf, fGa]; exact hdet
  have uAa : IsUnit Aa'.det := by
    rw [← isUnit_map_iff r, detr, rA, ← detr, isUnit_map_iff r]; exact uGa
  refine ⟨?_, ?_⟩
  · rw [← fAa, ← detf]; exact (hunit _).1 uAa
  · intro i k
    have eA : Aa⁻¹ * Ab = (Aa'⁻¹ * Ab').map f := by
      rw [Matrix.map_mul, ← hmapinv f _ uAa, fAa, fAb]
    have eG : Γa⁻¹ * Γb = (Ga'⁻¹ * Gb').map f := by
      rw [Matrix.map_mul, ← hmapinv f _ uGa, fGa, fGb]
    have er : (Aa'⁻¹ * Ab').map r = (Ga'⁻¹ * Gb').map r := by
      rw [Matrix.map_mul, Matrix.map_mul, ← hmapinv r _ uAa, ← hmapinv r _ uGa, rA, rB]
    rw [eA, eG]
    exact (hres _ _).1 (congrFun (congrFun er i) k)

end GlobalTheory
