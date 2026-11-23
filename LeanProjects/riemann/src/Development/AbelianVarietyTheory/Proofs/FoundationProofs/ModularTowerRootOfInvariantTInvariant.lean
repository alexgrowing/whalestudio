import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.TInv

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue

theorem const_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) : ∃ c : Ω, algebraMap Ω X.K c = x := by
  have hint : IsIntegral Ω x := IsIntegral.of_pow hL (by rw [hx]; exact isIntegral_one)
  have hdeg := IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint)
  obtain ⟨c, hc⟩ := RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (hx := hdeg))
  exact ⟨c, hc⟩

theorem cast_eq_of_dvd {d : ℕ} {y c : ℤ} (h : (d : ℤ) ∣ y - c) : (y : ZMod d) = (c : ZMod d) := ((ZMod.intCast_eq_intCast_iff_dvd_sub c y d).mpr h).symm

theorem exists_sl2_scalar_mod_coprime (A₁ A₂ : ℕ) (hcop : Nat.Coprime A₁ A₂) :
    ∃ δ : SL(2, ℤ), (A₁ : ℤ) ∣ δ 0 0 - 1 ∧ (A₁ : ℤ) ∣ δ 1 1 - 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 1 0 ∧
      ((A₁ : ℤ) * A₂) ∣ δ 0 1 ∧ (A₂ : ℤ) ∣ δ 0 0 + 1 ∧ (A₂ : ℤ) ∣ δ 1 1 + 1 ∧ ((A₁ : ℤ) * A₂) ∣ δ 0 0 - δ 1 1 := by
  obtain ⟨u, v, huv⟩ : IsCoprime ((A₁ : ℤ) ^ 2) ((A₂ : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow
  refine ⟨⟨!![v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2, (A₁ : ℤ) * A₂;
      -4 * u * v * ((A₁ : ℤ) * A₂), v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2], ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination (u * (A₁ : ℤ) ^ 2 + v * (A₂ : ℤ) ^ 2 + 1) * huv
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-2 * u * A₁, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - 1 = _
      linear_combination huv⟩
  · exact ⟨-4 * u * v, by
      show -4 * u * v * ((A₁ : ℤ) * A₂) = _
      ring⟩
  · exact ⟨1, by
      show (A₁ : ℤ) * A₂ = _
      ring⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨2 * v * A₂, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 + 1 = _
      linear_combination (-1 : ℤ) * huv⟩
  · exact ⟨0, by
      show v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2 - (v * (A₂ : ℤ) ^ 2 - u * (A₁ : ℤ) ^ 2) = _
      ring⟩

private lemma t_inv_mul_mul_t_mul_inv_mem_gamma {M : ℕ} (δ : SL(2, ℤ)) (hc : (M : ℤ) ∣ δ 1 0) (had : (M : ℤ) ∣ δ 0 0 - δ 1 1) :
    ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  have hc' : ((δ 1 0 : ℤ) : ZMod M) = 0 := by
    simpa using cast_eq_of_dvd (d := M) (c := 0) (by simpa using hc)
  have had' : ((δ 0 0 : ℤ) : ZMod M) = ((δ 1 1 : ℤ) : ZMod M) := cast_eq_of_dvd had
  rw [CongruenceSubgroup.Gamma_mem', map_mul, map_mul, map_mul, map_inv, map_inv, mul_inv_eq_one,
    mul_assoc, inv_mul_eq_iff_eq_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ModularGroup.coe_T, hc', had'] <;> ring

theorem exists_delta (N M l n : ℕ) (hl : l.Prime) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (hM : 0 < M) :
    ∃ δ : SL(2, ℤ), δ ∈ CongruenceSubgroup.Gamma1 N ∧ -δ ∈ CongruenceSubgroup.Gamma (l ^ n) ∧
      ModularGroup.T⁻¹ * δ * ModularGroup.T * δ⁻¹ ∈ CongruenceSubgroup.Gamma M := by
  obtain ⟨e, m, hlm, hM'⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' l hl.one_lt.ne'
  have hcl : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlm
  have hcN : Nat.Coprime l N := (Nat.Prime.coprime_iff_not_dvd hl).mpr hlN
  have hcop : Nat.Coprime (N * m) (l ^ (n + e)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.mul hcN.symm hcl.symm)
  obtain ⟨δ, h1, h2, h3, h4, h5, h6, h7⟩ := exists_sl2_scalar_mod_coprime (N * m) (l ^ (n + e)) hcop
  have hN1 : (N : ℤ) ∣ ((N * m : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr (Dvd.intro m rfl)
  have hln : ((l ^ n : ℕ) : ℤ) ∣ ((l ^ (n + e) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (pow_dvd_pow l (Nat.le_add_right n e))
  have hln' : ((l ^ n : ℕ) : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := Dvd.dvd.mul_left hln _
  have hMd : (M : ℤ) ∣ ((N * m : ℕ) : ℤ) * ((l ^ (n + e) : ℕ) : ℤ) := by
    have : M ∣ (N * m) * l ^ (n + e) := by
      rw [hM']
      exact ⟨N * l ^ n, by ring⟩
    exact_mod_cast this
  refine ⟨δ, ?_, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h1)
    · simpa using cast_eq_of_dvd (d := N) (dvd_trans hN1 h2)
    · simpa using cast_eq_of_dvd (d := N) (c := 0) (by rw [sub_zero]; exact dvd_trans (hN1.mul_right _) h3)
  · rw [CongruenceSubgroup.Gamma_mem]
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.neg_apply]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 0) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h5).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 0 1) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h4).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 0) (c := 0) (by rw [sub_zero]; exact (dvd_trans hln' h3).neg_right)
    · simpa using cast_eq_of_dvd (d := l ^ n) (y := -δ 1 1) (c := 1) (by rw [← neg_add']; exact (dvd_trans hln h6).neg_right)
  · exact t_inv_mul_mul_t_mul_inv_mem_gamma δ (dvd_trans hMd h3) (dvd_trans hMd h7)

private lemma sl_eq_self_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε)
    {L : ℕ} (hL : 0 < L) {x : X.K} (hx : x ^ L = 1) (g : GQ) : X.sl g x = x := by
  obtain ⟨c, rfl⟩ := const_of_pow_eq_one X hL hx
  exact (X.sl g).commutes c

theorem sl_T_eq {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l n : ℕ)
    (hl : l.Prime) (hl2 : l ≠ 2) (hlN : ¬ l ∣ N) (hN : 1 ≤ N) (u : X.K) (hu : u ≠ 0)
    (hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (u ^ (l ^ n)))
    (hδ : ∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) →
      ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (u * X.sl (ofSL δ) u) ^ (l ^ n) = g ^ (l ^ n)) :
    X.sl (ofSL ModularGroup.T) u = u := by
  have hL : 0 < l ^ n := pow_pos hl.pos n
  have hT : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 (N * l ^ n) := by
    rw [CongruenceSubgroup.Gamma1_mem]
    simp [ModularGroup.coe_T]
  have huL : u ^ (l ^ n) ≠ 0 := pow_ne_zero _ hu
  obtain ⟨ζ, hTu⟩ : ∃ ζ : X.K, X.sl (ofSL ModularGroup.T) u = ζ * u :=
    ⟨X.sl (ofSL ModularGroup.T) u / u, (div_mul_cancel₀ _ hu).symm⟩
  have hζL : ζ ^ (l ^ n) = 1 := by
    have h1 : X.sl (ofSL ModularGroup.T) (u ^ (l ^ n)) = u ^ (l ^ n) := hinv _ hT
    rw [map_pow, hTu, mul_pow] at h1
    exact mul_right_cancel₀ huL (h1.trans (one_mul _).symm)
  have hζfix : ∀ h : GQ, X.sl h ζ = ζ := fun h => sl_eq_self_of_pow_eq_one X hL hζL h
  obtain ⟨M, hM, hMu⟩ := X.level u
  obtain ⟨δ, hδ1, hδl, hδM⟩ := exists_delta N M l n hl hlN hN hM
  obtain ⟨g, hg, hgL⟩ := hδ δ hδ1 hδl
  have hsu : X.sl (ofSL δ) u ≠ 0 := fun h =>
    hu ((X.sl (ofSL δ)).injective (h.trans (map_zero _).symm))
  have hP0 : u * X.sl (ofSL δ) u ≠ 0 := mul_ne_zero hu hsu
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_pow hL.ne'] at hgL
    exact hP0 ((pow_eq_zero_iff hL.ne').mp hgL)
  have hw : (u * X.sl (ofSL δ) u / g) ^ (l ^ n) = 1 := by
    rw [div_pow, hgL, div_self (pow_ne_zero _ hg0)]
  have hTP : X.sl (ofSL ModularGroup.T) (u * X.sl (ofSL δ) u) = u * X.sl (ofSL δ) u := by
    rw [← div_mul_cancel₀ (u * X.sl (ofSL δ) u) hg0, map_mul, sl_eq_self_of_pow_eq_one X hL hw, hg _ hT]
  obtain ⟨γ, hγ, hγeq⟩ : ∃ γ ∈ CongruenceSubgroup.Gamma M,
      δ * ModularGroup.T = ModularGroup.T * γ * δ := ⟨_, hδM, by group⟩
  have hTδ : X.sl (ofSL ModularGroup.T) (X.sl (ofSL δ) u) = ζ * X.sl (ofSL δ) u := by
    rw [← X.sl_mul, ← map_mul ofSL δ ModularGroup.T, hγeq, map_mul, map_mul, X.sl_mul, X.sl_mul, hTu,
      map_mul (X.sl (ofSL γ)), hζfix, hMu γ hγ, map_mul (X.sl (ofSL δ)), hζfix]
  have hsq : ζ ^ 2 = 1 := by
    have h := hTP
    rw [map_mul, hTu, hTδ] at h
    have h2 : ζ ^ 2 * (u * X.sl (ofSL δ) u) = 1 * (u * X.sl (ofSL δ) u) := by
      linear_combination h
    exact mul_right_cancel₀ hP0 h2
  have hodd : Odd (l ^ n) := (hl.odd_of_ne_two hl2).pow
  obtain ⟨k, hk⟩ := hodd
  have hζ1 : ζ = 1 := by
    have h3 : ζ ^ (l ^ n) = ζ := by rw [hk, pow_succ, pow_mul, hsq, one_pow, one_mul]
    rw [← h3, hζL]
  rw [hTu, hζ1, one_mul]

end GlobalTheory.TInv
