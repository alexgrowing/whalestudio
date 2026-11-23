import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL3.PHfTrace
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.SplitK
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IntegralClosureCriterionSecond

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits

variable (D : D7)

abbrev bb : D.host.E := D.host.sqd

abbrev be : ℂ := Complex.I * (Real.sqrt D.host.d : ℂ)

def OKc (z : ℂ) : Prop :=
  ∃ x y : ℤ, Even (x - y) ∧ z = ((x : ℂ) + (y : ℂ) * be D) / 2

theorem d_pos : (0 : ℝ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

theorem sqrt_pos : 0 < Real.sqrt D.host.d := Real.sqrt_pos.2 (d_pos D)

theorem sq_sqrtC : ((Real.sqrt D.host.d : ℝ) : ℂ) ^ 2 = (D.host.d : ℂ) := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (d_pos D).le]; simp

theorem be_sq : be D ^ 2 = -(D.host.d : ℂ) := by
  rw [be, mul_pow, Complex.I_sq, sq_sqrtC]; ring

theorem conj_be : starRingEnd ℂ (be D) = -be D := by
  simp [be, Complex.conj_ofReal]

theorem d_mod : ∃ k : ℤ, (D.host.d : ℤ) = 4 * k + 3 :=
  ⟨(D.host.d : ℤ) / 4, by have := D.host.hyp.2.2.2.1; omega⟩

theorem phi_b : D.host.φ₀ (bb D) = be D := D.host.φ₀_mem

theorem b_sq : bb D ^ 2 = -(D.host.d : D.host.E) := by
  apply D.host.φ₀.injective
  rw [map_pow, phi_b, be_sq, map_neg, map_natCast]

theorem bK_mem : bb D ∈ D.host.K := FL.bE_mem D

def bK : D.host.K := ⟨bb D, bK_mem D⟩

theorem phi_smul (s : ℚ) (x : D.host.E) : D.host.φ₀ (s • x) = (s : ℂ) * D.host.φ₀ x := by
  rw [Rat.smul_def, map_mul, map_ratCast]

theorem K_repr (u : D.host.K) :
    ∃ p q : ℚ, D.host.φ₀ (u : D.host.E) = (p : ℂ) + (q : ℂ) * be D := by
  have hK : Module.finrank ℚ D.host.K = 2 :=
    Formalism.FrobeniusOrbits.SplitK.finrank_K (L := D.host.E) (b := bb D) D.host.hyp.2.1.pos (b_sq D)
  have hli : LinearIndependent ℚ ![(1 : D.host.K), bK D] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg (fun x : D.host.K => D.host.φ₀ (x : D.host.E)) hst
    simp only [IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one,
      IntermediateField.coe_zero, map_add, phi_smul, map_one, map_zero, bK, phi_b, mul_one] at h1
    have hre := congrArg Complex.re h1
    have him := congrArg Complex.im h1
    simp [be] at hre him
    have hs := sqrt_pos D
    rcases him with h | h
    · exact ⟨by simpa [h] using hre, h⟩
    · exact absurd h D.host.hyp.2.1.ne_zero
  have hsp := hli.span_eq_top_of_card_eq_finrank (by simp [hK])
  have hu : u ∈ Submodule.span ℚ (Set.range ![(1 : D.host.K), bK D]) := by rw [hsp]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).1 hu
  refine ⟨c 0, c 1, ?_⟩
  rw [← hc, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
    IntermediateField.coe_add, IntermediateField.coe_smul, IntermediateField.coe_one, map_add,
    phi_smul, map_one, mul_one, bK, phi_b]

theorem int_of_rat (r : ℚ) (h : IsIntegral ℤ (r : ℂ)) : ∃ n : ℤ, r = n := by
  have h' : IsIntegral ℤ r := by
    refine (isIntegral_algHom_iff (algebraMap ℚ ℂ).toIntAlgHom (algebraMap ℚ ℂ).injective).mp ?_
    simpa using h
  obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨n, by rw [← hn]; simp⟩

abbrev psi : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)

theorem okc_of (u : 𝓞 D.host.K) : OKc D (D.host.φ₀ ((u : D.host.K) : D.host.E)) :=
  by apply _root_.UpperTheory.Reformulated.B.IntegralClosureCriterionSecond.okc_of <;> assumption

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

open Formalism.MainNotions.TaylorLogMetric

def Bf (w₁ w₂ : ℂ) : ℝ := (starRingEnd ℂ w₁ * w₂).im

theorem Bf_swap (w₁ w₂ : ℂ) : Bf w₂ w₁ = -Bf w₁ w₂ := by
  simp only [Bf, Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring

theorem Bf_sub_zsmul_left (u w w₂ : ℂ) (q : ℤ) : Bf (u - q • w) w₂ = Bf u w₂ - q * Bf w w₂ := by
  simp only [Bf, zsmul_eq_mul, map_sub, map_mul, map_intCast, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem Bf_sub_zsmul_right (w₁ u w : ℂ) (q : ℤ) : Bf w₁ (u - q • w) = Bf w₁ u - q * Bf w₁ w := by
  simp only [Bf, zsmul_eq_mul, Complex.mul_im, Complex.sub_re,
    Complex.sub_im, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cramer (w₁ w₂ u : ℂ) :
    (Bf u w₂ : ℂ) * w₁ + (Bf w₁ u : ℂ) * w₂ = (Bf w₁ w₂ : ℂ) * u := by
  apply Complex.ext <;>
    simp only [Bf, Complex.mul_im, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im] <;> ring

theorem Bf_comb (w₁ w₂ : ℂ) (s t s' t' : ℝ) :
    Bf ((s : ℂ) * w₁ + (t : ℂ) * w₂) ((s' : ℂ) * w₁ + (t' : ℂ) * w₂) = (s * t' - t * s') * Bf w₁ w₂ := by
  simp only [Bf, map_add, map_mul, Complex.conj_ofReal, Complex.mul_im, Complex.mul_re,
    Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re,
    Complex.conj_im]; ring

theorem cast_toNat (n : ℤ) (h : 0 ≤ n) : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg h]

theorem area_spec (Λ : AddSubgroup ℂ) (κ : ℝ) (hκ : 0 < κ)
    (hdisc : ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = κ * n)
    (hne : ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area Λ = κ * m ∧ ∀ w₁ ∈ Λ, ∀ w₂ ∈ Λ, ∃ n : ℤ, Bf w₁ w₂ = area Λ * n := by
  classical

  have hQ : ∃ n : ℕ, 0 < n ∧ ∃ w₁ ∈ Λ, ∃ w₂ ∈ Λ, Bf w₁ w₂ = κ * n := by
    obtain ⟨w₁, h₁, w₂, h₂, h0⟩ := hne
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ w₂ h₂
    rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
    · refine ⟨(-n).toNat, by omega, w₂, h₂, w₁, h₁, ?_⟩
      rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring
    · exact absurd (by rw [hn, hn0]; simp) h0
    · refine ⟨n.toNat, by omega, w₁, h₁, w₂, h₂, ?_⟩
      rw [hn, cast_toNat _ hn0.le]
  set m := Nat.find hQ with hm
  obtain ⟨hm0, w₁, h₁, w₂, h₂, hw⟩ := Nat.find_spec hQ
  have hmin : ∀ n : ℕ, 0 < n → ∀ u ∈ Λ, ∀ v ∈ Λ, Bf u v = κ * n → m ≤ n :=
    fun n hn u hu v hv h => Nat.find_min' hQ ⟨hn, u, hu, v, hv, h⟩

  have harea : area Λ = κ * m := by
    unfold area
    refine IsLeast.csInf_eq ⟨⟨by positivity, w₁, h₁, w₂, h₂, ?_⟩, ?_⟩
    · change κ * m = |Bf w₁ w₂|
      rw [hw, abs_of_nonneg (by positivity)]
    · rintro a ⟨ha, u, hu, v, hv, rfl⟩
      change κ * m ≤ |Bf u v|
      obtain ⟨n, hn⟩ := hdisc u hu v hv
      rcases lt_trichotomy n 0 with hn0 | hn0 | hn0
      · have := hmin (-n).toNat (by omega) v hv u hu (by
          rw [Bf_swap, hn, cast_toNat _ (by omega)]; push_cast; ring)
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_neg (by exact_mod_cast hn0 : (n : ℝ) < 0)]
        have h' : ((m : ℤ) : ℝ) ≤ ((-n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ -n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
      · exfalso; change 0 < |Bf u v| at ha; rw [hn, hn0] at ha; simp at ha
      · have := hmin n.toNat (by omega) u hu v hv (by rw [hn, cast_toNat _ hn0.le])
        rw [hn, abs_mul, abs_of_pos hκ, abs_of_pos (by exact_mod_cast hn0 : (0 : ℝ) < n)]
        have h' : ((m : ℤ) : ℝ) ≤ ((n : ℤ) : ℝ) := by exact_mod_cast (by omega : (m : ℤ) ≤ n)
        push_cast at h'
        exact mul_le_mul_of_nonneg_left h' hκ.le
  refine ⟨m, hm0, harea, ?_⟩
  set g := κ * m with hg
  have hg0 : 0 < g := by positivity

  have hleft : ∀ u ∈ Λ, ∃ q : ℤ, Bf u w₂ = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc u hu w₂ h₂
    refine ⟨n / m, ?_⟩
    have hr : Bf (u - (n / m) • w₁) w₂ = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_left, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) _ (Λ.sub_mem hu (Λ.zsmul_mem h₁ _)) w₂ h₂
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring
  have hright : ∀ u ∈ Λ, ∃ q : ℤ, Bf w₁ u = g * q := by
    intro u hu
    obtain ⟨n, hn⟩ := hdisc w₁ h₁ u hu
    refine ⟨n / m, ?_⟩
    have hr : Bf w₁ (u - (n / m) • w₂) = κ * ((n % m : ℤ) : ℝ) := by
      rw [Bf_sub_zsmul_right, hn, hw]
      have := Int.mul_ediv_add_emod n m
      have : (n : ℝ) = ((n % m : ℤ) : ℝ) + m * ((n / m : ℤ) : ℝ) := by
        have h2 : (n : ℝ) = ((m : ℤ) : ℝ) * ((n / m : ℤ) : ℝ) + ((n % m : ℤ) : ℝ) := by exact_mod_cast this.symm
        rw [h2]; push_cast; ring
      rw [this]; ring
    have hr0 : n % (m : ℤ) = 0 := by
      by_contra hne0
      have hpos : 0 < n % (m : ℤ) := lt_of_le_of_ne (Int.emod_nonneg _ (by omega)) (Ne.symm hne0)
      have hlt : n % (m : ℤ) < m := Int.emod_lt_of_pos _ (by omega)
      have := hmin (n % (m : ℤ)).toNat (by omega) w₁ h₁ _ (Λ.sub_mem hu (Λ.zsmul_mem h₂ _))
        (by rw [hr, cast_toNat _ hpos.le])
      omega
    have := Int.mul_ediv_add_emod n m
    rw [hr0, add_zero] at this
    have h3 : (n : ℝ) = (m : ℝ) * ((n / m : ℤ) : ℝ) := by exact_mod_cast this.symm
    rw [hn, hg, h3]; ring

  have hdec : ∀ u ∈ Λ, ∃ s t : ℤ, u = ((s : ℝ) : ℂ) * w₁ + ((t : ℝ) : ℂ) * w₂ := by
    intro u hu
    obtain ⟨s, hs⟩ := hleft u hu
    obtain ⟨t, ht⟩ := hright u hu
    refine ⟨s, t, ?_⟩
    have hc := cramer w₁ w₂ u
    rw [hs, ht, hw] at hc
    have hg0' : (g : ℂ) ≠ 0 := by exact_mod_cast hg0.ne'
    apply mul_left_cancel₀ hg0'
    rw [← hc]; push_cast; ring
  intro u hu v hv
  obtain ⟨s, t, rfl⟩ := hdec u hu
  obtain ⟨s', t', rfl⟩ := hdec v hv
  refine ⟨s * t' - t * s', ?_⟩
  rw [Bf_comb, hw, harea]; push_cast; ring

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

end

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.FrobeniusOrbits Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO

variable (D : D7)

abbrev ph (c : 𝓞 D.host.K) : ℂ := D.host.φ₀ (((c : D.host.K) : D.host.E))

theorem okc_mul {z w : ℂ} (hz : OKc D z) (hw : OKc D w) : OKc D (z * w) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  obtain ⟨x', y', ⟨a', ha'⟩, rfl⟩ := hw
  obtain ⟨k, hk⟩ := d_mod D
  obtain rfl : x = y + a + a := by omega
  obtain rfl : x' = y' + a' + a' := by omega
  refine ⟨-(2 * k + 1) * y * y' + a * y' + a' * y + 2 * a * a', y * y' + a * y' + a' * y,
    ⟨-(k + 1) * y * y' + a * a', by ring⟩, ?_⟩
  have hkC : (D.host.d : ℂ) = 4 * k + 3 := by exact_mod_cast hk
  have hsq := be_sq D
  push_cast
  linear_combination hsq * ((y : ℂ) * y' / 4) - hkC * ((y : ℂ) * y' / 4)

theorem okc_conj {z : ℂ} (hz : OKc D z) : OKc D (starRingEnd ℂ z) := by
  obtain ⟨x, y, ⟨a, ha⟩, rfl⟩ := hz
  refine ⟨x, -y, ⟨a + y, by omega⟩, ?_⟩
  rw [map_div₀, map_add, map_mul, conj_be, map_intCast, map_intCast, map_ofNat]; push_cast; ring

theorem coord_eq (x y : ℤ) :
    ((x : ℂ) + (y : ℂ) * be D) / 2 =
      (((x : ℝ) / 2 : ℝ) : ℂ) + (((y : ℝ) * Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

theorem im_coord (x y : ℤ) :
    (((x : ℂ) + (y : ℂ) * be D) / 2).im = (y : ℝ) * Real.sqrt D.host.d / 2 := by
  rw [coord_eq]; simp

theorem good_of_okc {u : ℂ} (hu : OKc D u) : Good D (2 * u / (Real.sqrt D.host.d : ℂ)) := by
  obtain ⟨x, y, hxy, rfl⟩ := hu
  refine ⟨x, y, hxy, ?_⟩
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  push_cast
  field_simp

theorem half_int {F : Type*} [Field F] [CharZero F] (x : F) (k : ℤ)
    (hx : x ^ 2 = -(4 * (k : F) + 3)) : IsIntegral ℤ ((1 + x) / 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C (k + 1), by monicity!, ?_⟩
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  push_cast
  linear_combination hx / 4

theorem bK_sq : bK D ^ 2 = -(D.host.d : D.host.K) := by
  apply Subtype.ext
  push_cast
  exact b_sq D

def om : 𝓞 D.host.K :=
  ⟨(1 + bK D) / 2, half_int _ (d_mod D).choose (by
    have h2 : ((D.host.d : ℤ) : D.host.K) = ((4 * (d_mod D).choose + 3 : ℤ) : D.host.K) :=
      congrArg (fun t : ℤ => (t : D.host.K)) (d_mod D).choose_spec
    push_cast at h2
    rw [bK_sq D]; linear_combination -h2)⟩

theorem ph_om : ph D (om D) = (1 + be D) / 2 := by
  show D.host.φ₀ ((((1 + bK D) / 2 : D.host.K)) : D.host.E) = _
  have h2 : ((2 : D.host.K) : D.host.E) = 2 := by
    rw [show (2 : D.host.K) = 1 + 1 by norm_num, IntermediateField.coe_add, IntermediateField.coe_one]
    norm_num
  push_cast
  rw [h2, map_div₀, map_add, map_one, map_ofNat]
  exact congrArg (fun t => (1 + t) / 2) (phi_b D)

theorem Bf_lat (δ : ℂ) (c₁ c₂ : 𝓞 D.host.K) :
    Bf (δ * ph D c₁) (δ * ph D c₂) = Complex.normSq δ * (starRingEnd ℂ (ph D c₁) * ph D c₂).im := by
  have : starRingEnd ℂ (δ * ph D c₁) * (δ * ph D c₂) =
      (Complex.normSq δ : ℂ) * (starRingEnd ℂ (ph D c₁) * ph D c₂) := by
    rw [Complex.normSq_eq_conj_mul_self, map_mul]; ring
  rw [Bf, this]; simp [Complex.mul_im]

theorem okc_pair (c₁ c₂ : 𝓞 D.host.K) : OKc D (starRingEnd ℂ (ph D c₁) * ph D c₂) :=
  okc_mul D (okc_conj D (okc_of D c₁)) (okc_of D c₂)

theorem div_okc (cc : Ideal (𝓞 D.host.K)) (hcc : cc ≠ ⊥) (δ : ℂ) (hδ : δ ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ area (lamOf D cc δ) = Complex.normSq δ * (Real.sqrt D.host.d / 2) * m ∧
      ∀ c ∈ cc, ∀ c' ∈ cc, OKc D (starRingEnd ℂ (ph D c') * ph D c / m) := by
  have hn : 0 < Complex.normSq δ := Complex.normSq_pos.2 hδ
  have hs := sqrt_pos D
  have hκ : 0 < Complex.normSq δ * (Real.sqrt D.host.d / 2) := by positivity
  have hdisc : ∀ w₁ ∈ lamOf D cc δ, ∀ w₂ ∈ lamOf D cc δ, ∃ n : ℤ,
      Bf w₁ w₂ = Complex.normSq δ * (Real.sqrt D.host.d / 2) * n := by
    intro w₁ h₁ w₂ h₂
    obtain ⟨c₁, -, rfl⟩ := FL.lam_mem D cc δ w₁ h₁
    obtain ⟨c₂, -, rfl⟩ := FL.lam_mem D cc δ w₂ h₂
    obtain ⟨x, y, -, hz⟩ := okc_pair D c₁ c₂
    refine ⟨y, ?_⟩
    rw [Bf_lat, hz, im_coord]; ring
  have hne : ∃ w₁ ∈ lamOf D cc δ, ∃ w₂ ∈ lamOf D cc δ, Bf w₁ w₂ ≠ 0 := by
    obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hcc
    refine ⟨δ * ph D c, AddSubgroup.subset_closure ⟨c, hc, rfl⟩,
      δ * ph D (c * om D), AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩, ?_⟩
    have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
      rw [← ph_om]; simp [ph]
    have hc1 : ph D c ≠ 0 := by
      simp only [ph, map_ne_zero_iff _ D.host.φ₀.injective]
      exact_mod_cast hc0
    rw [Bf_lat, hph]
    have e : starRingEnd ℂ (ph D c) * (ph D c * ((1 + be D) / 2)) =
        (Complex.normSq (ph D c) : ℂ) * ((1 + be D) / 2) := by
      rw [Complex.normSq_eq_conj_mul_self]; ring
    have e4 : (1 + be D) / 2 =
        (((1 : ℝ) / 2 : ℝ) : ℂ) + ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    have e5 : ((Complex.normSq (ph D c) : ℂ) * ((((1 : ℝ) / 2 : ℝ) : ℂ) +
        ((Real.sqrt D.host.d / 2 : ℝ) : ℂ) * Complex.I)).im =
        Complex.normSq (ph D c) * (Real.sqrt D.host.d / 2) := by simp [Complex.mul_im]
    rw [e, e4, e5]
    exact mul_ne_zero hn.ne' (mul_ne_zero (Complex.normSq_pos.2 hc1).ne' (by positivity))
  obtain ⟨m, hm, harea, hall⟩ := area_spec (lamOf D cc δ) _ hκ hdisc hne
  refine ⟨m, hm, harea, fun c hc c' hc' => ?_⟩
  obtain ⟨x, y, -, hz⟩ := okc_pair D c' c
  obtain ⟨n₁, h₁⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c, hc, rfl⟩)
  obtain ⟨n₂, h₂⟩ := hall _ (AddSubgroup.subset_closure ⟨c', hc', rfl⟩) _
    (AddSubgroup.subset_closure ⟨c * om D, cc.mul_mem_right _ hc, rfl⟩)
  have hph : ph D (c * om D) = ph D c * ((1 + be D) / 2) := by
    rw [← ph_om]; simp [ph]
  rw [Bf_lat, hz, im_coord, harea] at h₁
  rw [Bf_lat, hph, ← mul_assoc, hz, harea] at h₂
  have e2 : ((x : ℂ) + (y : ℂ) * be D) / 2 * ((1 + be D) / 2) =
      ((((x - D.host.d * y : ℤ) : ℂ) + ((x + y : ℤ) : ℂ) * be D) / 2) / 2 := by
    push_cast; linear_combination (y : ℂ) / 4 * be_sq D
  rw [e2, Complex.div_ofNat_im, im_coord] at h₂
  have hy : (y : ℝ) = m * n₁ := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (y - m * n₁) = 0 := by linear_combination h₁
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hxy : ((x + y : ℤ) : ℝ) = 2 * (m * n₂) := by
    have : Complex.normSq δ * (Real.sqrt D.host.d / 2) * (((x + y : ℤ) : ℝ) - 2 * (m * n₂)) = 0 := by
      linear_combination 2 * h₂
    have := (mul_eq_zero.1 this).resolve_left hκ.ne'
    linarith
  have hyZ : y = m * n₁ := by exact_mod_cast hy
  have hxZ : x = 2 * m * n₂ - m * n₁ := by
    have : x + y = 2 * (m * n₂) := by exact_mod_cast hxy
    linarith
  refine ⟨2 * n₂ - n₁, n₁, ⟨n₂ - n₁, by ring⟩, ?_⟩
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [hz, hxZ, hyZ]
  field_simp
  push_cast
  ring

def HYYIntRec : Prop :=
  ∀ D : D7, ∀ N N' (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' →
    ∀ A ∈ YYl D L L', ∀ B ∈ YYl D L L', IsIntegral ℤ (hYY D A B)

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

namespace Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.AR

theorem HfArithRec_of_int (h : HYYIntRec) : HfArithRec := by
  intro D cc hcc δ hδ h0 N N' L L' hA c hc c' hc' A hA' B hB'
  obtain ⟨m, hm, harea, hdiv⟩ := div_okc D cc hcc.1 δ h0
  have hh : OKc D (D.host.φ₀ ((hYY D A B : D.host.K) : D.host.E)) :=
    okc_of D ⟨hYY D A B, h D N N' L L' hA A hA' B hB'⟩
  have hprod := okc_mul D (hdiv c hc c' hc') hh
  have hg := good_of_okc D hprod
  convert hg using 1
  have hnz : (Complex.normSq δ : ℂ) ≠ 0 := by exact_mod_cast (Complex.normSq_pos.2 h0).ne'
  have hs : (Real.sqrt D.host.d : ℂ) ≠ 0 := by exact_mod_cast (sqrt_pos D).ne'
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hcd : starRingEnd ℂ δ ≠ 0 := by simpa using h0
  rw [harea]
  simp only [ph, map_mul]
  push_cast
  rw [Complex.normSq_eq_conj_mul_self] at hnz ⊢
  field_simp

end Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

end
