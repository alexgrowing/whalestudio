import Formalism.EllipticTorsion.WChordSeries

open PowerSeries

universe u

noncomputable section

namespace Formalism.ELL
namespace WeierstrassChordSeries

section Alg
variable {R : Type*} [CommRing R]

def G (a1 a2 a3 a4 a6 z v : R) : R :=
  z ^ 3 + a1 * (z * v) + a2 * (z ^ 2 * v) + a3 * v ^ 2 + a4 * (z * v ^ 2) + a6 * v ^ 3 - v

def c3 (a2 a4 a6 l : R) : R := 1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3
def c2 (a1 a2 a3 a4 a6 l n : R) : R :=
  a1 * l + a2 * n + a3 * l ^ 2 + 2 * a4 * l * n + 3 * a6 * l ^ 2 * n
def c1 (a1 a3 a4 a6 l n : R) : R :=
  a1 * n + 2 * a3 * l * n + a4 * n ^ 2 + 3 * a6 * l * n ^ 2 - l
def c0 (a3 a6 n : R) : R := a3 * n ^ 2 + a6 * n ^ 3 - n

lemma G_line (a1 a2 a3 a4 a6 l n z : R) :
    G a1 a2 a3 a4 a6 z (l * z + n) = c3 a2 a4 a6 l * z ^ 3 + c2 a1 a2 a3 a4 a6 l n * z ^ 2
      + c1 a1 a3 a4 a6 l n * z + c0 a3 a6 n := by
  unfold G c3 c2 c1 c0
  ring

lemma vieta [IsDomain R] {a1 a2 a3 a4 a6 l n z1 z2 z3 : R} (hz : z1 ≠ z2)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0 ∧
      c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0 := by
  have k1 := h1
  have k2 := h2
  rw [G_line] at k1 k2
  have k : (z1 - z2) * (c3 a2 a4 a6 l * (z1 ^ 2 + z1 * z2 + z2 ^ 2)
      + c2 a1 a2 a3 a4 a6 l n * (z1 + z2) + c1 a1 a3 a4 a6 l n) = 0 := by
    linear_combination k1 - k2
  have k' := (mul_eq_zero.mp k).resolve_left (sub_ne_zero.mpr hz)
  have e2 : c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0 := by
    linear_combination (z1 + z2) * he1 - k'
  have e3 : c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0 := by
    linear_combination k1 - z1 ^ 2 * he1 + z1 * e2
  refine ⟨?_, e2, e3⟩
  rw [G_line]
  linear_combination z3 ^ 2 * he1 - z3 * e2 + e3

lemma G_inv [IsDomain R] {a1 a2 a3 a4 a6 z v f u d : R} (hf : f * d = z) (hu : u * d = v)
    (hd : d = -1 + a1 * z + a3 * v) (hd0 : d ≠ 0) (hG : G a1 a2 a3 a4 a6 z v = 0) :
    G a1 a2 a3 a4 a6 f u = 0 := by
  subst hf hu
  have key : d ^ 3 * G a1 a2 a3 a4 a6 f u = 0 := by
    unfold G at hG ⊢
    linear_combination hG - u * d * (d - 1) * hd
  exact (mul_eq_zero.mp key).resolve_left (pow_ne_zero 3 hd0)

lemma G_zero (a1 a2 a3 a4 a6 z : R) : G a1 a2 a3 a4 a6 z 0 = z ^ 3 := by
  unfold G
  ring

section maps
variable {R' : Type*} [CommRing R'] (φ : R →+* R')
lemma map_lineCoeffCubic (a2 a4 a6 l : R) : φ (c3 a2 a4 a6 l) = c3 (φ a2) (φ a4) (φ a6) (φ l) := by
  simp [c3]
lemma map_lineCoeffQuadratic (a1 a2 a3 a4 a6 l n : R) :
    φ (c2 a1 a2 a3 a4 a6 l n) = c2 (φ a1) (φ a2) (φ a3) (φ a4) (φ a6) (φ l) (φ n) := by
  have h2 : φ 2 = 2 := map_ofNat φ 2
  have h3 : φ 3 = 3 := map_ofNat φ 3
  simp [c2, h2, h3]
lemma map_lineCoeffLinear (a1 a3 a4 a6 l n : R) :
    φ (c1 a1 a3 a4 a6 l n) = c1 (φ a1) (φ a3) (φ a4) (φ a6) (φ l) (φ n) := by
  have h2 : φ 2 = 2 := map_ofNat φ 2
  have h3 : φ 3 = 3 := map_ofNat φ 3
  simp [c1, h2, h3]
lemma map_lineCoeffConst (a3 a6 n : R) : φ (c0 a3 a6 n) = c0 (φ a3) (φ a6) (φ n) := by
  simp [c0]
end maps

section mem
variable (T : Subring R)
lemma two_mem : (2 : R) ∈ T := by
  rw [← one_add_one_eq_two]
  exact T.add_mem T.one_mem T.one_mem
lemma three_mem : (3 : R) ∈ T := by
  rw [show (3 : R) = 2 + 1 by norm_num]
  exact T.add_mem (two_mem T) T.one_mem
lemma lineCoeffCubic_mem {a2 a4 a6 l : R} (h2 : a2 ∈ T) (h4 : a4 ∈ T) (h6 : a6 ∈ T) (hl : l ∈ T) :
    c3 a2 a4 a6 l ∈ T := by
  unfold c3
  exact T.add_mem (T.add_mem (T.add_mem T.one_mem (T.mul_mem h2 hl)) (T.mul_mem h4 (T.pow_mem hl 2)))
    (T.mul_mem h6 (T.pow_mem hl 3))
lemma lineCoeffQuadratic_mem {a1 a2 a3 a4 a6 l n : R} (h1 : a1 ∈ T) (h2 : a2 ∈ T) (h3 : a3 ∈ T) (h4 : a4 ∈ T)
    (h6 : a6 ∈ T) (hl : l ∈ T) (hn : n ∈ T) : c2 a1 a2 a3 a4 a6 l n ∈ T := by
  unfold c2
  exact T.add_mem (T.add_mem (T.add_mem (T.add_mem (T.mul_mem h1 hl) (T.mul_mem h2 hn))
    (T.mul_mem h3 (T.pow_mem hl 2))) (T.mul_mem (T.mul_mem (T.mul_mem (two_mem T) h4) hl) hn))
    (T.mul_mem (T.mul_mem (T.mul_mem (three_mem T) h6) (T.pow_mem hl 2)) hn)
end mem

end Alg

section Fld
variable {F : Type*} [Field F]

lemma chord_field (a1 a2 a3 a4 a6 z1 z2 z3 v1 v2 v3 l n f u D : F)
    (hv1 : v1 = l * z1 + n) (hv2 : v2 = l * z2 + n) (hv3 : v3 = l * z3 + n)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0)
    (he2 : c3 a2 a4 a6 l * (z1 * z2 + z1 * z3 + z2 * z3) - c1 a1 a3 a4 a6 l n = 0)
    (he3 : c3 a2 a4 a6 l * (z1 * z2 * z3) + c0 a3 a6 n = 0)
    (hc3 : c3 a2 a4 a6 l ≠ 0) (h1 : v1 ≠ 0) (h2 : v2 ≠ 0) (h3 : v3 ≠ 0) (hn : n ≠ 0)
    (hz : z1 ≠ z2) (hD : D = -1 + a1 * z3 + a3 * v3) (hD0 : D ≠ 0) (hf : f * D = z3)
    (hu : u * D = v3) :
    f / u = ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2 ∧
    -1 / u = -((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2) *
        ((((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - z1 / v1)
        + -1 / v1) - a1 * (((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) ^ 2
        + a1 * ((-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2)) - a2 - z1 / v1 - z2 / v2) - a3 := by
  simp only [c3, c2, c1, c0] at he1 he2 he3 hc3
  have hz' : z1 - z2 ≠ 0 := sub_ne_zero.mpr hz
  have hf' := (eq_div_iff hD0).mpr hf
  have hu' := (eq_div_iff hD0).mpr hu
  have hxd : z1 / v1 - z2 / v2 = n * (z1 - z2) / (v1 * v2) := by
    rw [div_sub_div _ _ h1 h2]
    congr 1
    rw [hv1, hv2]
    ring
  have hyd : -1 / v1 - -1 / v2 = l * (z1 - z2) / (v1 * v2) := by
    rw [div_sub_div _ _ h1 h2]
    congr 1
    rw [hv1, hv2]
    ring
  have hl : (-1 / v1 - -1 / v2) / (z1 / v1 - z2 / v2) = l / n := by
    rw [hxd, hyd]
    first
      | rw [div_div_div_cancel_right₀ (mul_ne_zero h1 h2), mul_div_mul_right _ _ hz']
      | (field_simp; done)
      | (field_simp
         ring)
  have hG : n ^ 2 * (z3 * (l * z1 + n) * (l * z2 + n) + z1 * (l * z2 + n) * (l * z3 + n) + z2 * (l * z1 + n) * (l * z3 + n)) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * ((l * z1 + n) * (l * z2 + n) * (l * z3 + n)) = 0 := by
    have hc : (1 + a2 * l + a4 * l ^ 2 + a6 * l ^ 3) * (n ^ 2 * (z3 * (l * z1 + n) * (l * z2 + n) + z1 * (l * z2 + n) * (l * z3 + n) + z2 * (l * z1 + n) * (l * z3 + n)) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * ((l * z1 + n) * (l * z2 + n) * (l * z3 + n))) = 0 := by
      linear_combination (n ^ 2 * (n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he1 + (l * n * (2 * n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he2 + (l ^ 2 * (3 * n ^ 2 - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * l)) * he3
    exact (mul_eq_zero.mp hc).resolve_left hc3
  have hG' : n ^ 2 * (z3 * v1 * v2 + z1 * v2 * v3 + z2 * v1 * v3) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * (v1 * v2 * v3) = 0 := by
    rw [hv1, hv2, hv3]
    exact hG
  have hsum : z3 / v3 = (l / n) ^ 2 + a1 * (l / n) - a2 - z1 / v1 - z2 / v2 := by
    rw [← sub_eq_zero]
    have e : z3 / v3 - ((l / n) ^ 2 + a1 * (l / n) - a2 - z1 / v1 - z2 / v2)
        = (n ^ 2 * (z3 * v1 * v2 + z1 * v2 * v3 + z2 * v1 * v3) - (l ^ 2 + a1 * l * n - a2 * n ^ 2) * (v1 * v2 * v3)) / (n ^ 2 * (v1 * v2 * v3)) := by
      field_simp
      ring
    rw [e, hG', zero_div]
  have hx3 : f / u = z3 / v3 := by
    rw [hf', hu']
    first
      | exact div_div_div_cancel_right₀ hD0 _ _
      | (field_simp; done)
      | (field_simp
         ring)
  refine ⟨?_, ?_⟩
  · rw [hl, hx3]
    exact hsum
  · rw [hl, ← hsum, hu']
    field_simp
    subst hD hv1 hv2 hv3
    ring

end Fld

section Wser
variable {K : Type u} [Field K] (W : WeierstrassCurve K)

def fw (v : PowerSeries K) : PowerSeries K :=
  X ^ 3 + C W.a₁ * X * v + C W.a₂ * X ^ 2 * v + C W.a₃ * v ^ 2 + C W.a₄ * X * v ^ 2
    + C W.a₆ * v ^ 3

lemma fw_cong {n : ℕ} {v v' : PowerSeries K} (h : X ^ n ∣ v - v') (hv : X ∣ v) (hv' : X ∣ v') :
    X ^ (n + 1) ∣ fw W v - fw W v' := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨b, rfl⟩ := hv
  obtain ⟨b', rfl⟩ := hv'
  refine ⟨C W.a₁ * a + C W.a₂ * X * a + C W.a₃ * a * (b + b') + C W.a₄ * X * a * (b + b')
    + C W.a₆ * X * a * (b ^ 2 + b * b' + b' ^ 2), ?_⟩
  unfold fw
  linear_combination (X * (C W.a₁ + C W.a₂ * X + C W.a₃ * (b + b') + C W.a₄ * X * (b + b')
    + C W.a₆ * X * (b ^ 2 + b * b' + b' ^ 2))) * ha

lemma fw_X_dvd {v : PowerSeries K} (hv : X ∣ v) : X ∣ fw W v := by
  obtain ⟨b, rfl⟩ := hv
  exact ⟨X ^ 2 + C W.a₁ * X * b + C W.a₂ * X ^ 2 * b + C W.a₃ * X * b ^ 2 + C W.a₄ * X ^ 2 * b ^ 2
    + C W.a₆ * X ^ 2 * b ^ 3, by unfold fw; ring⟩

def it : ℕ → PowerSeries K
  | 0 => 0
  | k + 1 => fw W (it k)

variable {W}

lemma it_spec {w : PowerSeries K} (hw : WFixed W w) :
    ∀ k, X ^ k ∣ w - it W k ∧ X ∣ it W k := by
  have hfix : fw W w = w := hw.2.symm
  have hXw : X ∣ w := PowerSeries.X_dvd_iff.mpr hw.1
  intro k
  induction k with
  | zero => exact ⟨by simp, by simp [it]⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · have e : w - it W (k + 1) = fw W w - fw W (it W k) := by
        rw [hfix]
        rfl
      rw [e]
      exact fw_cong W h1 hXw h2
    · exact fw_X_dvd W h2

lemma it_mem (S : Subalgebra ℤ K) (hS : ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) ⊆ S) :
    ∀ k, it W k ∈ (PowerSeries.map (algebraMap S K)).range := by
  have hX : (X : PowerSeries K) ∈ (PowerSeries.map (algebraMap S K)).range :=
    RingHom.mem_range.mpr ⟨X, PowerSeries.map_X _⟩
  have hC : ∀ a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K),
      (C a : PowerSeries K) ∈ (PowerSeries.map (algebraMap S K)).range := fun a ha =>
    RingHom.mem_range.mpr ⟨C ⟨a, hS ha⟩, by rw [PowerSeries.map_C]; rfl⟩
  have h1 := hC W.a₁ (by simp)
  have h2 := hC W.a₂ (by simp)
  have h3 := hC W.a₃ (by simp)
  have h4 := hC W.a₄ (by simp)
  have h6 := hC W.a₆ (by simp)
  intro k
  induction k with
  | zero => exact zero_mem _
  | succ k ih =>
    show fw W (it W k) ∈ _
    unfold fw
    exact add_mem (add_mem (add_mem (add_mem (add_mem (pow_mem hX 3) (mul_mem (mul_mem h1 hX) ih))
      (mul_mem (mul_mem h2 (pow_mem hX 2)) ih)) (mul_mem h3 (pow_mem ih 2)))
      (mul_mem (mul_mem h4 hX) (pow_mem ih 2))) (mul_mem h6 (pow_mem ih 3))

lemma w_coeff_mem {w : PowerSeries K} (hw : WFixed W w) (m : ℕ) :
    coeff m w ∈ Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K) := by
  have h := (it_spec hw (m + 1)).1
  rw [PowerSeries.X_pow_dvd_iff] at h
  have hm := h m (Nat.lt_succ_self m)
  rw [map_sub, sub_eq_zero] at hm
  rw [hm]
  obtain ⟨p, hp⟩ := RingHom.mem_range.mp (it_mem
    (Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) Algebra.subset_adjoin (m + 1))
  rw [← hp, PowerSeries.coeff_map]
  exact (coeff m p).2

lemma w_low {w : PowerSeries K} (hw : WFixed W w) :
    coeff 0 w = 0 ∧ coeff 1 w = 0 ∧ coeff 2 w = 0 ∧ coeff 3 w = 1 := by
  have hfix : fw W w = w := hw.2.symm
  have hXw : X ∣ w := PowerSeries.X_dvd_iff.mpr hw.1
  have h0 : fw W 0 = X ^ 3 := by simp [fw]
  have step : ∀ n, X ^ n ∣ w → X ^ (n + 1) ∣ w - X ^ 3 := fun n hn => by
    have := fw_cong W (n := n) (v := w) (v' := 0) (by simpa using hn) hXw (dvd_zero _)
    rwa [hfix, h0] at this
  have lift : ∀ n ≤ 3, X ^ n ∣ w - X ^ 3 → X ^ n ∣ w := fun n hn h => by
    have := dvd_add h (pow_dvd_pow (X : PowerSeries K) hn)
    simpa using this
  have h2 : X ^ 2 ∣ w := lift 2 (by norm_num) (step 1 (by simpa using hXw))
  have h3 : X ^ 3 ∣ w := lift 3 le_rfl (step 2 h2)
  have h4 := step 3 h3
  rw [PowerSeries.X_pow_dvd_iff] at h4
  have c : ∀ i < 4, coeff i w = if i = 3 then 1 else 0 := fun i hi => by
    have := h4 i hi
    rwa [map_sub, PowerSeries.coeff_X_pow, sub_eq_zero] at this
  exact ⟨by simpa using c 0 (by norm_num), by simpa using c 1 (by norm_num),
    by simpa using c 2 (by norm_num), by simpa using c 3 (by norm_num)⟩

end Wser

section Mser
variable {K : Type u} [Field K]

lemma eq_single_iff (e : Fin 2 →₀ ℕ) :
    (e = Finsupp.single 1 (e 1) ↔ e 0 = 0) ∧ (e = Finsupp.single 0 (e 0) ↔ e 1 = 0) := by
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [h]
    simp [Finsupp.single_apply]
  · ext j
    fin_cases j <;> simp [h, Finsupp.single_apply]
  · rw [h]
    simp [Finsupp.single_apply]
  · ext j
    fin_cases j <;> simp [h, Finsupp.single_apply]

def lam (w : PowerSeries K) : MvPowerSeries (Fin 2) K := fun e => coeff (e 0 + e 1 + 1) w

lemma coeff_lam (w : PowerSeries K) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam w) = coeff (e 0 + e 1 + 1) w := rfl

def Wi (w : PowerSeries K) (i : Fin 2) : MvPowerSeries (Fin 2) K := w.subst (MvPowerSeries.X i)

lemma coeff_Wi (w : PowerSeries K) (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (Wi w i) = if e = Finsupp.single i (e i) then coeff (e i) w else 0 := by
  have ha : PowerSeries.HasSubst (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) := by
    first
      | exact PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
      | exact PowerSeries.HasSubst.X i
      | exact PowerSeries.HasSubst.X'
  rw [Wi, PowerSeries.coeff_subst ha]
  first
    | simp only [MvPowerSeries.coeff_X_pow]
    | simp only [MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial]
  split_ifs with h
  · rw [finsum_eq_single _ (e i)]
    · rw [if_pos h, smul_eq_mul, mul_one]
    · intro d hd
      rw [if_neg, smul_zero]
      intro h'
      apply hd
      rw [h']
      simp
  · have hz : ∀ d : ℕ, (coeff d w • if e = Finsupp.single i d then (1 : K) else 0) = 0 := by
      intro d
      rw [if_neg, smul_zero]
      intro h'
      apply h
      rw [h']
      simp
    simp only [hz, finsum_zero]

private theorem coeff_mul_X_fin_two (φ : MvPowerSeries (Fin 2) K) (j : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (φ * MvPowerSeries.X j) =
      if Finsupp.single j 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single j 1) φ else 0 := by
  rw [show (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) =
      MvPowerSeries.monomial (Finsupp.single j 1) 1 from rfl, MvPowerSeries.coeff_mul_monomial]
  try simp only [mul_one]

private theorem single_one_le_iff_ne_zero (j : Fin 2) (e : Fin 2 →₀ ℕ) : Finsupp.single j 1 ≤ e ↔ e j ≠ 0 := by
  first
    | (rw [Finsupp.single_le_iff]
       exact Nat.one_le_iff_ne_zero)
    | (rw [Finsupp.le_def]
       constructor
       · intro h
         have := h j
         simp at this
         omega
       · intro h k
         by_cases hk : j = k
         · subst hk
           simp
           omega
         · simp [Finsupp.single_apply, hk])

lemma lam_mul (w : PowerSeries K) :
    (MvPowerSeries.X 1 - MvPowerSeries.X 0) * lam w = Wi w 1 - Wi w 0 := by
  have key : ∀ a b : ℕ, a = b → coeff a w = coeff b w := fun a b h => h ▸ rfl
  ext e
  rw [sub_mul, map_sub, map_sub, mul_comm (MvPowerSeries.X 1), mul_comm (MvPowerSeries.X 0), coeff_mul_X_fin_two,
    coeff_mul_X_fin_two, coeff_Wi, coeff_Wi, coeff_lam, coeff_lam]
  simp only [(eq_single_iff e).1, (eq_single_iff e).2, single_one_le_iff_ne_zero]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0 <;>
    simp [h0, h1] <;>
    first
      | (apply key; omega)
      | (rw [sub_eq_zero]; apply key; omega)
      | (rw [neg_inj]; apply key; omega)
      | (apply Eq.symm; apply key; omega)

local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff

lemma L_mul (φ ψ : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    (L i) (φ * ψ) = cc φ * (L i) ψ + (L i) φ * cc ψ := by
  first
    | (rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single, Finset.sum_map]
       simp [Finset.Nat.sum_antidiagonal_succ, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
       try ring
       done)
    | (rw [MvPowerSeries.coeff_mul, Finset.sum_eq_add (0, Finsupp.single i 1) (Finsupp.single i 1, 0)]
       · simp only [MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
         try ring
       · simp
       · rintro ⟨a, b⟩ hab hne
         rw [Finset.mem_antidiagonal] at hab
         exfalso
         have hj : ∀ j, a j + b j = (Finsupp.single i 1) j := fun j => by rw [← Finsupp.add_apply, hab]
         by_cases ha : a i = 0
         · apply hne.1
           have a0 : a = 0 := by
             ext j
             have := hj j
             by_cases hij : i = j
             · subst hij
               simp [ha]
             · simp [Finsupp.single_apply, hij] at this
               simp
               omega
           subst a0
           simp at hab
           rw [hab]
         · apply hne.2
           have b0 : b = 0 := by
             ext j
             have := hj j
             by_cases hij : i = j
             · subst hij
               simp at this
               simp
               omega
             · simp [Finsupp.single_apply, hij] at this
               simp
               omega
           subst b0
           simp at hab
           rw [hab]
       · intro h
         exfalso
         apply h
         simp [Finset.mem_antidiagonal]
       · intro h
         exfalso
         apply h
         simp [Finset.mem_antidiagonal]
       done)

lemma L_C (a : K) (i : Fin 2) : (L i) (MvPowerSeries.C a : MvPowerSeries (Fin 2) K) = 0 := by
  simp [MvPowerSeries.coeff_C]

lemma L_X (i j : Fin 2) : (L i) (MvPowerSeries.X j : MvPowerSeries (Fin 2) K) = if i = j then 1 else 0 := by
  rw [MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · have h' : Finsupp.single i 1 ≠ Finsupp.single j 1 := fun e => h (Finsupp.single_left_injective one_ne_zero e)
    rw [if_neg h', if_neg h]

lemma mul_vanishing_order_two {φ : MvPowerSeries (Fin 2) K} (h0 : cc φ = 0) (h1 : ∀ i, (L i) φ = 0)
    (ψ : MvPowerSeries (Fin 2) K) : cc (φ * ψ) = 0 ∧ ∀ i, (L i) (φ * ψ) = 0 := by
  exact ⟨by rw [map_mul, h0, zero_mul], fun i => by rw [L_mul, h0, h1 i]; ring⟩

variable (W : WeierstrassCurve K) (w : PowerSeries K)

def nu : MvPowerSeries (Fin 2) K := Wi w 0 - lam w * MvPowerSeries.X 0

abbrev ca (a : K) : MvPowerSeries (Fin 2) K := MvPowerSeries.C a

def C3 : MvPowerSeries (Fin 2) K := c3 (ca W.a₂) (ca W.a₄) (ca W.a₆) (lam w)
def C2 : MvPowerSeries (Fin 2) K :=
  c2 (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) (lam w) (nu w)

def z3 : MvPowerSeries (Fin 2) K :=
  -MvPowerSeries.X 0 - MvPowerSeries.X 1 - C2 W w * (C3 W w)⁻¹
def w3 : MvPowerSeries (Fin 2) K := lam w * z3 W w + nu w
def dd : MvPowerSeries (Fin 2) K := -1 + ca W.a₁ * z3 W w + ca W.a₃ * w3 W w

def F2 : MvPowerSeries (Fin 2) K := z3 W w * (dd W w)⁻¹
def wF : MvPowerSeries (Fin 2) K := w3 W w * (dd W w)⁻¹

variable {W w}

lemma Wi_cc (hw : WFixed W w) (i : Fin 2) : cc (Wi w i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Wi]
  simp [(w_low hw).1, hw.1]

lemma Wi_L (hw : WFixed W w) (i j : Fin 2) : (L j) (Wi w i) = 0 := by
  rw [coeff_Wi]
  by_cases h : j = i
  · subst h
    simp [(w_low hw).2.1]
  · simp [Finsupp.single_apply, h, (w_low hw).1, hw.1]

lemma lam_cc (hw : WFixed W w) : cc (lam w) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lam]
  simp [(w_low hw).2.1]

lemma lam_L (hw : WFixed W w) (i : Fin 2) : (L i) (lam w) = 0 := by
  have h : (Finsupp.single i 1) 0 + (Finsupp.single i 1) 1 = 1 := by
    fin_cases i <;> simp
  rw [coeff_lam, h]
  exact (w_low hw).2.2.1

lemma nu_cc (hw : WFixed W w) : cc (nu w) = 0 := by
  simp [nu, Wi_cc hw, lam_cc hw]

lemma nu_L (hw : WFixed W w) (i : Fin 2) : (L i) (nu w) = 0 := by
  rw [nu, map_sub, L_mul, Wi_L hw, lam_cc hw, lam_L hw]
  simp

lemma nu_ne (hw : WFixed W w) : nu w ≠ 0 := by
  intro h
  have h3 := (w_low hw).2.2.2
  have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 2 + Finsupp.single 1 1)) h
  rw [nu, map_sub, coeff_mul_X_fin_two, coeff_Wi, coeff_lam] at this
  first
    | simp only [(eq_single_iff _).2, single_one_le_iff_ne_zero] at this
    | skip
  simp [h3] at this

lemma constantCoeff_chordCoeffCubic (hw : WFixed W w) : cc (C3 W w) = 1 := by
  simp [C3, c3, lam_cc hw]

lemma constantCoeff_chordCoeffQuadratic (hw : WFixed W w) : cc (C2 W w) = 0 := by
  simp [C2, c2, lam_cc hw, nu_cc hw]

private theorem cc_L_mul_eq_zero_of_vanishing {φ : MvPowerSeries (Fin 2) K} (h0 : cc φ = 0) (h1 : ∀ i, (L i) φ = 0)
    (ψ : MvPowerSeries (Fin 2) K) : cc (ψ * φ) = 0 ∧ ∀ i, (L i) (ψ * φ) = 0 := by
  rw [mul_comm]
  exact mul_vanishing_order_two h0 h1 ψ

lemma linearCoeff_chordCoeffQuadratic (hw : WFixed W w) (i : Fin 2) : (L i) (C2 W w) = 0 := by
  have hs0 := lam_cc hw
  have hs1 := lam_L hw
  have hn0 := nu_cc hw
  have hn1 := nu_L hw
  have hss := mul_vanishing_order_two hs0 hs1 (lam w)
  rw [C2, c2, pow_two]
  simp only [map_add, (cc_L_mul_eq_zero_of_vanishing hs0 hs1 _).2 i, (cc_L_mul_eq_zero_of_vanishing hn0 hn1 _).2 i,
    (cc_L_mul_eq_zero_of_vanishing hss.1 hss.2 _).2 i, add_zero]

lemma constantCoeff_thirdParam (hw : WFixed W w) : cc (z3 W w) = 0 := by
  simp [z3, constantCoeff_chordCoeffQuadratic hw]

lemma linearCoeff_thirdParam (hw : WFixed W w) (i : Fin 2) : (L i) (z3 W w) = -1 := by
  rw [z3, map_sub, map_sub, map_neg, L_mul, constantCoeff_chordCoeffQuadratic hw,
    linearCoeff_chordCoeffQuadratic hw, L_X, L_X]
  fin_cases i <;> simp

lemma constantCoeff_thirdValue (hw : WFixed W w) : cc (w3 W w) = 0 := by
  simp [w3, constantCoeff_thirdParam hw, nu_cc hw]

lemma dd_cc (hw : WFixed W w) : cc (dd W w) = -1 := by
  simp [dd, constantCoeff_thirdParam hw, constantCoeff_thirdValue hw]

lemma constantCoeff_formalSum (hw : WFixed W w) : cc (F2 W w) = 0 := by
  simp [F2, constantCoeff_thirdParam hw]

lemma linearCoeff_formalSum (hw : WFixed W w) (i : Fin 2) : (L i) (F2 W w) = 1 := by
  rw [F2, L_mul, constantCoeff_thirdParam hw, linearCoeff_thirdParam hw,
    MvPowerSeries.constantCoeff_inv, dd_cc hw]
  norm_num

lemma wF_cc (hw : WFixed W w) : cc (wF W w) = 0 := by
  simp [wF, constantCoeff_thirdValue hw]

abbrev Sadj (W : WeierstrassCurve K) : Subalgebra ℤ K :=
  Algebra.adjoin ℤ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)

def T (W : WeierstrassCurve K) : Subring (MvPowerSeries (Fin 2) K) :=
  (MvPowerSeries.map (algebraMap (Sadj W) K)).range

lemma mem_T {φ : MvPowerSeries (Fin 2) K} : φ ∈ T W ↔ ∀ e, MvPowerSeries.coeff e φ ∈ Sadj W := by
  constructor
  · intro hφ e
    obtain ⟨p, rfl⟩ := RingHom.mem_range.mp hφ
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e p).2
  · intro h
    refine RingHom.mem_range.mpr ⟨fun e => ⟨MvPowerSeries.coeff e φ, h e⟩, ?_⟩
    ext e
    first
      | rfl
      | simp [MvPowerSeries.coeff_map]

lemma inv_mem_integralSeries {φ : MvPowerSeries (Fin 2) K} (h : φ ∈ T W) (h0 : cc φ ≠ 0)
    (hi : (cc φ)⁻¹ ∈ Sadj W) : φ⁻¹ ∈ T W := by
  classical
  rw [mem_T] at h ⊢
  have step : ∀ n : Fin 2 →₀ ℕ, (∀ m, m < n → MvPowerSeries.coeff m φ⁻¹ ∈ Sadj W) →
      MvPowerSeries.coeff n φ⁻¹ ∈ Sadj W := by
    intro n ih
    rw [MvPowerSeries.coeff_inv]
    split_ifs with hn
    · exact hi
    · refine mul_mem (neg_mem hi) (sum_mem fun x _ => ?_)
      split_ifs with hx
      · exact mul_mem (h _) (ih _ hx)
      · exact zero_mem _
  intro n
  first
    | exact (wellFounded_lt (α := Fin 2 →₀ ℕ)).induction n step
    | exact WellFoundedLT.induction n step
    | exact (wellFounded_lt (α := Fin 2 →₀ ℕ)).induction (C := fun n => MvPowerSeries.coeff n φ⁻¹ ∈ Sadj W) n step

lemma X_mem_T (i : Fin 2) : (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) ∈ T W := by
  rw [mem_T]
  intro e
  rw [MvPowerSeries.coeff_X]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

lemma constSeries_mem_integralSeries {a : K} (ha : a ∈ ({W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} : Set K)) : ca a ∈ T W := by
  rw [mem_T]
  intro e
  first
    | rw [MvPowerSeries.coeff_C]
    | rw [ca, MvPowerSeries.coeff_C]
  split_ifs
  · exact Algebra.subset_adjoin ha
  · exact zero_mem _

lemma slope_mem_integralSeries (hw : WFixed W w) : lam w ∈ T W := by
  rw [mem_T]
  intro e
  rw [coeff_lam]
  exact w_coeff_mem hw _

lemma wVar_mem_integralSeries (hw : WFixed W w) (i : Fin 2) : Wi w i ∈ T W := by
  rw [mem_T]
  intro e
  rw [coeff_Wi]
  split_ifs
  · exact w_coeff_mem hw _
  · exact zero_mem _

lemma intercept_mem_integralSeries (hw : WFixed W w) : nu w ∈ T W := by
  exact sub_mem (wVar_mem_integralSeries hw 0) (mul_mem (slope_mem_integralSeries hw) (X_mem_T 0))

lemma formalSum_mem_integralSeries (hw : WFixed W w) : F2 W w ∈ T W := by
  have h1 : ca W.a₁ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h2 : ca W.a₂ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h3 : ca W.a₃ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h4 : ca W.a₄ ∈ T W := constSeries_mem_integralSeries (by simp)
  have h6 : ca W.a₆ ∈ T W := constSeries_mem_integralSeries (by simp)
  have hl := slope_mem_integralSeries hw
  have hn := intercept_mem_integralSeries hw
  have hC3 : C3 W w ∈ T W := lineCoeffCubic_mem _ h2 h4 h6 hl
  have hC2 : C2 W w ∈ T W := lineCoeffQuadratic_mem _ h1 h2 h3 h4 h6 hl hn
  have hC3i : (C3 W w)⁻¹ ∈ T W :=
    inv_mem_integralSeries hC3 (by rw [constantCoeff_chordCoeffCubic hw]; exact one_ne_zero) (by rw [constantCoeff_chordCoeffCubic hw, inv_one]; exact Subalgebra.one_mem _)
  have hz3 : z3 W w ∈ T W :=
    (T W).sub_mem ((T W).sub_mem ((T W).neg_mem (X_mem_T 0)) (X_mem_T 1)) ((T W).mul_mem hC2 hC3i)
  have hw3 : w3 W w ∈ T W := (T W).add_mem ((T W).mul_mem hl hz3) hn
  have hdd : dd W w ∈ T W :=
    (T W).add_mem ((T W).add_mem ((T W).neg_mem (T W).one_mem) ((T W).mul_mem h1 hz3))
      ((T W).mul_mem h3 hw3)
  have hddi : (dd W w)⁻¹ ∈ T W :=
    inv_mem_integralSeries hdd (by rw [dd_cc hw]; exact neg_ne_zero.mpr one_ne_zero)
      (by rw [dd_cc hw, inv_neg, inv_one]; exact Subalgebra.neg_mem _ (Subalgebra.one_mem _))
  exact (T W).mul_mem hz3 hddi

lemma weq_iff (W : WeierstrassCurve K) (s v : MvPowerSeries (Fin 2) K) :
    WEqAt W s v ↔ G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) s v = 0 := by
  unfold Formalism.ELL.WEqAt G
  first
    | (simp only [MvPowerSeries.smul_eq_C_mul]
       rw [sub_eq_zero, eq_comm])
    | (simp only [Algebra.smul_def, MvPowerSeries.algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply]
       rw [sub_eq_zero, eq_comm])

lemma X_ne : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ MvPowerSeries.X 1 := by
  intro h
  have := congrArg (MvPowerSeries.coeff (Finsupp.single 0 1)) h
  rw [MvPowerSeries.coeff_X, MvPowerSeries.coeff_X, if_pos rfl, if_neg] at this
  · exact one_ne_zero this
  · intro h'
    exact absurd (Finsupp.single_left_injective one_ne_zero h') (by decide)

lemma ne_zero_of_L {φ : MvPowerSeries (Fin 2) K} {i : Fin 2} (h : (L i) φ ≠ 0) : φ ≠ 0 := by
  rintro rfl
  exact h (map_zero _)

lemma v_ne_of_G (W : WeierstrassCurve K) {z v : MvPowerSeries (Fin 2) K} (hz : z ≠ 0)
    (hG : G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄) (ca W.a₆) z v = 0) : v ≠ 0 := by
  rintro rfl
  rw [G_zero] at hG
  first
    | exact hz (pow_eq_zero_iff (by norm_num) |>.mp hG)
    | exact hz (pow_eq_zero hG)

lemma chord (hU : WSubstUnique.{u}) (hw : WFixed W w) :
    ChordAt W w (MvPowerSeries.X 0) (MvPowerSeries.X 1) (F2 W w) := by
  haveI hdom : IsDomain (MvPowerSeries (Fin 2) K) := by
    first
      | infer_instance
      | exact NoZeroDivisors.to_isDomain _
  have hι : Function.Injective (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) := IsFractionRing.injective _ _
  have hCa : ∀ a : K, (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.C a) = algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) a := fun a => by
    first
      | rfl
      | (rw [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))]; rfl)
      | simp [IsScalarTower.algebraMap_apply K (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))]
  have hE : ∀ s : MvPowerSeries (Fin 2) K, MvPowerSeries.constantCoeff s = 0 →
      G (ca W.a₁) (ca W.a₂) (ca W.a₃) (ca W.a₄)
        (ca W.a₆) s (w.subst s) = 0 :=
    fun s hs => (weq_iff W s _).mp (hU K W w hw (Fin 2) s hs).1
  have hG0 := hE (MvPowerSeries.X 0) (by simp)
  have hG1 := hE (MvPowerSeries.X 1) (by simp)
  have hv0 : lam w * MvPowerSeries.X 0 + nu w = Wi w 0 := by
    rw [nu]
    ring
  have hv1 : lam w * MvPowerSeries.X 1 + nu w = Wi w 1 := by
    rw [nu]
    linear_combination lam_mul w
  have hc0 : MvPowerSeries.constantCoeff (C3 W w) ≠ 0 := by
    rw [constantCoeff_chordCoeffCubic hw]
    exact one_ne_zero
  have hcinv : C3 W w * (C3 W w)⁻¹ = 1 := MvPowerSeries.mul_inv_cancel _ hc0
  have he1 : C3 W w * (MvPowerSeries.X 0 + MvPowerSeries.X 1 + Formalism.ELL.WeierstrassChordSeries.z3 W w)
      + C2 W w = 0 := by
    rw [Formalism.ELL.WeierstrassChordSeries.z3]
    linear_combination (-C2 W w) * hcinv
  obtain ⟨hG3, he2, he3⟩ := vieta (a1 := ca W.a₁) (a2 := ca W.a₂)
    (a3 := ca W.a₃) (a4 := ca W.a₄) (a6 := ca W.a₆) (l := lam w)
    (n := nu w) (z1 := MvPowerSeries.X 0) (z2 := MvPowerSeries.X 1) (z3 := Formalism.ELL.WeierstrassChordSeries.z3 W w)
    X_ne (by rw [hv0]; exact hG0) (by rw [hv1]; exact hG1) he1
  have hD0' : MvPowerSeries.constantCoeff (dd W w) ≠ 0 := by
    rw [dd_cc hw]
    norm_num
  have hDinv : (dd W w)⁻¹ * dd W w = 1 := MvPowerSeries.inv_mul_cancel _ hD0'
  have hD0 : dd W w ≠ 0 := fun h => hD0' (by rw [h, map_zero])
  have hfD : F2 W w * dd W w = Formalism.ELL.WeierstrassChordSeries.z3 W w := by
    rw [F2, mul_assoc, hDinv, mul_one]
  have huD : wF W w * dd W w = w3 W w := by
    rw [wF, mul_assoc, hDinv, mul_one]
  have hinv := G_inv (a1 := ca W.a₁) (a2 := ca W.a₂)
    (a3 := ca W.a₃) (a4 := ca W.a₄) (a6 := ca W.a₆)
    (z := Formalism.ELL.WeierstrassChordSeries.z3 W w) (v := w3 W w) (d := dd W w) hfD huD rfl hD0 hG3
  have hsub : wF W w = w.subst (F2 W w) :=
    (hU K W w hw (Fin 2) (F2 W w) (constantCoeff_formalSum hw)).2 _
      (wF_cc hw) ((weq_iff W _ _).mpr hinv)
  have hX0 : (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) ≠ 0 :=
    ne_zero_of_L (i := 0) (by rw [L_X]; simp)
  have hX1 : (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) ≠ 0 :=
    ne_zero_of_L (i := 1) (by rw [L_X]; simp)
  have hz3 : Formalism.ELL.WeierstrassChordSeries.z3 W w ≠ 0 :=
    ne_zero_of_L (i := 0) (by rw [linearCoeff_thirdParam hw]; norm_num)
  have hw0 : Wi w 0 ≠ 0 := v_ne_of_G W hX0 hG0
  have hw1 : Wi w 1 ≠ 0 := v_ne_of_G W hX1 hG1
  have hv3 : w3 W w ≠ 0 := v_ne_of_G W hz3 hG3
  have hc : C3 W w ≠ 0 := fun h => hc0 (by rw [h, map_zero])
  have key := chord_field (F := (FractionRing (MvPowerSeries (Fin 2) K))) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₁) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₂)
    (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₃) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₄) (algebraMap K (FractionRing (MvPowerSeries (Fin 2) K)) W.a₆)
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.X 0)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (MvPowerSeries.X 1)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Formalism.ELL.WeierstrassChordSeries.z3 W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Wi w 0)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (Wi w 1)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (w3 W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (lam w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (nu w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (F2 W w)) ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (wF W w))
    ((algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) (dd W w))
    (by rw [← hv0, map_add, map_mul]) (by rw [← hv1, map_add, map_mul]) (by rw [w3, map_add, map_mul])
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he1
      simpa [C3, C2, map_lineCoeffCubic, map_lineCoeffQuadratic, hCa,
        ca] using this)
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he2
      simpa [map_lineCoeffCubic, map_lineCoeffLinear, hCa, ca] using this)
    (by
      have := congrArg (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) he3
      simpa [map_lineCoeffCubic, map_lineCoeffConst, hCa, ca] using this)
    (by
      have := (map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hc
      simpa [C3, map_lineCoeffCubic, hCa, ca] using this)
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hw0) ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hw1)
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hv3) ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr (nu_ne hw))
    (hι.ne X_ne)
    (by
      rw [dd]
      simp [hCa, ca])
    ((map_ne_zero_iff (algebraMap (MvPowerSeries (Fin 2) K) (FractionRing (MvPowerSeries (Fin 2) K))) hι).mpr hD0)
    (by rw [← map_mul, hfD]) (by rw [← map_mul, huD])
  obtain ⟨hx, hy⟩ := key
  unfold Formalism.ELL.ChordAt Formalism.ELL.xOf Formalism.ELL.yOf
  rw [← hsub]
  first
    | exact ⟨hx, hy⟩
    | (refine ⟨?_, ?_⟩
       · convert hx using 1
       · convert hy using 1
         simp only [WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negY,
           WeierstrassCurve.Affine.negAddY, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₃]
         rfl)

end Mser

end WeierstrassChordSeries

open WeierstrassChordSeries in
theorem wChordSeries_of (hU : WSubstUnique.{u}) : WChordSeries.{u} := by
  intro K _ W w hw
  exact ⟨Formalism.ELL.WeierstrassChordSeries.F2 W w, Formalism.ELL.WeierstrassChordSeries.mem_T.mp (Formalism.ELL.WeierstrassChordSeries.formalSum_mem_integralSeries hw), Formalism.ELL.WeierstrassChordSeries.constantCoeff_formalSum hw,
    Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum hw 0, Formalism.ELL.WeierstrassChordSeries.linearCoeff_formalSum hw 1, Formalism.ELL.WeierstrassChordSeries.chord hU hw⟩
end Formalism.ELL
