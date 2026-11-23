import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Letter

noncomputable section

open scoped MatrixGroups

namespace GlobalTheory.CyclotomicQExpansion

open GlobalTheory.KZ

section Ops

variable {R : Type*} [CommRing R]

def cm (c : ℚ → R) (φ : HahnSeries ℚ R) : HahnSeries ℚ R where
  coeff r := c r * φ.coeff r
  isPWO_support' := φ.isPWO_support.mono (fun r hr h => hr (by simp [h]))

def qD [Algebra ℚ R] (φ : HahnSeries ℚ R) : HahnSeries ℚ R := cm (fun r => algebraMap ℚ R r) φ

def scale (a : ℚ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R :=
  if h : 0 < a then HahnSeries.embDomain (OrderIso.mulLeft₀ a h).toOrderEmbedding φ else φ

def latPart (N : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R :=
  cm (fun r => if ((N : ℚ) * r).den = 1 then 1 else 0) φ

def uqN (N q : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R := latPart N (scale ((q : ℚ)⁻¹) φ)

def uq (q : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R := uqN 1 q φ

def vq (q : ℕ) (φ : HahnSeries ℚ R) : HahnSeries ℚ R := scale (q : ℚ) φ

def IsLat (N : ℕ) (φ : HahnSeries ℚ R) : Prop := ∀ r : ℚ, φ.coeff r ≠ 0 → ((N : ℚ) * r).den = 1

namespace Api

@[local simp] theorem coeff_cm (c : ℚ → R) (φ : HahnSeries ℚ R) (r : ℚ) : (cm c φ).coeff r = c r * φ.coeff r := rfl

theorem cm_add (c : ℚ → R) (φ ψ : HahnSeries ℚ R) : cm c (φ + ψ) = cm c φ + cm c ψ := by
  ext r; simp [mul_add]

theorem cm_smul (c : ℚ → R) (t : R) (φ : HahnSeries ℚ R) : cm c (t • φ) = t • cm c φ := by
  ext r; simp [mul_left_comm]

@[local simp] theorem coeff_qD [Algebra ℚ R] (φ : HahnSeries ℚ R) (r : ℚ) :
    (qD φ).coeff r = algebraMap ℚ R r * φ.coeff r := rfl

theorem coeff_scale_mul {a : ℚ} (ha : 0 < a) (φ : HahnSeries ℚ R) (r : ℚ) :
    (scale a φ).coeff (a * r) = φ.coeff r := by
  unfold scale
  rw [dif_pos ha]
  exact HahnSeries.embDomain_coeff (f := (OrderIso.mulLeft₀ a ha).toOrderEmbedding) (x := φ) (a := r)

theorem coeff_scale {a : ℚ} (ha : 0 < a) (φ : HahnSeries ℚ R) (r : ℚ) :
    (scale a φ).coeff r = φ.coeff (r / a) := by
  rw [← coeff_scale_mul ha φ (r / a), mul_div_cancel₀ _ ha.ne']

theorem scale_add (a : ℚ) (φ ψ : HahnSeries ℚ R) : scale a (φ + ψ) = scale a φ + scale a ψ := by
  by_cases ha : 0 < a
  · ext r; simp [coeff_scale ha]
  · simp [scale, ha]

theorem scale_smul (a : ℚ) (t : R) (φ : HahnSeries ℚ R) : scale a (t • φ) = t • scale a φ := by
  by_cases ha : 0 < a
  · ext r; simp [coeff_scale ha]
  · simp [scale, ha]

theorem scale_mul (a : ℚ) (φ ψ : HahnSeries ℚ R) : scale a (φ * ψ) = scale a φ * scale a ψ := by
  by_cases ha : 0 < a
  · simp only [scale, dif_pos ha]
    exact HahnSeries.embDomain_mul _ (fun x y => mul_add a x y) φ ψ
  · simp [scale, ha]

@[local simp] theorem scale_one (φ : HahnSeries ℚ R) : scale 1 φ = φ := by
  ext r; rw [coeff_scale one_pos, div_one]

theorem coeff_latPart (N : ℕ) (φ : HahnSeries ℚ R) (r : ℚ) :
    (latPart N φ).coeff r = if ((N : ℚ) * r).den = 1 then φ.coeff r else 0 := by
  simp [latPart]

theorem coeff_uqN (N : ℕ) {q : ℕ} (hq : 0 < q) (φ : HahnSeries ℚ R) (r : ℚ) :
    (uqN N q φ).coeff r = if ((N : ℚ) * r).den = 1 then φ.coeff (q * r) else 0 := by
  have h : (0 : ℚ) < (q : ℚ)⁻¹ := by positivity
  rw [uqN, coeff_latPart, coeff_scale h, div_inv_eq_mul, mul_comm r]

theorem coeff_uq {q : ℕ} (hq : 0 < q) (φ : HahnSeries ℚ R) (r : ℚ) :
    (uq q φ).coeff r = if r.den = 1 then φ.coeff (q * r) else 0 := by
  rw [uq, coeff_uqN 1 hq]; simp

theorem coeff_vq {q : ℕ} (hq : 0 < q) (φ : HahnSeries ℚ R) (r : ℚ) : (vq q φ).coeff r = φ.coeff (r / q) :=
  coeff_scale (by exact_mod_cast hq) φ r

end Api

end Ops

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

def sub (ε : Ω →+* ℂ) (a b d : ℚ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω :=
  scale (a / d) (cm (fun r => eOm ε (r * b / d)) φ)

def hq (ε : Ω →+* ℂ) (q : ℕ) (φ : HahnSeries ℚ Ω) : HahnSeries ℚ Ω :=
  ((q : Ω)⁻¹) • ∑ j ∈ Finset.range q, sub ε 1 (j : ℚ) (q : ℚ) φ

def dlogQ (X : Tower Ω ε) (f : X.K) : HahnSeries ℚ Ω := qD (X.exp f) * (X.exp f)⁻¹

namespace Api

attribute [local simp] coeff_cm coeff_qD

omit [Algebra ℚ Ω] in

theorem coeff_sub_upper {a d : ℚ} (h : 0 < a / d) (b : ℚ) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (sub ε a b d φ).coeff (r * a / d) = eOm ε (r * b / d) * φ.coeff r := by
  rw [sub, mul_div_assoc, mul_comm r, coeff_scale_mul h, coeff_cm]

omit [Algebra ℚ Ω] in

theorem sub_map_add (a b d : ℚ) (φ ψ : HahnSeries ℚ Ω) : sub ε a b d (φ + ψ) = sub ε a b d φ + sub ε a b d ψ := by
  simp only [sub, cm_add, scale_add]

omit [Algebra ℚ Ω] in

theorem sub_map_smul (a b d : ℚ) (t : Ω) (φ : HahnSeries ℚ Ω) : sub ε a b d (t • φ) = t • sub ε a b d φ := by
  simp only [sub, cm_smul, scale_smul]

theorem ent_div_pos (g : GQ) (hg : ent g 1 0 = 0) : 0 < ent g 0 0 / ent g 1 1 := by
  have h : 0 < ((g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).det := g.2
  rw [Matrix.det_fin_two] at h
  change 0 < ent g 0 0 * ent g 1 1 - ent g 0 1 * ent g 1 0 at h
  rw [hg, mul_zero, sub_zero] at h
  exact div_pos_iff.2 (mul_pos_iff.1 h)

theorem exp_sl_upper (X : Tower Ω ε) (g : GQ) (hg : ent g 1 0 = 0) (f : X.K) :
    X.exp (X.sl g f) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp f) := by
  have h := ent_div_pos g hg
  ext s
  obtain ⟨r, rfl⟩ : ∃ r, s = r * ent g 0 0 / ent g 1 1 :=
    ⟨s / (ent g 0 0 / ent g 1 1), by rw [mul_div_assoc, div_mul_cancel₀ _ h.ne']⟩
  rw [X.exp_upper g hg, coeff_sub_upper h]

omit [Algebra ℚ Ω] in

theorem eOm_eq_of {x : ℚ} {c : Ω} (h : ε c = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) : eOm ε x = c := by
  rw [eOm, ← h]; exact Function.leftInverse_invFun ε.injective c

omit [Algebra ℚ Ω] in

theorem eOm_intCast_div {q : ℕ} {ζ : Ω} (hζ : ε ζ = Complex.exp (2 * Real.pi * Complex.I / q)) (n : ℤ) :
    eOm ε ((n : ℚ) / q) = ζ ^ n := by
  apply eOm_eq_of
  rw [map_zpow₀, hζ, ← Complex.exp_int_mul]
  congr 1; push_cast; ring

omit [Algebra ℚ Ω] in

theorem exists_root_of_isAlgClosed [IsAlgClosed Ω] (ε : Ω →+* ℂ) {q : ℕ} (hq : 0 < q) :
    ∃ ζ : Ω, ε ζ = Complex.exp (2 * Real.pi * Complex.I / q) := by
  haveI : CharZero Ω := ε.charZero
  haveI : NeZero q := ⟨hq.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω q
  obtain ⟨i, -, hi⟩ := (hξ.map_of_injective ε.injective).eq_pow_of_pow_eq_one
    (Complex.isPrimitiveRoot_exp q hq.ne').pow_eq_one
  exact ⟨ξ ^ i, by rw [map_pow, hi]⟩

omit [Algebra ℚ Ω] in

theorem coeff_hq {q : ℕ} (hq0 : 0 < q) (φ : HahnSeries ℚ Ω) (r : ℚ) :
    (hq ε q φ).coeff r = (q : Ω)⁻¹ * (∑ j ∈ Finset.range q, eOm ε (r * j)) * φ.coeff (q * r) := by
  have h0 : (0 : ℚ) < q := by exact_mod_cast hq0
  rw [hq, HahnSeries.coeff_smul, HahnSeries.coeff_sum, smul_eq_mul, mul_assoc, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  have := coeff_sub_upper (ε := ε) (a := 1) (d := q) (by positivity) j φ (q * r)
  rw [show (q : ℚ) * r * 1 / q = r by field_simp, show (q : ℚ) * r * j / q = r * j by field_simp] at this
  exact this

omit [Algebra ℚ Ω] in

theorem hq_eq_uq {q : ℕ} (hq0 : 0 < q) (hζ : ∃ ζ : Ω, ε ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    {φ : HahnSeries ℚ Ω} (hφ : IsLat 1 φ) : hq ε q φ = uq q φ := by
  obtain ⟨ζ, hζ⟩ := hζ
  haveI : CharZero Ω := ε.charZero
  have h0 : (q : ℚ) ≠ 0 := by exact_mod_cast hq0.ne'
  have h1 : (q : Ω) ≠ 0 := by exact_mod_cast hq0.ne'
  have hp : IsPrimitiveRoot ζ q :=
    IsPrimitiveRoot.of_map_of_injective (f := ε) (hζ ▸ Complex.isPrimitiveRoot_exp q hq0.ne') ε.injective
  ext r
  rw [coeff_hq hq0, coeff_uq hq0]
  by_cases hc : φ.coeff (q * r) = 0
  · simp [hc]
  have hd := hφ _ hc
  rw [Nat.cast_one, one_mul] at hd
  obtain ⟨n, hn⟩ : ∃ n : ℤ, (q : ℚ) * r = n := ⟨_, (Rat.coe_int_num_of_den_eq_one hd).symm⟩
  have hr : r = n / q := by rw [← hn]; field_simp
  have he : ∀ j : ℕ, eOm ε (r * j) = (ζ ^ n) ^ j := fun j => by
    rw [← zpow_natCast, ← zpow_mul, ← eOm_intCast_div hζ, hr]; congr 1; push_cast; ring
  simp only [he]
  split_ifs with hr1
  · have : ζ ^ n = 1 := by
      rw [hp.zpow_eq_one_iff_dvd]
      refine ⟨r.num, ?_⟩
      have : (n : ℚ) = q * r.num := by rw [Rat.coe_int_num_of_den_eq_one hr1, hn]
      exact_mod_cast this
    simp [this, h1]
  · have hne : ζ ^ n ≠ 1 := by
      rw [Ne, hp.zpow_eq_one_iff_dvd]
      rintro ⟨m, rfl⟩
      apply hr1
      have : r = m := by rw [hr]; push_cast; field_simp
      rw [this, Rat.den_intCast]
    have hq1 : (ζ ^ n) ^ q = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hp.pow_eq_one, one_zpow]
    rw [geom_sum_eq hne, hq1]; simp

omit [Algebra ℚ Ω] in

theorem hq_eq_uq_of_isAlgClosed [IsAlgClosed Ω] {q : ℕ} (hq0 : 0 < q) {φ : HahnSeries ℚ Ω} (hφ : IsLat 1 φ) :
    hq ε q φ = uq q φ := hq_eq_uq hq0 (exists_root_of_isAlgClosed ε hq0) hφ

example : uq 2 (HahnSeries.single (1 : ℚ) (1 : ℤ)) = 0 := by
  ext r
  rw [coeff_uq two_pos, HahnSeries.coeff_zero]
  split_ifs with h
  · refine HahnSeries.coeff_single_of_ne fun h2 => ?_
    have : r = 1 / 2 := by push_cast at h2; linarith
    subst this; norm_num at h
  · rfl

example : (uq 2 (HahnSeries.single (6 : ℚ) (5 : ℤ))).coeff 3 = 5 := by
  rw [coeff_uq two_pos]; norm_num

example : (vq 2 (HahnSeries.single (3 : ℚ) (5 : ℤ))).coeff 6 = 5 := by
  rw [coeff_vq two_pos]; norm_num

example : (qD (HahnSeries.single (-1 / 2 : ℚ) (1 : ℚ))).coeff (-1 / 2) = -1 / 2 := by simp

example : (hq (Rat.castHom ℂ) 2 (HahnSeries.single (1 : ℚ) (1 : ℚ))).coeff (1 / 2) = 0 := by
  rw [hq_eq_uq two_pos ⟨-1, ?_⟩, coeff_uq two_pos]
  · norm_num
  · intro r hr
    have : r = 1 := by by_contra h; exact hr (HahnSeries.coeff_single_of_ne h)
    subst this; norm_num
  · rw [show (2 * Real.pi * Complex.I / ((2 : ℕ) : ℂ)) = Real.pi * Complex.I by push_cast; ring,
      Complex.exp_pi_mul_I]; simp

end Api

end GlobalTheory.CyclotomicQExpansion
