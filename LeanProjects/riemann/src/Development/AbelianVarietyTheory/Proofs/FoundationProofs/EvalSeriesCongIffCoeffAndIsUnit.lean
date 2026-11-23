import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsGaloisInvariantValuationIntegersEqIntegral
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResidueLinearDisjointnessCoeffLtOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElementsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamifiedDivisibilityOfUnramifiedDivisibilityStatement
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

noncomputable section

namespace GlobalTheory.Glue.EvInj

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

def zpHom (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] : ℤ_[p] →+* Ω :=
  (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp HahnSeries.C)

theorem zp_eq (z : ℤ_[p]) : zp Ω z = zpHom p Ω z := by
  simp [zp, zpHom, HahnSeries.C_apply]

theorem psi_C {T : GlobalTheory.K5.Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (z : ℤ_[p]) :
    ψ (algebraMap (Lau p) (O0 p) (HahnSeries.C z)) = zp Ω z := by
  have hpn : ((p : ℤ) ^ n) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [h.sub (HahnSeries.C z) (HahnSeries.C z), zp, HahnSeries.C_apply]
  · intro i
    by_cases hi : i = 0
    · simp [hi, HahnSeries.C_apply, HahnSeries.coeff_single]
    · have : (p : ℤ) ^ n * i ≠ 0 := mul_ne_zero hpn hi
      simp [hi, this, HahnSeries.C_apply, HahnSeries.coeff_single]
  · intro r hr
    have : r ≠ 0 := by rintro rfl; exact hr (dvd_zero _)
    simp [this, HahnSeries.C_apply, HahnSeries.coeff_single]

theorem psi_int {T : GlobalTheory.K5.Tower p Ω} {n : ℕ} {ψ : O0 p →+* Ω} (h : IsReb T n ψ) (y : O0 p) :
    IsInt p (ψ y) := by
  have hq : IsIntegral (O0 p) (T.qq n) := by
    refine IsIntegral.of_pow (pow_pos (Fact.out : p.Prime).pos n) ?_
    rw [GlobalTheory.K5.Basic.qq_pow]; exact isIntegral_algebraMap
  have hm : ψ y ∈ ψ.range := ⟨y, rfl⟩
  rw [h.rng, Subalgebra.mem_toSubring] at hm
  exact adjoin_le_integralClosure hq hm

theorem dvd_C_iff (k : ℕ) (z : ℤ_[p]) : (p : Lau p) ^ k ∣ HahnSeries.C z ↔ (p : ℤ_[p]) ^ k ∣ z := by
  rw [GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
  constructor
  · intro h; simpa [HahnSeries.C_apply, HahnSeries.coeff_single] using h 0
  · intro h m
    by_cases hm : m = 0
    · simpa [hm, HahnSeries.C_apply, HahnSeries.coeff_single] using h
    · simp [hm, HahnSeries.C_apply, HahnSeries.coeff_single]

section Val

variable (v : Valuation Ω ℝ≥0)

theorem cong_iff (hv : ∀ x, v x ≤ 1 ↔ IsInt p x) (hp0 : 0 < v (p : Ω)) (k : ℕ) (y : Ω) :
    Cong p k y 0 ↔ v y ≤ v (p : Ω) ^ k := by
  have hpk : (p : Ω) ^ k ≠ 0 := by
    intro h
    have := congrArg v h
    rw [map_pow, map_zero] at this
    exact (pow_pos hp0 k).ne' this
  constructor
  · rintro ⟨z, hz, e⟩
    rw [sub_zero] at e
    rw [e, map_mul, map_pow]
    exact mul_le_of_le_one_right zero_le' ((hv z).2 hz)
  · intro hy
    refine ⟨y / (p : Ω) ^ k, (hv _).1 ?_, by rw [sub_zero]; field_simp⟩
    rw [map_div₀, map_pow]
    exact div_le_one_of_le₀ hy zero_le'

def S (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (b : Fin F → Fin E → Lau p) : Ω :=
  ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * ψ (algebraMap (Lau p) (O0 p) (b j s))

theorem S_mul (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (m : ℕ) (b : Fin F → Fin E → Lau p) :
    S ψ π κ (fun j s => (p : Lau p) ^ m * b j s) = (p : Ω) ^ m * S ψ π κ b := by
  simp only [S, map_mul, map_pow, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun s _ => by ring

theorem S_le_one (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω) (hπ : v π ≤ 1) (hκ : ∀ j, v (κ j) ≤ 1)
    (hψ : ∀ y, v (ψ y) ≤ 1) (b : Fin F → Fin E → Lau p) : v (S ψ π κ b) ≤ 1 := by
  refine v.map_sum_le fun j _ => v.map_sum_le fun s _ => ?_
  rw [map_mul, map_mul, map_pow]
  exact mul_le_one' (mul_le_one' (hκ j) (pow_le_one' hπ _)) (hψ _)

theorem key_k (hp0 : 0 < v (p : Ω)) (hp1 : v (p : Ω) < 1) (ψ : O0 p →+* Ω) {E F : ℕ} (π : Ω) (κ : Fin F → Ω)
    (hπ : v π ≤ 1) (hκ : ∀ j, v (κ j) ≤ 1) (hψ : ∀ y, v (ψ y) ≤ 1)
    (K1 : ∀ b : Fin F → Fin E → Lau p, v (S ψ π κ b) ≤ v (p : Ω) → ∀ j s, (p : Lau p) ∣ b j s) :
    ∀ (k : ℕ) (b : Fin F → Fin E → Lau p), v (S ψ π κ b) ≤ v (p : Ω) ^ k ↔ ∀ j s, (p : Lau p) ^ k ∣ b j s := by
  intro k
  induction k with
  | zero => intro b; simpa using S_le_one v ψ π κ hπ hκ hψ b
  | succ k ih =>
    intro b
    constructor
    · intro h
      have h1 : ∀ j s, (p : Lau p) ∣ b j s :=
        K1 b (h.trans (pow_le_of_le_one zero_le' hp1.le (Nat.succ_ne_zero k)))
      choose b' hb' using h1
      have hb : b = fun j s => (p : Lau p) ^ 1 * b' j s := by
        funext j s; rw [pow_one]; exact hb' j s
      rw [hb, S_mul, map_mul, map_pow, pow_one, pow_succ'] at h
      have h2 : v (S ψ π κ b') ≤ v (p : Ω) ^ k := le_of_mul_le_mul_left h hp0
      intro j s
      rw [hb' j s, pow_succ']
      exact mul_dvd_mul_left _ ((ih b').1 h2 j s)
    · intro h
      choose b' hb' using h
      have hb : b = fun j s => (p : Lau p) ^ (k + 1) * b' j s := by
        funext j s; exact hb' j s
      rw [hb, S_mul, map_mul, map_pow]
      exact mul_le_of_le_one_right zero_le' (S_le_one v ψ π κ hπ hκ hψ b')

end Val

end GlobalTheory.Glue.EvInj

end

open GlobalTheory.Glue.EvInj in

theorem GlobalTheory.Glue.ev_cong_iff_and_unit : ∀ (p : ℕ) [Fact p.Prime], ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (n : ℕ), ∀ (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (k : ℕ) (c : ℤ → Ω) (x x' : Ω), Ev ψ c x x' → ((Cong p k x 0 ↔ ∀ r, Cong p k (c r) 0) ∧ ((∃ r, c r ≠ 0 ∧ IsInt p (c r)⁻¹) → x ≠ 0 ∧ IsInt p x⁻¹)) := by
  intro p _ Ω _ _ hC T n ψ hψ k c x x' hEv
  obtain ⟨v, hv, -, hp0, hp1⟩ := GlobalTheory.K5.exists_valuation_isInt p Ω hC
  obtain ⟨d, e, a, he, hc, hx, -⟩ := hEv
  have hψv : ∀ y, v (ψ y) ≤ 1 := fun y => (hv _).2 (psi_int hψ y)
  have hzp : ∀ z : ℤ_[p], v (zp Ω z) ≤ 1 := fun z => (hv _).2 (by rw [zp]; exact isIntegral_algebraMap)
  have hev : ∀ t, v (e t) ≤ 1 := fun t => (hv _).2 (he t).1
  have hcv : ∀ r, v (c r) ≤ 1 := fun r => by
    rw [hc r]; exact v.map_sum_le fun t _ => by rw [map_mul]; exact mul_le_one' (hev t) (hzp _)
  have hxv : v x ≤ 1 := by
    rw [hx]; exact v.map_sum_le fun t _ => by rw [map_mul]; exact mul_le_one' (hev t) (hψv _)
  refine ⟨?_, ?_⟩
  · obtain ⟨E, F, π, κ, lam, hE, -, hπE, hκ, hκu, hesp⟩ := GlobalTheory.T.exists_integral_basis_of_integral_algebraic_elements p Ω hC v hv hp0 hp1 d e he
    have hπ1 : v π < 1 := by
      by_contra h
      push_neg at h
      have h2 : 1 ≤ v π ^ E := one_le_pow₀ h
      rw [hπE] at h2
      exact absurd hp1 (not_lt.2 h2)
    have hκv : ∀ j, v (κ j) ≤ 1 := fun j => (hv _).2 (hκ j).1
    have LeviInductionForms : ∀ b : Fin F → Lau p, v (∑ j, κ j * ψ (algebraMap (Lau p) (O0 p) (b j))) < 1 →
        ∀ j, (p : Lau p) ∣ b j := by
      intro b hb j
      have hr := GlobalTheory.T.residue_linear_disjointness_coeff_lt_one p Ω hC v hv hp1 T n ψ hψ F κ b (fun j => hκ j) hb
      rw [← pow_one (p : Lau p), GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
      intro r
      by_contra hnd
      have h1 := hκu (fun j => (b j).coeff r) ⟨j, by simpa using hnd⟩
      have h2 := hr r
      rw [h1] at h2
      exact lt_irrefl _ h2
    have K1 := GlobalTheory.T.ramified_divisibility_of_unramified_divisibility p Ω v ψ E F π κ hE hp0 hp1 hπE hκv hψv LeviInductionForms
    have Kk := key_k v hp0 hp1 ψ π κ hπ1.le hκv hψv K1
    obtain ⟨B, hB⟩ : ∃ B : Fin F → Fin E → Lau p, ∀ j s, B j s = ∑ t, HahnSeries.C (lam t j s) * a t :=
      ⟨_, fun _ _ => rfl⟩
    have hx2 : x = S ψ π κ B := by
      simp only [S, hB, map_sum, map_mul, psi_C hψ, hx, hesp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by ring
    have hc2 : ∀ r, c r = S ψ π κ (fun j s => HahnSeries.C ((B j s).coeff r)) := by
      intro r
      simp only [S, psi_C hψ, hB, HahnSeries.coeff_sum, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul,
        smul_eq_mul, zp_eq, map_sum, map_mul, hc, hesp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => by
        rw [← HahnSeries.C_mul_eq_smul, map_mul, map_mul, psi_C hψ, psi_C hψ, zp_eq, zp_eq]
        ring
    rw [cong_iff v hv hp0, hx2, Kk]
    simp_rw [cong_iff v hv hp0, hc2, Kk, dvd_C_iff, GlobalTheory.K5.Basic.natCast_pow_dvd_iff]
    exact ⟨fun h r j s => h j s r, fun h j s r => h r j s⟩
  · rintro ⟨r, hr0, hri⟩
    have hcr : v (c r) = 1 := by
      refine le_antisymm (hcv r) ?_
      have h1 := (hv _).2 hri
      rw [map_inv₀] at h1
      have h0 : v (c r) ≠ 0 := (Valuation.ne_zero_iff v).2 hr0
      exact (inv_le_one₀ (pos_iff_ne_zero.2 h0)).1 h1
    have hx1 : v x = 1 := by
      refine le_antisymm hxv (not_lt.1 fun hlt => ?_)
      have h3 := GlobalTheory.T.residue_linear_disjointness_coeff_lt_one p Ω hC v hv hp1 T n ψ hψ d e a he (by rwa [← hx]) r
      rw [← hc r, hcr] at h3
      exact lt_irrefl _ h3
    have hx0 : x ≠ 0 := by
      intro h
      rw [h, map_zero] at hx1
      exact zero_ne_one hx1
    exact ⟨hx0, (hv _).1 (by rw [map_inv₀, hx1, inv_one])⟩
