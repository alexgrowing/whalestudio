import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerExpSlashUpperTriangularEqSubstStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubstUpperTriangularHahnMulAndOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HahnSeriesQDerivativeSubstUpperTriangularStatement

noncomputable section

open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.DlUp

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem sub_coeff (ε : Ω →+* ℂ) {a b d : ℚ} (h : 0 < a / d) (φ : HahnSeries ℚ Ω) (s : ℚ) :
    (sub ε a b d φ).coeff s = eOm ε ((a / d)⁻¹ * s * b / d) * φ.coeff ((a / d)⁻¹ * s) := by
  have hs : s = (OrderIso.mulLeft₀ (a / d) h).toOrderEmbedding ((a / d)⁻¹ * s) := by
    show s = (a / d) * ((a / d)⁻¹ * s)
    rw [mul_inv_cancel_left₀ h.ne']
  unfold sub scale
  rw [dif_pos h]
  conv_lhs => rw [hs]
  rw [HahnSeries.embDomain_coeff]
  rfl

theorem theta_one (φ : HahnSeries ℚ Ω) : theta 1 φ = qD φ := by
  ext r
  simp [theta, qD, cm]

theorem mem_of_pow_eq_one (A : ValuationSubring Ω) {y : Ω} {k : ℕ} (hk : k ≠ 0) (hy : y ^ k = 1) : y ∈ A := by
  rw [← A.valuation_le_one_iff]
  by_contra hlt
  push_neg at hlt
  have h := one_lt_pow' hlt hk
  rw [← map_pow, hy, map_one] at h
  exact lt_irrefl _ h

theorem eOm_pow [IsAlgClosed Ω] (ε : Ω →+* ℂ) (x : ℚ) : eOm ε x ^ x.den = 1 := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  have hy : Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ x.den = 1 := by
    rw [← Complex.exp_nat_mul]
    have h' : (x : ℂ) * x.den = x.num := by exact_mod_cast Rat.mul_den_eq_num x
    have : (x.den : ℂ) * (2 * Real.pi * Complex.I * (x : ℂ)) = ((x.num : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      linear_combination (2 * Real.pi * Complex.I) * h'
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  haveI : NeZero x.den := ⟨x.den_nz⟩
  haveI : NeZero (x.den : Ω) := ⟨Nat.cast_ne_zero.2 x.den_nz⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic x.den Ω)
    (ne_of_gt (Polynomial.degree_cyclotomic_pos x.den Ω x.den_pos))
  have hζ : IsPrimitiveRoot z x.den := Polynomial.isRoot_cyclotomic_iff.1 hz
  have hεζ : IsPrimitiveRoot (ε z) x.den := hζ.map_of_injective ε.injective
  obtain ⟨i, -, hi⟩ := hεζ.eq_pow_of_pow_eq_one hy
  have hrange : ∃ w, ε w = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := ⟨z ^ i, by rw [map_pow, hi]⟩
  have hε : ε (eOm ε x) = Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) := Function.invFun_eq hrange
  apply ε.injective
  rw [map_pow, hε, hy, map_one]

theorem eOm_unit [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) (x : ℚ) :
    eOm ε x ≠ 0 ∧ eOm ε x ∈ A ∧ (eOm ε x)⁻¹ ∈ A := by
  have h := eOm_pow ε x
  refine ⟨fun h0 => ?_, mem_of_pow_eq_one A x.den_nz h, mem_of_pow_eq_one A x.den_nz (by rw [inv_pow, h, inv_one])⟩
  rw [h0, zero_pow x.den_nz] at h
  exact zero_ne_one h

theorem prim_sub [IsAlgClosed Ω] (ε : Ω →+* ℂ) (A : ValuationSubring Ω) {a b d : ℚ} (h : 0 < a / d)
    {ψ : HahnSeries ℚ Ω} (hψ : Prim A ψ) : Prim A (sub ε a b d ψ) := by
  obtain ⟨h1, r, hr0, hr⟩ := hψ
  refine ⟨fun s => ?_, (a / d) * r, ?_, ?_⟩
  · rw [sub_coeff ε h]; exact mul_mem (eOm_unit ε A _).2.1 (h1 _)
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne']; exact mul_ne_zero (eOm_unit ε A _).1 hr0
  · rw [sub_coeff ε h, inv_mul_cancel_left₀ h.ne', mul_inv]; exact mul_mem (eOm_unit ε A _).2.2 hr

theorem isDl_sl_upper : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n : ℕ) (g : GQ), ent g 1 0 = 0 → 0 < ent g 0 0 → 0 < ent g 1 1 → algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) ∈ A →
  ∀ (f : X.K) (φ : HahnSeries ℚ Ω), IsDl X A l n 1 f φ →
    IsDl X A l n 1 (X.sl g f) (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ) := by
  intro Ω _ _ _ ε X A N l _ n g h10 ha hd hc f φ hdl
  obtain ⟨hφ, a₀, b₀, κ, hκ, hfb, hPa, hPb, hcg⟩ := hdl
  have hpos : 0 < ent g 0 0 / ent g 1 1 := div_pos ha hd
  have hexp : ∀ u, X.exp (X.sl g u) = sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp u) :=
    fun u => GlobalTheory.T.tower_exp_slash_upperTriangular_eq_subst Ω ε X g h10 u
  have hmul := GlobalTheory.T.substUpperTriangularHahn_mul_and_one Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hqd := GlobalTheory.T.hahnSeriesQDerivative_substUpperTriangular Ω ε (ent g 0 0) (ent g 0 1) (ent g 1 1) hpos
  have hco := sub_coeff ε (b := ent g 0 1) hpos
  have hss : ∀ ψ χ : HahnSeries ℚ Ω, sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (ψ - χ) =
      sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) ψ - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) χ := by
    intro ψ χ; ext s; simp [hco, mul_sub]
  simp only [theta_one] at hcg
  refine ⟨?_, X.sl g a₀, X.sl g b₀, κ, hκ, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, hco, smul_eq_mul]
    exact mul_mem hc (mul_mem (eOm_unit ε A _).2.1 (hφ _))
  · rw [← map_mul, hfb, map_mul, AlgEquiv.commutes]
  · rw [hexp]; exact prim_sub ε A hpos hPa
  · rw [hexp]; exact prim_sub ε A hpos hPb
  · intro s
    simp only [theta_one]
    rw [hexp, hexp, hqd, hqd]
    have e1 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) φ *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (φ * X.exp a₀ * X.exp b₀) := by
      rw [(hmul _ _).1, (hmul _ _).1]; ring
    have e2 : HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀)) *
        sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp b₀) - sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (X.exp a₀) *
        (HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) * sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp b₀))) =
        HahnSeries.C (algebraMap ℚ Ω (ent g 0 0 / ent g 1 1)) *
          sub ε (ent g 0 0) (ent g 0 1) (ent g 1 1) (qD (X.exp a₀) * X.exp b₀ - X.exp a₀ * qD (X.exp b₀)) := by
      rw [hss, (hmul _ _).1, (hmul _ _).1]; ring
    rw [e1, e2]
    obtain ⟨z, hz, hzeq⟩ := hcg ((ent g 0 0 / ent g 1 1)⁻¹ * s)
    refine ⟨algebraMap ℚ Ω (ent g 0 0 / ent g 1 1) *
      eOm ε ((ent g 0 0 / ent g 1 1)⁻¹ * s * ent g 0 1 / ent g 1 1) * z,
      mul_mem (mul_mem hc (eOm_unit ε A _).2.1) hz, ?_⟩
    rw [HahnSeries.C_mul_eq_smul, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, HahnSeries.coeff_smul, hco, hco,
      smul_eq_mul, smul_eq_mul, ← mul_sub, ← mul_sub, hzeq]
    ring

end GlobalTheory.DlUp
