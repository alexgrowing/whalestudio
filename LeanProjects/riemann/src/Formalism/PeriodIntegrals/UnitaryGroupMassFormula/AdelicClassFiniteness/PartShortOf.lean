import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.HformSelfStar

noncomputable section

namespace PIW.AdelClassFin

open Formalism.UG NumberField
open scoped Matrix ComplexOrder

section Defs

variable {E : Type} [Field E] [NumberField E] [StarRing E]

def gramTr {m N : ℕ} (J : Matrix (Fin m) (Fin m) E) (e : Fin N → Fin m → E) : Matrix (Fin N) (Fin N) ℚ :=
  Matrix.of fun i j => Algebra.trace ℚ E (hform (starRingEnd E) J (e i) (e j))

def IsMajFam {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ) : Prop :=
  ∀ φ : E →+* ℂ, (H φ).PosDef ∧ (H φ).det = ((‖(J.map φ).det‖ : ℝ) : ℂ) ∧
    (∀ z : Fin m → ℂ, ‖star z ⬝ᵥ (J.map φ *ᵥ z)‖ ≤ (star z ⬝ᵥ (H φ *ᵥ z)).re) ∧
    H (ComplexEmbedding.conjugate φ) = (H φ).map (starRingEnd ℂ)

end Defs

def SvCodiffAt (E : Type) [Field E] [NumberField E] (δ : ℕ) : Prop :=
  ∀ y : E, (∀ a : 𝓞 E, Algebra.trace ℚ E (algebraMap (𝓞 E) E a * y) ∈ (algebraMap ℤ ℚ).range) →
    (δ : E) * y ∈ (algebraMap (𝓞 E) E).range

def SvCodiff : Prop :=
  ∀ (E : Type) [Field E] [NumberField E], ∃ δ : ℕ, 1 ≤ δ ∧ SvCodiffAt E δ

def SvMaj : Prop :=
  ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), J.IsHermitian → J.det ≠ 0 →
    ∃ H : Matrix (Fin n) (Fin n) ℂ, H.PosDef ∧ H.det = ((‖J.det‖ : ℝ) : ℂ) ∧
      ∀ z : Fin n → ℂ, ‖star z ⬝ᵥ (J *ᵥ z)‖ ≤ (star z ⬝ᵥ (H *ᵥ z)).re

def SvMajE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J → J.det ≠ 0 →
      ∃ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H

def SvBasis : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (m : ℕ) (M : Submodule (𝓞 E) (Fin m → E)),
    M.FG → Submodule.span E (M : Set (Fin m → E)) = ⊤ →
      ∃ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e ∧ (∀ i, e i ∈ M) ∧
        ∀ x ∈ M, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i

def SvGramDet : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ m d δ : ℕ, 1 ≤ d → 1 ≤ δ → SvCodiffAt E δ → ∀ p ∈ Lat E m d,
      ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, LinearIndependent ℚ e → (∀ i, e i ∈ p.2) →
        (∀ x ∈ p.2, ∃ c : Fin (m * Module.finrank ℚ E) → ℤ, x = ∑ i, (c i : E) • e i) →
          (gramTr p.1 e).det ≠ 0 ∧ |(gramTr p.1 e).det| ≤ ((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E)

def SvReal : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
    Formalism.BasicNotions.CMData F E → ∀ (m : ℕ) (J : Matrix (Fin m) (Fin m) E), IsHerm (starRingEnd E) J →
      ∀ H : (E →+* ℂ) → Matrix (Fin m) (Fin m) ℂ, IsMajFam J H →
        ∀ e : Fin (m * Module.finrank ℚ E) → Fin m → E, (gramTr J e).det ≠ 0 →
          ∃ R : Matrix (Fin (m * Module.finrank ℚ E)) (Fin (m * Module.finrank ℚ E)) ℝ,
            R.PosDef ∧ R.det = |((gramTr J e).det : ℝ)| ∧
              ∀ c : Fin (m * Module.finrank ℚ E) → ℤ,
                ∑ φ : E →+* ℂ, ‖φ (hform (starRingEnd E) J (∑ i, (c i : E) • e i) (∑ i, (c i : E) • e i))‖ ≤
                  (fun i => (c i : ℝ)) ⬝ᵥ (R *ᵥ fun i => (c i : ℝ))

theorem partShort_of (hM : PartMink) (hMaj : SvMajE) (hCod : SvCodiff) (hB : SvBasis)
    (hD : SvGramDet) (hR : SvReal) : PartShort := by
  intro F E _ _ _ _ _ _ hCM m d hm hd
  obtain ⟨δ, hδ1, hδ⟩ := hCod E
  have hn1 : 0 < Module.finrank ℚ E := Module.finrank_pos
  have hN1 : 1 ≤ m * Module.finrank ℚ E :=
    Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega))
  obtain ⟨Kc, hK⟩ := hM _ hN1
  set S : ℝ := max Kc 0 * ((d * δ : ℕ) : ℝ) with hS
  refine ⟨((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℚ), fun p hp => ?_⟩
  obtain ⟨hherm, hdet, hfg, hspan, -, -⟩ := id hp
  obtain ⟨H, hH⟩ := hMaj F E hCM m p.1 hherm hdet
  obtain ⟨e, hlin, hemem, hegen⟩ := hB E m p.2 hfg hspan
  obtain ⟨hgd, hgb⟩ := hD F E hCM m d δ hd hδ1 hδ p hp e hlin hemem hegen
  obtain ⟨R, hRpd, hRdet, hRle⟩ := hR F E hCM m p.1 hherm H hH e hgd
  obtain ⟨c, hc0, hcR⟩ := hK R hRpd
  set x : Fin m → E := ∑ i, (c i : E) • e i with hx
  have hxmem : x ∈ p.2 := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [Int.cast_smul_eq_zsmul E]
    exact p.2.toAddSubgroup.zsmul_mem (hemem i) (c i)
  have hx0 : x ≠ 0 := by
    intro h0
    apply hc0
    funext i
    have h0' : ∑ i, (c i : ℚ) • e i = 0 := by
      rw [← h0, hx]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Int.cast_smul_eq_zsmul ℚ, Int.cast_smul_eq_zsmul E]
    exact_mod_cast Fintype.linearIndependent_iff.1 hlin _ h0' i
  refine ⟨x, hxmem, hx0, ?_⟩
  set a := hform (starRingEnd E) p.1 x x with ha
  have hsumle : ∑ φ : E →+* ℂ, ‖φ a‖ ≤ S := by
    have h1 := hRle c
    have hdetR : R.det ≤ ((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E) := by
      rw [hRdet]
      have h' : ((|(gramTr p.1 e).det| : ℚ) : ℝ) ≤
          ((((d * δ : ℕ) : ℚ) ^ (m * Module.finrank ℚ E) : ℚ) : ℝ) := by exact_mod_cast hgb
      rw [Rat.cast_abs, Rat.cast_pow, Rat.cast_natCast] at h'
      exact h'
    have hR0 : 0 ≤ R.det := hRpd.det_pos.le
    have hroot : R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) ≤ ((d * δ : ℕ) : ℝ) := by
      calc R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ))
          ≤ (((d * δ : ℕ) : ℝ) ^ (m * Module.finrank ℚ E)) ^
              ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
            Real.rpow_le_rpow hR0 hdetR (by positivity)
        _ = ((d * δ : ℕ) : ℝ) := by
            rw [one_div]; exact Real.pow_rpow_inv_natCast (by positivity) (by omega)
    have hroot0 : 0 ≤ R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := Real.rpow_nonneg hR0 _
    calc ∑ φ : E →+* ℂ, ‖φ a‖ ≤ _ := h1
      _ ≤ Kc * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) := hcR
      _ ≤ max Kc 0 * R.det ^ ((1 : ℝ) / ((m * Module.finrank ℚ E : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hroot0
      _ ≤ S := mul_le_mul_of_nonneg_left hroot (le_max_right _ _)
  have hnorm : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ S ^ Module.finrank ℚ E := by
    have h2 := congrArg (‖·‖) (Algebra.norm_eq_prod_embeddings ℚ ℂ a)
    simp only [norm_prod] at h2
    rw [show ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ a)‖ = |((Algebra.norm ℚ a : ℚ) : ℝ)| by simp] at h2
    rw [Rat.cast_abs, h2]
    calc ∏ σ : E →ₐ[ℚ] ℂ, ‖σ a‖ ≤ ∏ σ : E →ₐ[ℚ] ℂ, S :=
          Finset.prod_le_prod (fun σ _ => norm_nonneg _) (fun σ _ =>
            (Finset.single_le_sum (f := fun φ : E →+* ℂ => ‖φ a‖) (fun φ _ => norm_nonneg _)
              (Finset.mem_univ (σ : E →+* ℂ))).trans hsumle)
      _ = S ^ Module.finrank ℚ E := by rw [Finset.prod_const, Finset.card_univ, AlgHom.card ℚ E ℂ]
  have hfin : ((|Algebra.norm ℚ a| : ℚ) : ℝ) ≤ ((⌈S ^ Module.finrank ℚ E⌉₊ : ℕ) : ℝ) :=
    hnorm.trans (Nat.le_ceil _)
  exact_mod_cast hfin

end PIW.AdelClassFin
