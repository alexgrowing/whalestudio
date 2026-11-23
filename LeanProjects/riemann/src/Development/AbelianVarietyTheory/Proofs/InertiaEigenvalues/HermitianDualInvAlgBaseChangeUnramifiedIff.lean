import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OverExtAlgebraMap
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfValNonneg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralTraceUnramifiedQuadraticLocalExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitTraceUnramifiedExtensionStatement

noncomputable section

namespace GlobalTheory.UnitLemma.Unr.Dual

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr

theorem val_mul (K : UQ) {x y : K.E} (hx : x ≠ 0) (hy : y ≠ 0) :
    val K.O (x * y) = val K.O x + val K.O y := by
  unfold val
  rw [map_mul, WithZero.log_mul (by simpa using hx) (by simpa using hy)]
  ring

theorem val_inv (K : UQ) (x : K.E) : val K.O x⁻¹ = - val K.O x := by
  unfold val
  rw [map_inv₀, WithZero.log_inv]

theorem deg_pos {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) : 0 < d := by
  rcases Nat.eq_zero_or_pos d with h | h
  · exfalso
    have h1 := K'.card_res
    rw [hU.1, h, pow_zero, one_pow] at h1
    have : 1 < Nat.card (IsLocalRing.ResidueField K'.O) := Finite.one_lt_card
    omega
  · exact h

theorem herm_eq_trace {K K' : UQ} {d : ℕ} {φ : K.E →+* K'.E} (hU : IsUnrExt K K' d φ) (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) :
    B.herm x y z = @Algebra.trace K.E K'.E _ _ φ.toAlgebra ((overExt φ B ψ hψ hσ).herm x y z) := by
  letI : Algebra K.E K'.E := φ.toAlgebra
  letI : Algebra K'.E B.A := ψ.toAlgebra
  haveI : IsScalarTower K.E K'.E B.A := IsScalarTower.of_algebraMap_eq fun e => (hψ e).symm
  haveI : Module.Finite K.E K'.E := Module.finite_of_finrank_pos
    (by rw [show Module.finrank K.E K'.E = d from hU.2.2.2.2]; exact deg_pos hU)
  haveI : Module.Finite K'.E B.A := Module.Finite.of_restrictScalars_finite K.E K'.E B.A
  show Algebra.trace K.E B.A (x * y * B.σ z) = Algebra.trace K.E K'.E (Algebra.trace K'.E B.A (x * y * B.σ z))
  exact (Algebra.trace_trace _).symm

theorem herm_smul {K K' : UQ} {φ : K.E →+* K'.E} (B : InvAlg K)
    (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e))
    (x y z : B.A) (m : K'.E) (y₀ : K'.O) (hcm : K'.c (algebraMap K'.O K'.E y₀) = m) :
    (overExt φ B ψ hψ hσ).herm x y (y₀ • (show (overExt φ B ψ hψ hσ).A from z)) =
      m * (overExt φ B ψ hψ hσ).herm x y z := by
  letI : Algebra K'.E B.A := ψ.toAlgebra
  have hs : B.σ (ψ (algebraMap K'.O K'.E y₀) * z) = ψ m * B.σ z := by
    rw [map_mul, hσ, hcm]
  show Algebra.trace K'.E B.A (x * y * B.σ (ψ (algebraMap K'.O K'.E y₀) * z)) =
    m * Algebra.trace K'.E B.A (x * y * B.σ z)
  rw [hs, show x * y * (ψ m * B.σ z) = m • (x * y * B.σ z) by
    rw [Algebra.smul_def]; show _ = ψ m * _; ring, LinearMap.map_smul, smul_eq_mul]

end GlobalTheory.UnitLemma.Unr.Dual

open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr GlobalTheory.UnitLemma.Unr.Dual in

theorem GlobalTheory.UnitLemma.Unr.dual_iff : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → ∀ (B : InvAlg K) (ψ : K'.E →+* B.A) (hψ : ∀ e, ψ (φ e) = algebraMap K.E B.A e) (hσ : ∀ e, B.σ (ψ e) = ψ (K'.c e)) (L : Submodule K'.O (overExt φ B ψ hψ hσ).A) (x y : B.A), (∀ z ∈ L, (overExt φ B ψ hψ hσ).herm x y z ∈ (algebraMap K'.O K'.E).range) ↔ (∀ z ∈ L, B.herm x y z ∈ (algebraMap K.O K.E).range) := by
  intro K K' d φ hU B ψ hψ hσ L x y
  letI : Algebra K.E K'.E := φ.toAlgebra
  have hT : ∀ z, B.herm x y z = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) :=
    fun z => herm_eq_trace hU B ψ hψ hσ x y z
  constructor
  · intro h z hz
    obtain ⟨b, hb⟩ := h z hz
    obtain ⟨a, ha⟩ := GlobalTheory.T.exists_integral_trace_unramifiedQuadraticLocalExt K K' d φ hU b
    refine ⟨a, ?_⟩
    calc algebraMap K.O K.E a = Algebra.trace K.E K'.E (algebraMap K'.O K'.E b) := ha.symm
      _ = Algebra.trace K.E K'.E ((overExt φ B ψ hψ hσ).herm x y z) := by rw [hb]
      _ = B.herm x y z := (hT z).symm
  · intro h z₀ hz₀
    by_contra hw
    have hv : val K'.O ((overExt φ B ψ hψ hσ).herm x y z₀) < 0 := by
      by_contra hle
      push_neg at hle
      obtain ⟨b, hb⟩ := mem_range_of_val_nonneg K' _ hle
      exact hw ⟨b, hb⟩
    have hw0 : (overExt φ B ψ hψ hσ).herm x y z₀ ≠ 0 := by
      intro h0
      exact hw ⟨0, by rw [h0, map_zero]⟩
    obtain ⟨u, a, ha, hua⟩ := GlobalTheory.T.exists_unit_trace_unramifiedInvolutionFieldExt K K' d φ hU
    obtain ⟨π, hπ⟩ := (IsDiscreteValuationRing.maximalIdeal K.O).valuation_exists_uniformizer K.E
    have hπv : val K.O π = 1 := by
      unfold val
      rw [hπ, WithZero.log_exp]
      norm_num
    have hπ0 : π ≠ 0 := by
      rintro rfl
      simp [val] at hπv
    have hφπ : φ π ≠ 0 := (map_ne_zero φ).2 hπ0
    set w := (overExt φ B ψ hψ hσ).herm x y z₀ with hwdef
    set m : K'.E := algebraMap K'.O K'.E u * w⁻¹ * (φ π)⁻¹ with hm
    have hm_int : 0 ≤ val K'.O m := by
      by_cases hu0 : algebraMap K'.O K'.E u = 0
      · rw [hm, hu0, zero_mul, zero_mul]
        simp [val]
      · rw [hm, val_mul K' (mul_ne_zero hu0 (inv_ne_zero hw0)) (inv_ne_zero hφπ),
          val_mul K' hu0 (inv_ne_zero hw0), val_inv, val_inv, hU.2.2.1, hπv]
        have := val_algebraMap_nonneg K' u
        omega
    obtain ⟨m₀, hm₀⟩ := mem_range_of_val_nonneg K' m hm_int
    obtain ⟨y₀, hy₀⟩ := K'.c_int m₀
    have hz₁ : y₀ • z₀ ∈ L := L.smul_mem y₀ hz₀
    have key : (overExt φ B ψ hψ hσ).herm x y (y₀ • z₀) = m * w :=
      herm_smul B ψ hψ hσ x y z₀ m y₀ (by rw [← hy₀, K'.c_c, hm₀])
    obtain ⟨b, hb⟩ := h _ hz₁
    have hb' := hb.trans (hT _)
    rw [key] at hb'
    have hmw : m * w = π⁻¹ • algebraMap K'.O K'.E u := by
      rw [Algebra.smul_def, hm]
      show _ = φ π⁻¹ * _
      rw [map_inv₀]
      field_simp
    rw [hmw, LinearMap.map_smul, hua, smul_eq_mul] at hb'
    have ha0 : algebraMap K.O K.E a ≠ 0 := by
      rw [Ne, ← map_zero (algebraMap K.O K.E), (IsFractionRing.injective K.O K.E).eq_iff]
      exact ha.ne_zero
    have h1 := val_algebraMap_nonneg K b
    rw [hb', val_mul K (inv_ne_zero hπ0) ha0, val_inv, hπv, GlobalTheory.UnitLemma.Orbit.val_unit a ha] at h1
    omega
