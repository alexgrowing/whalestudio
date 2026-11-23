import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SameOffRefl
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInertStatement
import Formalism.LocalToGlobal.GlobalTheory.GL3.PLinkThIndep
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct

noncomputable section

namespace GlobalTheory.TwV.Xc

theorem ringHom_mem_qbar {A : Type} [Field A] [NumberField A] (f : A →+* ℂ) (x : A) : f x ∈ TaylorLogMetric.Qbar := by
  rw [mem_algebraicClosure_iff']
  exact (Algebra.IsIntegral.isIntegral (R := ℚ) x).map f.toRatAlgHom

theorem lamC_eq_of_mem {p : ℕ} [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) {s : ℂ} (hs : s ∈ TaylorLogMetric.Qbar) :
    TaylorLogMetric.lamC lam s = lam ⟨s, hs⟩ := by
  unfold TaylorLogMetric.lamC
  rw [dif_pos hs]

theorem chi_alg_unit_inert : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (χ : TaylorLogMetric.IdE D → ℂ),
    TaylorLogMetric.IsChi D χ → p ≠ 2 → GL3Theta.InertK D p → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 →
      χ 𝔞 ∈ TaylorLogMetric.Qbar ∧ χ 𝔞 ≠ 0 ∧ ‖TaylorLogMetric.lamC lam (χ 𝔞)‖ = 1 := by
  intro D p _ lam χ hχ hp2 hin 𝔞 ha
  letI := D.host.cmStar
  obtain ⟨k, hk, z, hz, hspan⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.pow_unitary D ha
  have hzu : z ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.star_conj]
    exact ⟨by rw [mul_comm]; exact hz, hz⟩
  set P : ℂ := ∏ τ : D.what₂.Tau, TaylorLogMetric.embT D τ z with hPdef
  have hpow : χ 𝔞 ^ k = P⁻¹ := by
    have h := hχ.2 ⟨z, hzu⟩
    simp only at h
    rw [← hspan, Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.CU.chi_pow D χ hχ ha k hk] at h
    rw [h, hPdef, Finset.prod_inv_distrib]
  have hz0 : z ≠ 0 := by
    rintro rfl; simp at hz
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.mpr fun τ _ => (map_ne_zero _).mpr hz0
  have hP : P ∈ TaylorLogMetric.Qbar := prod_mem fun τ _ => ringHom_mem_qbar _ z
  have hk0 : k ≠ 0 := by omega
  have halg : χ 𝔞 ∈ TaylorLogMetric.Qbar := by
    rw [mem_algebraicClosure_iff] at hP ⊢
    have h2 : IsAlgebraic ℚ (χ 𝔞 ^ k) := by rw [hpow]; exact hP.inv
    exact IsAlgebraic.of_pow (Nat.pos_of_ne_zero hk0) h2
  have hne : χ 𝔞 ≠ 0 := by
    intro h0
    rw [h0, zero_pow hk0] at hpow
    exact hP0 (inv_eq_zero.mp hpow.symm)
  refine ⟨halg, hne, ?_⟩
  have hnu := GlobalTheory.T.norm_prod_cmEmbeddings_eq_one_of_inert D p lam hp2 hin z hz
  rw [← hPdef, lamC_eq_of_mem lam hP] at hnu
  have hsub : (⟨χ 𝔞, halg⟩ : TaylorLogMetric.Qbar) ^ k = (⟨P, hP⟩ : TaylorLogMetric.Qbar)⁻¹ := by
    apply Subtype.ext
    simp [hpow]
  have e1 : ‖lam ⟨χ 𝔞, halg⟩‖ ^ k = 1 := by
    rw [← norm_pow, ← map_pow, hsub, map_inv₀, norm_inv, hnu, inv_one]
  rw [lamC_eq_of_mem lam halg]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hk0).mp e1

end GlobalTheory.TwV.Xc

end
