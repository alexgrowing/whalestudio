import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

namespace GlobalTheory.MassLink

theorem sqrt_d_pos' (D : D7) : 0 < Real.sqrt D.host.d :=
  Real.sqrt_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero D.host.hyp.2.1.ne_zero))

theorem tauE_injective' (D : D7) : Function.Injective (TH.tauE D) := fun _ _ h =>
  D.eTau.injective (Subtype.ext ((Formalism.BasicNotions.factEmb D.R D.host).1.1 h))

theorem conj_tauE_ne' (D : D7) (ρ ρ' : D.what₂.Tau) :
    ComplexEmbedding.conjugate (TH.tauE D ρ) ≠ TH.tauE D ρ' := by
  intro h
  have e := DFunLike.congr_fun h D.host.sqrtMinusD
  rw [ComplexEmbedding.conjugate_coe_eq, Formalism.L2.Theta.tauE_sqrtMinusD, Formalism.L2.Theta.tauE_sqrtMinusD] at e
  have e2 := congrArg Complex.im e
  simp at e2
  have := sqrt_d_pos' D
  linarith

theorem tauE_surj' (D : D7) (φ : D.host.E →+* ℂ)
    (h : φ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ)) : ∃ ρ, TH.tauE D ρ = φ := by
  obtain ⟨g, rfl⟩ := (Formalism.BasicNotions.factEmb D.R D.host).1.2 φ
  exact ⟨D.eTau.symm ⟨g, ((Formalism.BasicNotions.factEmb D.R D.host).2 g).1 h⟩, by unfold TH.tauE; rw [Equiv.apply_symm_apply]⟩

theorem tauE_or' (D : D7) (φ : D.host.E →+* ℂ) :
    ∃ ρ, TH.tauE D ρ = φ ∨ TH.tauE D ρ = ComplexEmbedding.conjugate φ := by
  have h0 : D.host.φ₀ D.host.sqrtMinusD = Complex.I * (Real.sqrt D.host.d : ℂ) := D.host.φ₀_mem
  have hs : D.host.sqrtMinusD * D.host.sqrtMinusD = -(D.host.d : D.host.E) := by
    apply D.host.φ₀.injective
    rw [map_mul, h0, map_neg, map_natCast, mul_mul_mul_comm, Complex.I_mul_I, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg _)]
    simp
  have h1 : φ D.host.sqrtMinusD * φ D.host.sqrtMinusD =
      (Complex.I * (Real.sqrt D.host.d : ℂ)) * (Complex.I * (Real.sqrt D.host.d : ℂ)) := by
    rw [← map_mul, hs, ← h0, ← map_mul, hs, map_neg, map_neg, map_natCast, map_natCast]
  rcases mul_self_eq_mul_self_iff.1 h1 with h | h
  · obtain ⟨ρ, e⟩ := tauE_surj' D φ h
    exact ⟨ρ, Or.inl e⟩
  · obtain ⟨ρ, e⟩ := tauE_surj' D (ComplexEmbedding.conjugate φ) (by
      rw [ComplexEmbedding.conjugate_coe_eq, h, map_neg, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring)
    exact ⟨ρ, Or.inr e⟩

open Classical in

theorem psi_cmType_equiv : ∀ D : D7, letI : IsCMField D.host.E := D.host.isCMField_hostE;
    (∀ τ : D.host.E →+* ℂ, τ ∈ GlobalTheory.MassLink.psi D ↔ ComplexEmbedding.conjugate τ ∉ GlobalTheory.MassLink.psi D) ∧
    ∃ eΨ : D.what₂.Tau ≃ GlobalTheory.MassLink.psi D, ∀ ρ, ((eΨ ρ : GlobalTheory.MassLink.psi D) : D.host.E →+* ℂ) = TH.tauE D ρ := by
  intro D
  have mem : ∀ φ : D.host.E →+* ℂ, φ ∈ psi D ↔ ∃ ρ, TH.tauE D ρ = φ := fun φ => by
    simp [psi]
  refine ⟨fun τ => ?_, ?_⟩
  · rw [mem, mem]
    constructor
    · rintro ⟨ρ, rfl⟩ ⟨ρ', h⟩
      exact conj_tauE_ne' D ρ ρ' h.symm
    · intro h
      obtain ⟨ρ, h1 | h1⟩ := tauE_or' D τ
      · exact ⟨ρ, h1⟩
      · exact absurd ⟨ρ, h1⟩ h
  · refine ⟨(Equiv.ofInjective _ (tauE_injective' D)).trans (Equiv.setCongr ?_), fun ρ => rfl⟩
    ext φ
    simp [psi]

end GlobalTheory.MassLink
