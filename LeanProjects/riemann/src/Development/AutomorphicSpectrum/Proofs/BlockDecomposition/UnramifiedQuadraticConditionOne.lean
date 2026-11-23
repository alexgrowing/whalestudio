import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

noncomputable section

namespace GlobalTheory.CompanionTheory.ResidueInvolution

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigma_sigma {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

theorem sigR_tmul (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R) (e : E) :
    sigR R σ (a ⊗ₜ[F] e) = a ⊗ₜ[F] σ e := rfl

theorem sigR_sigR {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    sigR R σ (sigR R σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a e => rw [sigR_tmul, sigR_tmul, sigma_sigma h]
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem sigR_algebraMap (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (c : R) :
    sigR R σ (algebraMap R (R ⊗[F] E) c) = algebraMap R (R ⊗[F] E) c := by
  rw [Algebra.TensorProduct.algebraMap_apply, sigR_tmul]
  simp

theorem one_lt_absNorm (v : HeightOneSpectrum (𝓞 F)) : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  omega

theorem eq_zero_of_forall_pow {v : HeightOneSpectrum (𝓞 F)} {ϖ c : Fv F v} (h0 : ϖ ≠ 0) (h1 : ‖ϖ‖ < 1)
    (hc : ∀ j : ℕ, (ϖ⁻¹) ^ j * c ∈ v.adicCompletionIntegers F) : c = 0 := by
  by_contra hne
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hne) h1
  have h2 : ‖(ϖ⁻¹) ^ j * c‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 (hc j)
  rw [norm_mul, norm_pow, norm_inv, inv_pow] at h2
  have h3 : 0 < ‖ϖ‖ ^ j := pow_pos (norm_pos_iff.2 h0) j
  rw [inv_mul_le_iff₀ h3, mul_one] at h2
  exact absurd hj (not_lt.2 h2)

theorem q1 : PositivityTheory.SiegelWeilFormula.Gunr.Q1 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hH hϖ
  obtain ⟨hσ, -, hcar, hsig, h0, h1, -, -⟩ := hH
  refine ⟨fun a => Subtype.ext ?_, Subtype.ext ?_, ?_, ?_, one_lt_absNorm v⟩
  · rw [hsig, hsig, sigR_sigR hσ]
  · rw [hsig, sigR_algebraMap]
  · intro x y hxy
    have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (x : Fv F v ⊗[F] E) =
        algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (y : Fv F v ⊗[F] E) := congrArg Subtype.val hxy
    rw [← Algebra.smul_def, ← Algebra.smul_def] at e
    exact Subtype.ext (smul_right_injective _ h0 e)
  · intro hu
    obtain ⟨b, hb⟩ := hu.exists_right_inv
    have hb1 : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ * (b : Fv F v ⊗[F] E) = 1 := congrArg Subtype.val hb
    have hb2 : (b : Fv F v ⊗[F] E) = algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ := by
      have e : algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
          algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = 1 := by
        rw [← map_mul, inv_mul_cancel₀ h0, map_one]
      calc (b : Fv F v ⊗[F] E)
          = (algebraMap (Fv F v) (Fv F v ⊗[F] E) (ϖ : Fv F v)⁻¹ *
              algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ) * (b : Fv F v ⊗[F] E) := by rw [e, one_mul]
        _ = _ := by rw [mul_assoc, hb1, mul_one]
    have hc : ∀ k, (Algebra.TensorProduct.basis (Fv F v) bs).repr 1 k = 0 := fun k => by
      refine eq_zero_of_forall_pow h0 h1 fun j => ?_
      have hm : ((b ^ j : S) : Fv F v ⊗[F] E) ∈ Rv bs v := by
        rw [← hcar]
        exact (b ^ j).2
      have e : ((b ^ j : S) : Fv F v ⊗[F] E) = ((ϖ : Fv F v)⁻¹ ^ j) • (1 : Fv F v ⊗[F] E) := by
        rw [Subring.coe_pow, hb2, ← map_pow, Algebra.algebraMap_eq_smul_one]
      have := hm k
      rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul] at this
      exact this
    have h10 : (1 : Fv F v ⊗[F] E) = 0 :=
      (Algebra.TensorProduct.basis (Fv F v) bs).repr.map_eq_zero_iff.1 (Finsupp.ext hc)
    exact one_ne_zero h10

end GlobalTheory.CompanionTheory.ResidueInvolution

end
