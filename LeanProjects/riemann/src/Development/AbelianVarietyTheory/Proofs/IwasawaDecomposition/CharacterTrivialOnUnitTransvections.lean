import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsometryConjTransvectionScaleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsotropicDualLatticeVectorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PowMemArithmeticSubgroupOfStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealUnitNotRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryStabilizerScalingIsotropicStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdUnitPowSubOneStatement

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem gl_pow_mulVec {E : Type} [Field E] {N : ℕ} (g : GL (Fin N) E) (ξ : Fin N → E) (ε : E)
    (h : (g : Matrix (Fin N) (Fin N) E).mulVec ξ = ε • ξ) (k : ℕ) :
    ((g ^ k : GL (Fin N) E) : Matrix (Fin N) (Fin N) E).mulVec ξ = ε ^ k • ξ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Units.val_mul, ← Matrix.mulVec_mulVec, h, Matrix.mulVec_smul, ih, smul_smul,
      pow_succ']

theorem killsScaled : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N),
    1 < Module.finrank ℚ E / 2 → ∀ (φ : X.Γ →* Multiplicative ℝ) (ξ : Fin N → E), ξ ∈ X.Λ → ξ ≠ 0 →
    herm X.Gm ξ ξ = 0 → ∃ u : 𝓞 E, u ≠ 0 ∧ cc (u : E) = u ∧ ∀ t : E, cc t = t → IsIntegral ℤ t →
    ∀ γ : X.Γ, ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) =
      transvMat X.Gm ξ (X.m * (u * t) * X.κ0) → φ γ = 1 := by
  intro E _ _ _ N X hdeg φ ξ hξ hξ0 hiso
  obtain ⟨η, d, hd, hη, hξη, hηη⟩ := GlobalTheory.T.exists_isotropic_dual_lattice_vector E N X ξ hξ hξ0 hiso
  obtain ⟨u0, hu0c, hu0⟩ := GlobalTheory.T.exists_real_unit_not_root_of_unity E hdeg
  have hM : ((d : 𝓞 E) * X.den) ≠ 0 :=
    mul_ne_zero (Nat.cast_ne_zero.2 hd.ne') X.den_ne
  obtain ⟨k1, hk1, c, hc⟩ := GlobalTheory.T.dvd_unit_pow_sub_one E u0 _ hM

  obtain ⟨v, hv⟩ : ∃ v : (𝓞 E)ˣ, v = u0 ^ k1 := ⟨_, rfl⟩
  rw [← hv] at hc
  obtain ⟨ε, hε⟩ : ∃ ε : E, ε = ((v : 𝓞 E) : E) := ⟨_, rfl⟩
  have hεpow : ε = ((u0 : 𝓞 E) : E) ^ k1 := by
    rw [hε, hv, Units.val_pow_eq_pow_val]; exact map_pow (algebraMap (𝓞 E) E) _ _
  have hεc : cc ε = ε := by rw [hεpow, cc_pow, hu0c]
  have hε0 : ε ≠ 0 := by
    rw [hε]; exact (v.isUnit.map (algebraMap (𝓞 E) E)).ne_zero
  have hεint : IsIntegral ℤ ε := by rw [hε]; exact RingOfIntegers.isIntegral_coe _
  have hεinv : IsIntegral ℤ ε⁻¹ := by
    have h1 : (((v⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) * ε = 1 := by
      have := congrArg (algebraMap (𝓞 E) E) (Units.inv_mul v)
      rw [map_mul, map_one] at this
      rw [hε]; exact this
    rw [← eq_inv_of_mul_eq_one_left h1]
    exact RingOfIntegers.isIntegral_coe _
  have hε1 : ε - 1 = d * X.den * c := by
    have := congrArg (algebraMap (𝓞 E) E) hc
    rw [map_sub, map_one, map_mul, map_mul, map_natCast] at this
    rw [hε]; exact this
  obtain ⟨g, hgU, hgξ⟩ :=
    GlobalTheory.T.exists_unitary_stabilizer_scaling_isotropic E N X ξ η d ε c hd hξ hη hiso hηη hξη hεc hε0 hεint hεinv hε1
  obtain ⟨k2, hk2, hmem⟩ := GlobalTheory.T.pow_mem_arithmetic_subgroup_of_stabilizer E N X g hgU
  have hgmξ := gl_pow_mulVec g ξ ε hgξ k2
  have hgiso : IsIsom X.Gm ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) :=
    (X.Γ_stab _ hmem).1
  obtain ⟨θ, hθ⟩ : ∃ θ : E, θ = ε ^ k2 := ⟨_, rfl⟩
  rw [← hθ] at hgmξ
  have hθc : cc θ = θ := by rw [hθ, cc_pow, hεc]
  have hθ0 : θ ≠ 0 := by rw [hθ]; exact pow_ne_zero _ hε0
  have hθint : IsIntegral ℤ (θ ^ 2) := by rw [hθ]; exact (hεint.pow _).pow _
  have hθ2 : θ ^ 2 ≠ 1 := by
    have := hu0 (k1 * k2 * 2) (by positivity)
    rwa [pow_mul, pow_mul, ← hεpow, ← hθ] at this

  have hucoe : ((((v : 𝓞 E) ^ k2) ^ 2 - 1 : 𝓞 E) : E) = θ ^ 2 - 1 := by
    rw [hθ, hε]
    simp only [map_sub, map_pow, map_one]
  refine ⟨((v : 𝓞 E) ^ k2) ^ 2 - 1, ?_, ?_, ?_⟩
  · intro h0
    apply hθ2
    have : θ ^ 2 - 1 = 0 := by rw [← hucoe, h0]; exact map_zero (algebraMap (𝓞 E) E)
    exact sub_eq_zero.1 this
  · rw [hucoe, cc_sub, cc_pow, hθc, cc_one]
  intro t ht hti γ hγ
  rw [hucoe] at hγ
  obtain ⟨a, ha, hav⟩ := X.transv ξ hξ hiso t ht hti
  have hθt : cc (θ ^ 2 * t) = θ ^ 2 * t := by rw [cc_mul, cc_pow, hθc, ht]
  obtain ⟨b, hb, hbv⟩ := X.transv ξ hξ hiso (θ ^ 2 * t) hθt (hθint.mul hti)
  have eq1 : (⟨g ^ k2, hmem⟩ : X.Γ) * ⟨a, ha⟩ = ⟨b, hb⟩ * ⟨g ^ k2, hmem⟩ := by
    apply Subtype.ext
    apply Units.ext
    show ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) * (a : Matrix (Fin N) (Fin N) E) =
      (b : Matrix (Fin N) (Fin N) E) * ((g ^ k2 : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
    rw [hav, hbv, GlobalTheory.T.isometry_conj_transvection_scale E N X.Gm _ ξ θ hgiso hgmξ hθc hθ0]
    congr 2
    ring
  have eq2 : φ ⟨a, ha⟩ = φ ⟨b, hb⟩ := by
    have := congrArg φ eq1
    rw [map_mul, map_mul, mul_comm] at this
    exact mul_right_cancel this
  have eq3 : (⟨b, hb⟩ : X.Γ) = ⟨a, ha⟩ * γ := by
    apply Subtype.ext
    apply Units.ext
    show (b : Matrix (Fin N) (Fin N) E) =
      (a : Matrix (Fin N) (Fin N) E) * ((γ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E)
    rw [hbv, hav, hγ, transvMat_mul_self X.Gm ξ hiso]
    congr 1
    ring
  have eq4 : φ ⟨a, ha⟩ * φ γ = φ ⟨a, ha⟩ := by rw [← map_mul, ← eq3, ← eq2]
  exact mul_eq_left.1 eq4

end GlobalTheory.UnipKill
