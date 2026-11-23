import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviTorusElementCmStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdeleCharacterValueStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsElementAngleNontrivialStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK.LawSep

theorem lawSep : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ X om om', IsTriple B G X om om' →
      ∃ (t : (AE F E)ˣ) (m : UA σ G.W.J), IsLevi (W₁ := G₁.W) H' t 1 m ∧
        (X.α t : ℂ) * (((absE F E t : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) ≠ (X.β t : ℂ) * (((absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ) := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' hT
  have hcm := hT.base.cm
  obtain ⟨w₀⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hκ : 0 < B.mα w₀ - B.mβ w₀ := lt_of_le_of_lt (by positivity) (hT.geo.kappa w₀)
  obtain ⟨ξ, hξ0, hξ⟩ := GlobalTheory.T.exists_element_angle_nontrivial F E σ hcm (B.emb w₀).1 (B.mα w₀ - B.mβ w₀).toNat (by omega)
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_idele_character_value F E σ hcm B.emb w₀ ξ hξ0
  obtain ⟨m, hm⟩ := GlobalTheory.T.exists_levi_torus_element_cm F E σ B _ _ G.W G₁.W H' _ _ 0 (b + 1) hcm hT.geo.hW hC.hH' t
  refine ⟨t, m, hm, ?_⟩
  rw [ht _ _ hT.chars.expα, ht _ _ hT.chars.expβ]
  set u : ℂ := (B.emb w₀).1 ξ / (‖(B.emb w₀).1 ξ‖ : ℂ) with hu
  have hτ0 : (B.emb w₀).1 ξ ≠ 0 := (map_ne_zero _).2 hξ0
  have hu0 : u ≠ 0 := div_ne_zero hτ0 (by exact_mod_cast norm_ne_zero_iff.2 hτ0)
  have hun : ‖u‖ = 1 := by rw [hu, norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.2 hτ0)]
  have hA : 0 < (absE F E t : ℝ) := by
    have h1 : absE F E t * absE F E t⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
    have : absE F E t ≠ 0 := fun h => by simp [h] at h1
    exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 this)
  set P : ℝ := (absE F E t : ℝ) ^ ((a' : ℝ) / 2) with hP
  set Q : ℝ := (absE F E t : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) with hQ
  have hP0 : 0 < P := Real.rpow_pos_of_pos hA _
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hA _
  have hsplit : B.mα w₀ = B.mβ w₀ + ((B.mα w₀ - B.mβ w₀).toNat : ℤ) := by omega
  intro heq
  rw [hsplit, zpow_add₀ hu0, zpow_natCast, mul_assoc] at heq
  have h2 : u ^ (B.mα w₀ - B.mβ w₀).toNat * (P : ℂ) = (Q : ℂ) := mul_left_cancel₀ (zpow_ne_zero _ hu0) heq
  have h3 : ‖u ^ (B.mα w₀ - B.mβ w₀).toNat‖ = 1 := by rw [norm_pow, hun, one_pow]
  have h4 : P = Q := by
    have := congrArg norm h2
    rw [norm_mul, h3, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hP0.le, Real.norm_of_nonneg hQ0.le] at this
    exact this
  apply hξ
  rw [← h4] at h2
  exact mul_right_cancel₀ (by exact_mod_cast hP0.ne') (h2.trans (one_mul _).symm)

end GlobalTheory.ThK.LawSep
