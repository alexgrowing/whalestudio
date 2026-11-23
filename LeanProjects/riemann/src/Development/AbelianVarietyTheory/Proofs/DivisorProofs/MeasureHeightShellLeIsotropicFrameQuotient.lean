import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ScalesBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureTranslateShellLeDivModulus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameUnipotentRadicalClosedFundDomainMassOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactLevelHeightScalesIsotropicFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCentreFlowWittFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCentreFlowConjScalesHaarIsotropicUnipotentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalIsotropicStabiliserSplitLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightSlabSubsetUnipotentLeviCompactStatement

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.ResLine GlobalTheory.ResidueEisenstein
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ResidueEisenstein

theorem measure_shell_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)) (h : GAd σ J → ℝ), DataJ σ J X Y L a h → ∀ (μ : Measure (GAd σ J)) (D : Set (GAd σ J)), μ.IsHaarMeasure → IsFundamentalDomain ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) D μ → ∃ B : ℝ≥0∞, B ≠ ⊤ ∧ ∀ j : ℕ, μ.restrict D {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) := by
  intro F E _ _ _ _ _ σ n J r X Y L a h hD μ D hμ hFD
  obtain ⟨b, hb⟩ := GlobalTheory.T.exists_leviCentreFlow_wittFrame F E σ n J r X Y hD.cm hD.herm hD.witt
  obtain ⟨-, hHt, hlaw⟩ := GlobalTheory.T.isCompact_level_height_scales_isotropicFrame F E σ n J r X Y L a h hD
  obtain ⟨-, ν, DN, hν, hDN, hone⟩ := unipRad_frame_closed_mass_one F E σ n J r X Y hD.cm hD.herm hD.witt
  have hmod := GlobalTheory.T.leviCentreFlow_conj_scales_haar_isotropicUnipotent F E σ n J r X Y hD.cm hD.herm hD.witt b hb ν hν
  obtain ⟨π, DM, hSL⟩ := GlobalTheory.T.rational_isotropicStabiliser_splitLattice F E σ n J r X Y hD.cm hD.herm hD.witt ν DN hν hDN hone
  obtain ⟨C, hC, hslab⟩ := GlobalTheory.T.heightSlab_subset_unipotent_levi_compact F E σ n J r X Y L a h hD b hb
  haveI : Countable (ratPts σ J) := inferInstance
  haveI : Countable ((ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤) : Subgroup (GAd σ J)) :=
    Function.Injective.countable (Subgroup.inclusion_injective
      (inf_le_left : ratPts σ J ⊓ GlobalTheory.StdPar.frameStab σ J X ⊤ ≤ ratPts σ J))
  obtain ⟨B, hB, hsh⟩ := GlobalTheory.ResLine.modulus_mul_measure_shell_le (GAd σ J) _ _ _ ν π DN DM hSL μ D hμ hFD C hC
  refine ⟨B, hB, fun j => ?_⟩
  have hS : MeasurableSet {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} :=
    (measurableSet_Ioc (a := Real.exp (-(j + 1 : ℝ))) (b := Real.exp (-(j : ℝ)))).preimage hHt.cont.measurable
  have key := hsh (b j) _ (fun m hm => hb.comm j m (Subgroup.mem_inf.mp hm).1) (hmod j) _ hS (fun x hx => by
    obtain ⟨β, hβ, e⟩ := hb.onX j
    have e2 : h (b j * x) = Real.exp j * h x := by rw [hlaw _ β hβ, e]
    have hp : 0 < Real.exp (j : ℝ) := Real.exp_pos _
    refine hslab _ ?_ ?_
    · rw [e2]
      have : Real.exp (-1) = Real.exp j * Real.exp (-(j + 1 : ℝ)) := by rw [← Real.exp_add]; congr 1; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.1.le hp.le
    · rw [e2]
      have : (1 : ℝ) = Real.exp j * Real.exp (-(j : ℝ)) := by rw [← Real.exp_add]; simp
      rw [this]
      exact mul_le_mul_of_nonneg_left hx.2 hp.le)
  rw [Measure.restrict_apply hS]
  have e1 : ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; simp
  calc _ = ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * (ENNReal.ofReal (Real.exp (-(((n : ℝ) - (r + 1)) * j))) * _) := by
        rw [← mul_assoc, e1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (((n : ℝ) - (r + 1)) * j)) * B := by gcongr
    _ = _ := mul_comm _ _

end GlobalTheory.ResidueEisenstein
