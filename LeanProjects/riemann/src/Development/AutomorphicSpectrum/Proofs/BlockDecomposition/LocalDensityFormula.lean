import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramIntegral

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open PositivityTheory.Rg.Base1 PositivityTheory.SiegelWeilFormula.Densx
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOne

theorem dens : Dens := by
  intro F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hσ hJ hli hlam hμ hF hmi hm S φ A hT
  obtain ⟨hφ, hφc, hφ0, hφU, hA, -⟩ := hT
  have : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨c1, c2, -, c4⟩ := GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral (Ainf F)
    (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hσ.1) hσ hJ b li hli.1 mi hmi φ hφ hφc hφ0 hφU
  have hv : ∀ v ∈ S, Continuous (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      HasCompactSupport (fun s : Fv F v => (m v (hermScal (Fv F v) σ s) (A v)).toReal) ∧
      ENNReal.ofReal (∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v)) =
        coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    exact GlobalTheory.CompanionTheory.SW.FibreCpt.masses_field (Fv F v) (GlobalTheory.T.completion_is_local_ring F v) hσ hJ b (lam v) (hlam v).1
      (m v) (hm v) (A v) (hA v hvS).1 (hA v hvS).2.1 (hA v hvS).2.2
  refine ⟨c1, c2, fun v hvS => ⟨continuous_const.mul (hv v hvS).1, (hv v hvS).2.1.mul_left⟩, ?_⟩
  have hI0 : 0 ≤ ∫ y, Gi mi φ y ∂li :=
    integral_nonneg fun s => integral_nonneg fun X => hφ0 X
  have hJ0 : ∀ v ∈ S, 0 ≤ ∫ s, gv m A v s ∂(lam v) := fun v _ =>
    integral_nonneg fun s => mul_nonneg (NNReal.coe_nonneg _) ENNReal.toReal_nonneg
  have hloc : ∀ v ∈ S, ENNReal.ofReal (∫ s, gv m A v s ∂(lam v)) =
      (cfac E v : ℝ≥0∞) * coordW (Fv F v) b (lam v) 1 1 (A v) := fun v hvS => by
    have e : ∫ s, gv m A v s ∂(lam v) =
        (cfac E v : ℝ) * ∫ s, (m v (hermScal (Fv F v) σ s) (A v)).toReal ∂(lam v) :=
      integral_const_mul _ _
    rw [e, ENNReal.ofReal_mul (NNReal.coe_nonneg _), ENNReal.ofReal_coe_nnreal, (hv v hvS).2.2]
  rw [ENNReal.ofReal_mul hI0, ENNReal.ofReal_prod_of_nonneg hJ0, Finset.prod_congr rfl hloc,
    Finset.prod_mul_distrib]
  have e0 : ENNReal.ofReal (∫ y, Gi mi φ y ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 1) := c4
  rw [e0, vol]
  ring

end GlobalTheory.CompanionTheory.SW.RankOne

end
