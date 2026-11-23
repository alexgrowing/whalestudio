import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaDiagInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section
namespace GlobalTheory.ArchPull

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

def linM (D : Matrix κ ι F) :
    (ι → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) where
  toFun a := fun k => ∑ i, mixedEmbedding F (D k i) * a i
  map_add' a b := by funext k; simp [mul_add, Finset.sum_add_distrib]
  map_smul' c a := by funext k; simp [Finset.smul_sum, mul_smul_comm]

theorem linM_apply (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) (k : κ) :
    linM D a k = ∑ i, mixedEmbedding F (D k i) * a i := rfl

theorem linM_mul (L : Matrix ι κ F) (D : Matrix κ ι F) (a : ι → mixedEmbedding.mixedSpace F) :
    linM L (linM D a) = linM (L * D) a := by
  funext i
  simp only [linM_apply, Finset.mul_sum, Matrix.mul_apply, map_sum, Finset.sum_mul, map_mul, mul_assoc]
  exact Finset.sum_comm

theorem linM_one (a : ι → mixedEmbedding.mixedSpace F) : linM (1 : Matrix ι ι F) a = a := by
  funext i
  simp [linM_apply, Matrix.one_apply]

theorem exists_leftInv (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0) :
    ∃ L : Matrix ι κ F, L * D = 1 := by
  have hinj : Function.Injective (Matrix.toLin' D) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz; exact hD z (by simpa using hz)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' D)
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  rw [← LinearMap.toMatrix'_toLin' D, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end GlobalTheory.ArchPull

open GlobalTheory.ArchPull in
theorem GlobalTheory.ArchPull.exists_pull : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ,
      ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i) := by
  intro F _ _ ι κ _ _ D hD
  obtain ⟨L, hL⟩ := exists_leftInv D hD
  let M := LinearMap.toContinuousLinearMap (linM D)
  let N := LinearMap.toContinuousLinearMap (linM L)
  have hb : ∀ a, ‖a‖ ≤ ‖N‖₊ * ‖M a‖ := fun a => by
    have e : N (M a) = a := by
      change linM L (linM D a) = a
      rw [linM_mul, hL, linM_one]
    calc ‖a‖ = ‖N (M a)‖ := by rw [e]
      _ ≤ ‖N‖ * ‖M a‖ := N.le_opNorm _
      _ = _ := rfl
  have hl : AntilipschitzWith ‖N‖₊ M := ContinuousLinearMap.antilipschitz_of_bound M hb
  exact ⟨SchwartzMap.compCLMOfAntilipschitz ℂ M.hasTemperateGrowth hl, fun f a => rfl⟩
