import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

namespace GlobalTheory.ThK.DblKer.RatPair

theorem blk_mem_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (W : Spc F E n) (W₂ : Spc F E (n + n)), W₂.J = dblGram finSumFinEquiv W.J →
    ∀ i : UA σ W.J × UA σ W.J →* UA σ W₂.J, (∀ h h', mat (i (h, h')) = blkMat finSumFinEquiv (mat h) (mat h')) →
    ∀ γ ∈ ratU σ W.J, ∀ γ' ∈ ratU σ W.J, i (γ, γ') ∈ ratU σ W₂.J := by
  intro F E _ _ _ _ _ σ n W W₂ _ i hi γ hγ γ' hγ'
  rw [ratU, Subgroup.mem_subgroupOf] at hγ hγ' ⊢
  obtain ⟨A, hA⟩ := hγ
  obtain ⟨A', hA'⟩ := hγ'
  refine ⟨blkGL finSumFinEquiv (A, A'), Units.ext ?_⟩
  change (blkMat finSumFinEquiv A.1 A'.1).map _ = mat (i (γ, γ'))
  rw [hi, blkMat_map _ _ (map_zero _)]
  have h1 : (A.1).map (inclR (F := F) (E := E) (AF F)) = mat γ := congrArg Units.val hA
  have h2 : (A'.1).map (inclR (F := F) (E := E) (AF F)) = mat γ' := congrArg Units.val hA'
  rw [h1, h2]

end GlobalTheory.ThK.DblKer.RatPair
