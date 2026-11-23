import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarFundamentalDomainUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentBoundedHeightReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarStabilizerPeriodCaseBThird
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

namespace GlobalTheory.UnipFDAdapted

theorem exists_fd_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s : ℕ),
    B.IsGood σ → W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∃ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure ∧
      IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ ∧ μ 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s hB hW hH
  obtain ⟨R, hR⟩ := GlobalTheory.UnipCompact.exists_bounded_translate F E σ B _ _ W W₁ H' _ _ _ _ hB hW hH
  refine GlobalTheory.UnipFD.main F E σ W H' ⟨Subtype.val ⁻¹' {g : UA σ W.J | ht g ≤ R},
    (GlobalTheory.UnipCT.isClosed_unip σ W H').isClosedEmbedding_subtypeVal.isCompact_preimage
      (GlobalTheory.ConeSmallSerInt.isCompact_ht_le R), fun u => ?_⟩
  obtain ⟨γ, hγ, hle⟩ := hR u.1 u.2
  exact ⟨⟨γ, hγ.2⟩, Subgroup.mem_subgroupOf.2 hγ.1, hle⟩

end GlobalTheory.UnipFDAdapted
