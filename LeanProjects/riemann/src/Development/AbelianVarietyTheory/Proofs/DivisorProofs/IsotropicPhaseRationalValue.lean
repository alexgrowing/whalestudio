import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqZeroOfMulRight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.IsoPhaseRat

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem trace_inclR (e : E) :
    Algebra.trace (AF F) (AE F E) (inclR (F := F) (AF F) e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  show Algebra.trace (AF F) (AF F ⊗[F] E) ((1 : AF F) ⊗ₜ[F] e) = _
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem phase_rat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (d d₁ : ℕ) (W : Spc F E d)
    (H' : Plane E d d₁) (w : Fin d₁ → E), ∀ γ ∈ ratU σ W.J, ∃ c : F,
      GlobalTheory.IsoPhase.phase σ W H' w γ = algebraMap F (AF F) c := by
  intro F E _ _ _ _ _ σ d d₁ W H' w γ hγ
  have hγi : γ⁻¹ ∈ ratU σ W.J := inv_mem hγ
  obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 hγi
  have hm : mat γ⁻¹ = incM F (g : Matrix (Fin d) (Fin d) E) := by
    ext i j
    show ((γ⁻¹ : UA σ W.J) : GL (Fin d) (AE F E)) i j = _
    rw [← hg]
    rfl
  refine ⟨-Algebra.trace F E (form σ W.J (H'.ι *ᵥ w) ((g : Matrix (Fin d) (Fin d) E) *ᵥ H'.y)), ?_⟩
  rw [GlobalTheory.IsoPhase.phase, hm, GlobalTheory.UnipMass.incM_mulVec_incV, GlobalTheory.UnipMass.hA_incV, trace_inclR, map_neg]

end GlobalTheory.IsoPhaseRat
