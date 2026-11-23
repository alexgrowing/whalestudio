import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsShear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryScalingVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryLeviLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterMultiplicativeStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConeRepresentatives
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatUOfForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallMidJB

namespace GlobalTheory.MidLineParam

theorem levi_one_mem_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ : ℕ)
    (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁),
    (∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + b • H'.y) →
    ∀ (h₁ : UA σ W₁.J) (h : UA σ W.J), IsLevi H' 1 h₁ h → h₁ ∈ ratU σ W₁.J → h ∈ ratU σ W.J := by
  intro F E _ _ _ _ _ σ d d₁ W W₁ H' hspan h₁ h hL hr
  obtain ⟨Q, hQ, -⟩ := rat_mulVec hr
  obtain ⟨hx, hy, hι⟩ := hL
  refine mem_ratU_of_mulVec h fun v => ?_
  obtain ⟨a, b, u, rfl⟩ := hspan v
  refine ⟨a • H'.x + H'.ι *ᵥ (Q *ᵥ u) + b • H'.y, ?_⟩
  have hx' : mat h *ᵥ incV F H'.x = incV F H'.x := by simpa using hx
  have hy' : mat h *ᵥ incV F H'.y = incV F H'.y := by simpa using hy
  have hu : mat h *ᵥ incV F (H'.ι *ᵥ u) = incV F (H'.ι *ᵥ (Q *ᵥ u)) := by
    rw [← incM_mulVec, ← incM_mulVec, ← hQ, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hι]
  rw [incV_add, incV_add, incV_add, incV_add, incV_smul, incV_smul, Matrix.mulVec_add, Matrix.mulVec_add,
    Matrix.mulVec_smul, Matrix.mulVec_smul, hx', hy', hu]

end GlobalTheory.MidLineParam
