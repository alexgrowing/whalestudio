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

noncomputable section

namespace GlobalTheory.RationalShear

open GlobalTheory.MidLineParam

theorem shear_mem_ratU : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d d₁ e : ℕ)
    (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (H₂ : Plane E d₁ e),
    (∀ v : Fin d → E, ∃ (a b : E) (u : Fin d₁ → E), v = a • H'.x + H'.ι *ᵥ u + b • H'.y) →
    (∀ v : Fin d₁ → E, ∃ (a b : E) (u : Fin e → E), v = a • H₂.x + H₂.ι *ᵥ u + b • H₂.y) →
    ∀ nn : AE F E → UA σ J, IsShear H' H₂ nn → ∀ c : E, nn (inclR (F := F) (AF F) c) ∈ ratU σ J := by
  intro F E _ _ _ _ _ σ d d₁ e J H' H₂ h1 h2 nn hn c
  obtain ⟨hx, hx2, hy2, hy, hι⟩ := hn (inclR (F := F) (AF F) c)
  refine mem_ratU_of_mulVec _ fun v => ?_
  obtain ⟨a, b, u, rfl⟩ := h1 v
  obtain ⟨a', b', u', rfl⟩ := h2 u
  have hc : cA σ (inclR (F := F) (AF F) c) = inclR (F := F) (AF F) (σ c) := GlobalTheory.PlaneLevi.cA_inclR σ c
  have hu : mat (nn (inclR (F := F) (AF F) c)) *ᵥ incV F (H'.ι *ᵥ (H₂.ι *ᵥ u')) = incV F (H'.ι *ᵥ (H₂.ι *ᵥ u')) := by
    rw [Matrix.mulVec_mulVec, ← incM_mulVec, Matrix.mulVec_mulVec, hι]
  refine ⟨a • H'.x + (a' • (H'.ι *ᵥ H₂.x + c • H'.x) + H'.ι *ᵥ (H₂.ι *ᵥ u') + b' • (H'.ι *ᵥ H₂.y))
    + b • (H'.y - σ c • (H'.ι *ᵥ H₂.y)), ?_⟩
  rw [Matrix.mulVec_add H'.ι, Matrix.mulVec_add H'.ι, Matrix.mulVec_smul H'.ι, Matrix.mulVec_smul H'.ι]
  simp only [incV_add, incV_sub, incV_smul]
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [hx, hx2, hy2, hy, hu, hc]

end GlobalTheory.RationalShear

end
