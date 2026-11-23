import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCtIntSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DisjointLineMid
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NeOfReNe
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeSmallMidJB

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def IsSwap {d d₁ e : ℕ} {J : Matrix (Fin d) (Fin d) E} (H' : Plane E d d₁) (H₂ : Plane E d₁ e) (w : UA σ J) : Prop :=
  w ∈ ratU σ J ∧ mat w *ᵥ incV F H'.x = incV F (H'.ι *ᵥ H₂.x) ∧ mat w *ᵥ incV F H'.y = incV F (H'.ι *ᵥ H₂.y) ∧
    mat w *ᵥ incV F (H'.ι *ᵥ H₂.x) = incV F H'.x ∧ mat w *ᵥ incV F (H'.ι *ᵥ H₂.y) = incV F H'.y ∧
    mat w * incM F (H'.ι * H₂.ι) = incM F (H'.ι * H₂.ι)

def IsShear {d d₁ e : ℕ} {J : Matrix (Fin d) (Fin d) E} (H' : Plane E d d₁) (H₂ : Plane E d₁ e)
    (nn : AE F E → UA σ J) : Prop :=
  ∀ c, mat (nn c) *ᵥ incV F H'.x = incV F H'.x ∧
    mat (nn c) *ᵥ incV F (H'.ι *ᵥ H₂.x) = incV F (H'.ι *ᵥ H₂.x) + c • incV F H'.x ∧
    mat (nn c) *ᵥ incV F (H'.ι *ᵥ H₂.y) = incV F (H'.ι *ᵥ H₂.y) ∧
    mat (nn c) *ᵥ incV F H'.y = incV F H'.y - cA σ c • incV F (H'.ι *ᵥ H₂.y) ∧
    mat (nn c) * incM F (H'.ι * H₂.ι) = incM F (H'.ι * H₂.ι)

end GlobalTheory.ConeSmallMidJB

end
