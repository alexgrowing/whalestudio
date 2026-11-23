import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittFrameGLTwoDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasCentreLawZero
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.DescB.PlaneTwo GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.DescB.PlaneTwo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def IsTwoPlaneFrame {n n₁ n₂ : ℕ} (Y : Spc F E n) (H₁ : Plane E n n₁) (H₂ : Plane E n₁ n₂) (c : E) {r : ℕ} (h1 : 1 < r)
    (Xf Yf : Matrix (Fin n) (Fin r) E) : Prop :=
  IsWittFrame σ (c • Y.J.map σ) Xf Yf ∧ (fun k => Xf k ⟨0, by omega⟩) = H₁.x ∧ (fun k => Xf k ⟨1, h1⟩) = xTwo H₁ H₂ ∧
    (fun k => Yf k ⟨0, by omega⟩) = c⁻¹ • H₁.y ∧ (fun k => Yf k ⟨1, h1⟩) = c⁻¹ • yTwo H₁ H₂

end GlobalTheory.ThK.DescB.PlaneTwo

end
