import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulLeftInvariantVolGL

noncomputable section

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil
open scoped TensorProduct

namespace GlobalTheory.GodementJacquet

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def eMat (k : Type) [Field k] (r t : ℕ) : Matrix (Fin (r + t)) (Fin r) k :=
  Matrix.of fun i j => if (i : ℕ) = j then 1 else 0

def coef (σ : Representation ℂ (GL (Fin r) k) V) (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (v w : V)
    (g : GL (Fin r) k) : ℂ :=
  Bf (σ g⁻¹ v) w

def gjInt [MeasurableSpace (GL (Fin r) k)] (m : Measure (GL (Fin r) k)) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V)
    (Bf : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (Φ : Matrix (Fin (r + t)) (Fin r) k → ℂ)
    (h : GL (Fin (r + t)) k) (v w : V) : ℂ :=
  ∫ g, om μ g h Φ (eMat k r t) * coef σ Bf v w g ∂m

abbrev leviRep (t : ℕ) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) :
    Representation ℂ (Levi k (Two (Fin r) (Fin t))) (V ⊗[ℂ] ℂ) :=
  (extTensor σ (detRep (Fin t) μ)).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom

end GlobalTheory.GodementJacquet
