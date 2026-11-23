import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryRootExchangeMirrorIdentity
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BesselDatumAuxiliaryVectorOrthogonalImage
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.BesselData GlobalTheory.RootExch
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRootExchange_mirror_identity : ∀ (D : D7) (A B : HSp D) (ι : A.V →ₗ[D.host.E] B.V) (d : BesselDatum A B ι) (ψ : AddChar (AF D.host.F) ℂ) (ε : AE D), IsSplitIdem D ε → ∀ (j : Fin d.ρ) (t₀ t : Fin A.rank → AE D) (b₀ k : GA D B), ε • t₀ = t₀ → cA D ε • t = t → IsK B (vecA B (dual d j.succ)) (iA ι t₀) b₀ → IsK B (vecA B (d.e j)) (iA ι t) k → SuppAt ε B k ∧ ∀ b ∈ ExGe d ε (j.1 + 2), b * (b₀ * k * b₀⁻¹) * b⁻¹ ∈ d.N ∧ SuppAt ε B (b * (b₀ * k * b₀⁻¹) * b⁻¹) ∧ d.psiN ψ (b * (b₀ * k * b₀⁻¹) * b⁻¹) = ψ (Algebra.trace (AF D.host.F) (AE D) (incA D d.θ * hA A t₀ t)) := by
  first | exact @GlobalTheory.RootExch.Mirror.mirror | exact GlobalTheory.RootExch.Mirror.mirror | (intros; apply GlobalTheory.RootExch.Mirror.mirror <;> assumption)
