import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MapRestrictLatticeStabiliserMeasureEqCompactDual
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InfiniteCoordinateUnfold
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.AdelicUnitaryHaarMeasure
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FundamentalDomainNeZero
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
open NumberField MeasureTheory Matrix Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice GlobalTheory.IndefiniteRowSideFullHecke.InfiniteCoordinateUnfold GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers GlobalTheory.Mem.Vol GlobalTheory.Mem.VolExists
open scoped ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_restrict_latticeStabiliser_measure_eq_compactDual : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (I : Type) [Fintype I] (τ : I → (E →+* ℂ)) (θ : I → (Ainf F ⊗[F] E →+* ℂ)), (∀ ρ, IsInfEmb (τ ρ) (θ ρ)) → ∀ (M P Q : ℕ), M = P + Q → ∀ (J : Matrix (Fin M) (Fin M) E), J.det ≠ 0 → ∀ (A : I → Matrix (Fin P ⊕ Fin Q) (Fin M) ℂ), (∀ ρ, (A ρ)ᴴ * Formalism.UG.Jpq P Q * A ρ = J.map (τ ρ)) → ∀ (L : Set (Fin M → E)), MeasurableSet (stab σ J L : Set (HA (AF F) σ J)) → ∀ (cd : CDHaar) (μ : Measure (HA (AF F) σ J)), (∀ B : I → Set (UpqT P Q), (∀ ρ, MeasurableSet (B ρ)) → μ {h | StabHat F L (finMat σ J h) ∧ ∀ ρ, ∃ b ∈ B ρ, UpqT.mat b * A ρ = A ρ * infMat σ J (θ ρ) h} = ∏ ρ, cd.cd P Q (B ρ)) → (∃ N : I → Matrix (Fin M) (Fin P ⊕ Fin Q) ℂ, (∀ ρ, N ρ * A ρ = 1) ∧ ∀ ρ, A ρ * N ρ = 1) ∧ ∃ ψ : HA (AF F) σ J →* (I → UpqT P Q), Continuous ψ ∧ (∀ h ρ, UpqT.mat (ψ h ρ) * A ρ = A ρ * infMat σ J (θ ρ) h) ∧ (μ.restrict (stab σ J L)).map ψ = Measure.pi fun _ => cd.cd P Q := by
  first | exact @GlobalTheory.VolStabImage.map_restrict_stab | exact GlobalTheory.VolStabImage.map_restrict_stab | (intros; apply GlobalTheory.VolStabImage.map_restrict_stab <;> assumption)
