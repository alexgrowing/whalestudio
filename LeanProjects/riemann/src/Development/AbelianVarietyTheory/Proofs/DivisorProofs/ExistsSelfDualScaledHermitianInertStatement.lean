import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSelfDualScaledHermitianInert
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocKLeLocU
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsConjAt
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_self_dual_scaled_hermitian_inert : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d r s : ℕ) (W : Spc F E d), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → W.IsSkew σ B r s →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), w.under (𝓞 F) = v → Formalism.UG.IsInertAt F E v w →
    ∃ δ : E, δ ≠ 0 ∧ IsHermND σ (δ • W.J.map σ) ∧ IsSelfDualAt σ (δ • W.J.map σ) W.L v := by
  first | exact @GlobalTheory.InertSkewRescale.exists_herm_selfDualAt | exact GlobalTheory.InertSkewRescale.exists_herm_selfDualAt | (intros; apply GlobalTheory.InertSkewRescale.exists_herm_selfDualAt <;> assumption)
