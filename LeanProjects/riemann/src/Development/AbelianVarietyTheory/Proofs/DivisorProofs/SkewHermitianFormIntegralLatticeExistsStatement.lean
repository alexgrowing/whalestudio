import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianFormIntegralLatticeExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFundamentalDomainMulRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.AdelicIsomorphismStatement
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BridgeSIsBridge
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThetaCplV
open Matrix
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.skew_hermitian_form_integral_lattice_exists : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → Even d → ∀ c : E, c ≠ 0 → σ c = -c → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsHermND σ (c • W.J.map σ) ∧ ∃ L : Submodule (𝓞 E) (Fin d → E), L.FG ∧ Submodule.span E (L : Set (Fin d → E)) = ⊤ ∧ ∀ x : Fin d → E, x ∈ L ↔ ∀ y ∈ L, Formalism.UG.hform (σ : E →+* E) (c • W.J.map σ) y x ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.SkewSelfDual.exists_selfDual_smul_skew | exact GlobalTheory.SkewSelfDual.exists_selfDual_smul_skew | (intros; apply GlobalTheory.SkewSelfDual.exists_selfDual_smul_skew <;> assumption)
