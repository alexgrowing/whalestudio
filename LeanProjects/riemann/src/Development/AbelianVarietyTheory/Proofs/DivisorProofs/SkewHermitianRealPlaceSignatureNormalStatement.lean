import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewHermitianRealPlaceSignatureNormal
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
theorem _root_.GlobalTheory.T.skew_hermitian_real_place_signature_normal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (d r s : ℕ) (W : Spc F E d), B.IsGood σ → W.IsSkew σ B r s → ∀ c : E, c ≠ 0 → σ c = -c → ∀ w : InfinitePlace F, ∃ (ε : Fin d → Bool) (P : Matrix (Fin d) (Fin d) ℂ), IsUnit P ∧ Pᴴ * (c • W.J.map σ).map (B.emb w).1 * P = Formalism.REAL.Jm ε ∧ (P⁻¹ * W.θ w * P = Formalism.REAL.Jm ε ∨ P⁻¹ * W.θ w * P = -Formalism.REAL.Jm ε) := by
  first | exact @GlobalTheory.CartanFrame.exists_frame | exact GlobalTheory.CartanFrame.exists_frame | (intros; apply GlobalTheory.CartanFrame.exists_frame <;> assumption)
