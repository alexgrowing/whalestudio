import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CenterActionIterateMatchesDifferential
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
theorem _root_.GlobalTheory.T.center_action_iterate_matches_differential : ∀ (I : Formalism.MainNotions.S.AutInst) (s : I.E →ₐ[I.F] I.E) (hs : s = I.cm.sig) (v : InfinitePlace I.F) (m : ℕ), ∃ z : List (ℝ → GlobalTheory.AdelicU.GAd s I.J) →₀ ℂ, GlobalTheory.UAut.IsCentral s I.J z ∧ ∀ (N : ℕ) (φ : GlobalTheory.AdelicU.GAd s I.J → ℂ), GlobalTheory.UAut.IsSm s I.J φ → (GlobalTheory.Dec.zOp I v m)^[N] (fun x => φ (GlobalTheory.HCFinU.bridgeS I s hs x)) = fun x => (GlobalTheory.UAut.dop z)^[N] φ (GlobalTheory.HCFinU.bridgeS I s hs x) := by
  first | exact @GlobalTheory.HCFinU.Central.zOp_eq_dop | exact GlobalTheory.HCFinU.Central.zOp_eq_dop | (intros; apply GlobalTheory.HCFinU.Central.zOp_eq_dop <;> assumption)
