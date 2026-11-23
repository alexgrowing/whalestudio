import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySatakeTransformEqOfBaseChangeSatakeParame
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.PRep GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySatakeTransform_eq_of_baseChangeSatakeParameter_eq : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α α' : Fin (n / 2) → ℂˣ, GlobalTheory.LGrp.bcParam n α = GlobalTheory.LGrp.bcParam n α' → ∀ φ ∈ Hecke ℂ (KU σ n), SatU ϖ q φ (fun i => (α i : ℂ)) = SatU ϖ q φ (fun i => (α' i : ℂ)) := by
  first | exact @GlobalTheory.SatBc.satU_eq_of_bcParam_eq | exact GlobalTheory.SatBc.satU_eq_of_bcParam_eq | (intros; apply GlobalTheory.SatBc.satU_eq_of_bcParam_eq <;> assumption)
