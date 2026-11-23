import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ZAEqAlgebraMapPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000

theorem _root_.UpperTheory.KN.iTot_eisensteinPow_eq_iD_eisensteinHatPow :
    ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (β : ℕ), toOD l ↥(OL LL) (ϖ.iTot (thetaW a LL) ↥LL.1 (fun _ => ⟨E ↥LL.1 l e ^ β, pow_mem (E_mem l e _) β⟩)) = ϖ.iD (thetaW a LL) ↥LL.1 (fun _ => Ehat ↥(OL LL) ↥LL.1 l e) ^ β := by
  intro l _ a e _ _ ϖ LL _ _ β
  refine (ϖ.iD_ofA (thetaW a LL) ↥LL.1 _).symm.trans ?_
  refine Eq.trans ?_ (map_pow (ϖ.iD (thetaW a LL) ↥LL.1) _ β)
  refine congrArg (ϖ.iD (thetaW a LL) ↥LL.1) ?_
  funext τ
  exact map_pow (ofA ↥(OL LL) ↥LL.1 l e) ⟨E ↥LL.1 l e, E_mem l e _⟩ β
