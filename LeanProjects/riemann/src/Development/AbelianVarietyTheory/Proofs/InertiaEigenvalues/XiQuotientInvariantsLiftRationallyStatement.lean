import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationally
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.xiQuotient_invariants_lift_rationally : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (a e b : ℤ) (j : ℕ) (hle : Gj K j ≤ GK K), s ≤ j → a ≤ e → e ≤ b → IsCrysOn S S.W.GKs T → ∀ p : Qab (AinfSub l) (xiU (D.locA l)) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU (D.locA l)) a e, (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) → letI := zlMod LL T; ∀ z : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a e)), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a e) g z = z) → ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b))), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) g x = x) ∧ LinearMap.lTensor ↥T.L.T p x = (l : ℤ_[l]) ^ k • z := by
  first | exact @GlobalTheory.InvariantLift.invariants_lift | exact GlobalTheory.InvariantLift.invariants_lift | (intros; apply GlobalTheory.InvariantLift.invariants_lift <;> assumption)
