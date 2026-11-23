import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetSubquotientRestriction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMidJacAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThK.MidJac GlobalTheory.CuspBlock
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_subquotient_restriction : GlobalTheory.Published.BernsteinZelevinskyFiniteness →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N l n : ℕ) (h : l + n ≤ N)
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), IsSmooth π → HasFiniteLength π →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (Q : Representation ℂ (GL (Fin n) k) W),
      IsSubquotient Q ((jacU (tripPlace h) π).comp (midHom k l n N)) →
    ∀ (Y : Type) [AddCommGroup Y] [Module ℂ Y] (η : Representation ℂ (GL (Fin n) k) Y) (f : Q.IntertwiningMap η), f ≠ 0 →
      ∃ ρ : GlobalTheory.CuspRep.SmIrr (GL (Fin n) k), IsSubquotient ρ.ρ ((jacU (tripPlace h) π).comp (midHom k l n N)) ∧
        ∃ g : ρ.ρ.IntertwiningMap η, g ≠ 0 := by
  first | exact @GlobalTheory.MidIrr.exists_smIrr_subquotient_map | exact GlobalTheory.MidIrr.exists_smIrr_subquotient_map | (intros; apply GlobalTheory.MidIrr.exists_smIrr_subquotient_map <;> assumption)
