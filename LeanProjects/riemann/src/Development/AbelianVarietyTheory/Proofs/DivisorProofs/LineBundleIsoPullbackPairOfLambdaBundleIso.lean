import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAHOfIsFactorAH
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LamPull

theorem lbIso_pull_lift : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left) (M : LB A.left), P.IsLB → M.IsLB → LBIso P (cubeLB A ![fst A A, snd A A] M) → ∀ (T : Over (Sp ℂ)) (a b : T ⟶ A), LBIso (P.pull (lift a b).left) (cubeLB A ![a, b] M) := by
  intro A _ _ P M hP hM e T a b
  have hc : ∀ {T' : Over (Sp ℂ)} (x : Fin 2 → (T' ⟶ A)), (cubeLB A x M).IsLB := fun x => by
    unfold cubeLB; exact LB.isLB_linComb hM _ _
  have h₁ : LBIso (P.pull (lift a b).left) ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) :=
    GlobalTheory.GenSpread.lbIso_pullback e _
  have h₂ : LBIso ((cubeLB A ![fst A A, snd A A] M).pull (lift a b).left) (cubeLB A ![a, b] M) :=
    LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl)
      (GlobalTheory.PrimNorm.chartSquare M (lift a b) (lift_fst a b).symm (lift_snd a b).symm) (GlobalTheory.lbIso_refl (hc _))
  exact LBIso.trans (pull_isLB hP _) (pull_isLB (hc _) _) (hc _) h₁ h₂

end GlobalTheory.LamPull
