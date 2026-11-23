import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem cTw_eq_mul (B : Base) :
    ((B.R.m * (B.R.t + 1) / 2 : ℕ) : ℤ) = (B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ) := by
  obtain ⟨b, hb⟩ := B.R.t_odd
  have h2 : B.R.t + 1 = 2 * (b + 1) := by omega
  rw [h2, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2), Nat.mul_left_comm,
    Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  push_cast
  ring

theorem trueWeight_lastStep_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ = B.wts.lamTrue u B.R.m τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (Examples₂.lamOf (B.hcW u τ) B.R.m) (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (Examples₂.lamOf (B.hcW u τ) B.R.m) (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

theorem trueRowWeight_trueColumns {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)
    (τ : (I.rec7 l Z).what₂.Tau) : Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ = B.wts.sgTrue τ := by
  have h := cTw_eq_mul B
  show Formalism.MainNotions.product_first_zeroth_parts.wSh (B.wts.row τ).sg (Formalism.MainNotions.product_first_zeroth_parts.cTw B.R) =
    Formalism.L2.Col.shiftW (B.wts.row τ).sg (-((B.R.m : ℤ) * (((B.R.t + 1) / 2 : ℕ) : ℤ)))
  unfold Formalism.MainNotions.product_first_zeroth_parts.wSh Formalism.L2.Col.shiftW Formalism.MainNotions.product_first_zeroth_parts.cTw
  congr 1
  funext i
  rw [h]
  ring

end GlobalTheory.Mem.Col2.TC

namespace GlobalTheory.Mem.Col2.TC

theorem branchingNorm_identity_trueColumns_members {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    BeOnTie (I.rec7 l Z) u := by
  intro τ
  have e1 := trueWeight_lastStep_trueColumns I l Z u τ
  have e2 := trueRowWeight_trueColumns I l Z u τ
  have n1 : (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ).natW :=
    Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  have n2 : (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ).natW = (((I.rec7 l Z).fm u).sg τ).natW := Formalism.MainNotions.product_first_zeroth_parts.natW_wSh _ _
  show fockOpNorm (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)
      (GlobalTheory.IndefiniteRowSideFullHecke.InterlacingEquivariance.brOne ℂ (N_m_succ B.R) (B.wts.lamTrue u B.R.m τ) (B.wts.sgTrue τ)) =
    fockOpNorm (((I.rec7 l Z).fm u).lam (I.rec7 l Z).R.m τ) (((I.rec7 l Z).fm u).sg τ)
      (Formalism.L2.Ker.brOne ℂ (Formalism.MainNotions.product_first_zeroth_parts.Nm_succ (I.rec7 l Z).R).symm (Formalism.MainNotions.product_first_zeroth_parts.lamTr (I.rec7 l Z) u τ)
        (Formalism.MainNotions.product_first_zeroth_parts.sgTr (I.rec7 l Z) u τ))
  rw [e1, e2] at *
  exact fockOpNorm_congr _ n1 n2

theorem beOnTie_true : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws)
    (Z : TC.Later B (I.cols l)), ∀ u, BeOnTie (I.rec7 l Z) u :=
  fun I _ _ l Z u => branchingNorm_identity_trueColumns_members I l Z u

end GlobalTheory.Mem.Col2.TC
