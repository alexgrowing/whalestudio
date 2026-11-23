import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EWtApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UfGLRatHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryOfIsON
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC

theorem tup_sgHC_eq {R : Ranks} (P : HCParam R) (i : Fin (R.N R.m - 1)) :
    Formalism.L2.Forms.sgHC R P i = (RowPar.of P).sgHC i := by
  have hi := i.2
  have hN : R.N R.m = (R.k + R.m) + R.m * R.t := N_eq_blocks R R.m
  unfold Formalism.L2.Forms.sgHC RowPar.sgHC
  congr 1
  by_cases h1 : (i : ℕ) < R.k - 1
  · rw [dif_pos h1, dif_pos h1]
    rfl
  · rw [dif_neg h1, dif_neg h1]
    have h2 : ((i : ℕ) - (R.k - 1)) / (R.t + 1) < R.m := by
      rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
      have := R.two_le_m
      have e : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
      have e' : R.m * R.t.succ = R.m * (R.t + 1) := rfl
      omega
    rw [dif_pos h2]
    split_ifs with h3
    · simp [RowPar.bAt, h2]
      rfl
    · simp [RowPar.eAt, h2]
      rfl

theorem tup_rowPar_eq (B : Base) (u : B.Word) (τ : Tau B.R) : RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ) := by
  unfold RowPar.of
  rw [B.hcW_v, B.hcW_b, B.hcW_e]

theorem fm_sg_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι), ∀ τ (i : Fin ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1)), (((I.fm l u a).sg τ).w i : ℚ) = Formalism.L2.Forms.sgHC (I.rec7 l Z).R ((I.rec7 l Z).hcW u τ) i - rhoVec ((I.rec7 l Z).R.N (I.rec7 l Z).R.m - 1) i := by
  intro B X I hI hP l Z u a τ i
  have h2 := (tup_sgHC_eq (B.hcW u τ) i).trans (congrArg (fun P => RowPar.sgHC P i) (tup_rowPar_eq B u τ))
  exact (RowPar.sg_eq (B.hc τ) i).trans (congrArg (· - _) h2.symm)

end GlobalTheory.Mem.Col2.TC

end
