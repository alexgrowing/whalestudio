import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemParLevOfQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOfStarEq
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.Mem.R3.LiftBrg.ActQ

theorem castGL_rfl_apply' {R : Type} [CommRing R] {m : ℕ} (x : GL (Fin m) R) : castGL (rfl : m = m) x = x := by
  apply Units.ext
  ext i j
  simp [castGL]

theorem castGL_St_redFn (X : Stages) {m n : ℕ} (h : m = n) (x : GL (Fin m) (EA X)) (hx : x ∈ Formalism.L2.DIV.St 1)
    (PP : Pl X.toD7.host.E) :
    castGL h x ∈ Formalism.L2.DIV.St 1 ∧
      Formalism.L2.DIV.redFn 1 PP (castGL h x) = castGL h (Formalism.L2.DIV.redFn 1 PP x) := by
  subst h
  rw [castGL_rfl_apply', castGL_rfl_apply']
  exact ⟨hx, rfl⟩

theorem redZ_eq_castGL_redFn : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (U : Set I.ι)
    (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)), LevOf X I U L →
    ∀ (i : Fin X.toD7.R.m) (t : TupU I U) (A k : GL (Fin X.B.R.nV) (LiftBrg.EA X)), LiftBrg.FrameOK X I U i t A k →
    ∀ (κ : (levEnv (Vc X.toD7 i) (L.βV i) (L.datVt i t)).Q) (w : Formalism.L2.Col.rowSG (X.B.primes px) I.sel t.1),
      LiftBrg.ActQ.redZ X I U L i t A k κ w =
        LiftBrg.castGL (LiftBrg.rkEq X i).symm (Formalism.L2.DIV.redFn (L.βV i) w.1
          (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _))) := by
  intro X px I U L hL i t A k hF κ w
  have hAk : A * k ∈ Formalism.L2.DIV.St (1 : GL (Fin X.B.R.nV) (EA X)) := Subgroup.mul_mem _ hF.2.1 hF.2.2.2.2.1
  have hred : Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1 (A * k) = 1 := (Formalism.L2.DIV.mem_princAt.1 (hF.2.2.2.2.2 w.1 w.2)).2
  have hy := Formalism.L2.DIV.parLev_St (mem_parLev_of_Q X I U L i t κ)
  have hβ := hL.beta.1 i
  show Formalism.L2.DIV.redFn (1 : GL (Fin X.B.R.nV) (EA X)) w.1
    ((A * k)⁻¹ * castGL (rkEq X i).symm
      (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) * (A * k)) = _
  generalize (Formalism.UG.bc (swapAE X.toD7) ((κ : Bridge.Gf (Vc X.toD7 i)) : GL (Fin (Vc X.toD7 i).rank) _)) = y at hy ⊢
  generalize L.βV i = β at hy hβ ⊢
  subst hβ
  obtain ⟨hc, hcr⟩ := castGL_St_redFn X (rkEq X i).symm y hy w.1
  have e1 := Formalism.L2.DIV.redFn_mul (Subgroup.mul_mem _ (Subgroup.inv_mem _ hAk) hc) hAk w.1
  have e2 := Formalism.L2.DIV.redFn_mul (Subgroup.inv_mem _ hAk) hc w.1
  have e3 := Formalism.L2.DIV.redFn_inv hAk w.1
  refine e1.trans ?_
  rw [e2, e3, hred, hcr]
  simp

end GlobalTheory.Mem.R3.LiftBrg.ActQ
