import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SumMatApply
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
open GlobalTheory.Core.Rk.SumBox

noncomputable section

namespace GlobalTheory.Core.Rk.SumBox

variable {D : D7}

theorem pair_eq_dot (n : ℕ) (G : Matrix (Fin n) (Fin n) D.host.E) (x y : Fin n → D.host.E) :
    ∑ i, ∑ j, star (x i) * G i j * y j = star x ⬝ᵥ (G *ᵥ y) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem pair_iA {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iA *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * W.gram i j * (o.qA *ᵥ y) j := by
  have hq : W.gram * o.qA = o.iAᴴ * B.gram := by
    rw [OrthDec.qA, Matrix.mul_nonsing_inv_cancel_left _ _ (gram_isUnit_det W)]
  rw [pair_eq_dot, pair_eq_dot, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, hq]

theorem pair_iB {B W H : HSp D} (o : OrthDec B W H) (x : Fin H.rank → D.host.E) (y : Fin B.rank → D.host.E) :
    ∑ i, ∑ j, star ((o.iB *ᵥ x) i) * B.gram i j * y j = ∑ i, ∑ j, star (x i) * H.gram i j * (o.qB *ᵥ y) j :=
  pair_iA o.symm x y

theorem split_vec {B W H : HSp D} (o : OrthDec B W H) (y : Fin B.rank → D.host.E) :
    o.iA *ᵥ (o.qA *ᵥ y) + o.iB *ᵥ (o.qB *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, o.iA_qA_add, Matrix.one_mulVec]

theorem qA_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qA *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qA_iA, o.qA_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero]

theorem qB_split {B W H : HSp D} (o : OrthDec B W H) (x : Fin W.rank → D.host.E) (x' : Fin H.rank → D.host.E) :
    o.qB *ᵥ (o.iA *ᵥ x + o.iB *ᵥ x') = x' := by
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, o.qB_iA, o.qB_iB, Matrix.one_mulVec,
    Matrix.zero_mulVec, zero_add]

theorem iA_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) {LW : Lat W} (LH : Lat H) {x : Fin W.rank → D.host.E}
    (hx : x ∈ LW) : o.iA *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨x, hx, 0, zero_mem _, by rw [Matrix.mulVec_zero, add_zero]⟩

theorem iB_mem_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) {LH : Lat H} {x : Fin H.rank → D.host.E}
    (hx : x ∈ LH) : o.iB *ᵥ x ∈ sumLatO o LW LH :=
  (mem_sumLatO o LW LH _).2 ⟨0, zero_mem _, x, hx, by rw [Matrix.mulVec_zero, zero_add]⟩

theorem isLattice_sumLatO {B W H : HSp D} (o : OrthDec B W H) (LW : Lat W) (LH : Lat H)
    (hW : Submodule.IsLattice D.host.E LW) (hH : Submodule.IsLattice D.host.E LH) :
    Submodule.IsLattice D.host.E (sumLatO o LW LH) := by
  refine ⟨(hW.fg.map _).sup (hH.fg.map _), eq_top_iff.2 fun y _ => ?_⟩
  have hA : ∀ z ∈ Submodule.span D.host.E (LW : Set (Fin W.rank → D.host.E)),
      o.iA *ᵥ z ∈ Submodule.span D.host.E (sumLatO o LW LH : Set (Fin B.rank → D.host.E)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (iA_mem_sumLatO o LH hx)
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.mulVec_add]; exact add_mem hx hz
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
  have hB : ∀ z ∈ Submodule.span D.host.E (LH : Set (Fin H.rank → D.host.E)),
      o.iB *ᵥ z ∈ Submodule.span D.host.E (sumLatO o LW LH : Set (Fin B.rank → D.host.E)) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span (iB_mem_sumLatO o LW hx)
    | zero => rw [Matrix.mulVec_zero]; exact zero_mem _
    | add x z _ _ hx hz => rw [Matrix.mulVec_add]; exact add_mem hx hz
    | smul a x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ a hx
  rw [← split_vec o y]
  exact add_mem (hA _ (hW.span_eq_top ▸ Submodule.mem_top)) (hB _ (hH.span_eq_top ▸ Submodule.mem_top))

theorem selfDual_sumLatO : ∀ (D : D7) (B W H : HSp D) (o : OrthDec B W H) (LW : Lat W) (LH : Lat H),
    IsSelfDualC W LW → IsSelfDualC H LH → IsSelfDualC B (sumLatO o LW LH) := by
  intro D B W H o LW LH hW hH
  refine ⟨isLattice_sumLatO o LW LH hW.1 hH.1, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := (mem_sumLatO o LW LH y).1 hy
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (mem_sumLatO o LW LH x).1 hx
    obtain ⟨b₁, hb₁⟩ := (hW.2 y₁).1 hy₁ x₁ hx₁
    obtain ⟨b₂, hb₂⟩ := (hH.2 y₂).1 hy₂ x₂ hx₂
    refine ⟨b₁ + b₂, ?_⟩
    have e : ∑ i, ∑ j, star ((o.iA *ᵥ x₁ + o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j =
        ∑ i, ∑ j, star ((o.iA *ᵥ x₁) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j +
          ∑ i, ∑ j, star ((o.iB *ᵥ x₂) i) * B.gram i j * (o.iA *ᵥ y₁ + o.iB *ᵥ y₂) j := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, star_add]
      ring
    rw [e, pair_iA, pair_iB, qA_split, qB_split, ← hb₁, ← hb₂]
    push_cast
    ring
  · have hA : o.qA *ᵥ y ∈ LW := (hW.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iA_mem_sumLatO o LH hx)
      exact ⟨b, hb.trans (pair_iA o x y)⟩
    have hB : o.qB *ᵥ y ∈ LH := (hH.2 _).2 fun x hx => by
      obtain ⟨b, hb⟩ := hy _ (iB_mem_sumLatO o LW hx)
      exact ⟨b, hb.trans (pair_iB o x y)⟩
    rw [← split_vec o y]
    exact (mem_sumLatO o LW LH _).2 ⟨_, hA, _, hB, rfl⟩

end GlobalTheory.Core.Rk.SumBox
end
