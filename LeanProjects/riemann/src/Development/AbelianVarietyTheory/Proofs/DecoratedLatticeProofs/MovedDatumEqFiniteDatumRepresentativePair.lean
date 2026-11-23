import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIffOfCarries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNsmulMemStdHom
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartBasePairDatumRationalApproxEqTwistedStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf

namespace GlobalTheory.AdForm.TwMovedVal

set_option maxHeartbeats 1600000 in

theorem moves_rep_tw : ∀ {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} (A : TwDat I l Z u a Ch), A.Is → ∀ (j : ℕ) (hj : j ≤ B.R.m) (c : (I.stp u a j).Cl) (g : GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j)), finM _ (rankN (I.rec7 l Z) j hj) g = ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 → Moves _ (rankN (I.rec7 l Z) j hj) g ((I.stp u a j).rep c).1.1.deco.1.N := by
  intro B X I l Z u a Ch A hA j hj c g hg
  have h1 := ((hA.reads j hj).pt c).lat
  have h2 := ((hA.base j hj (A.chOf j c)).1).lat
  rw [extTo_deco] at h1 h2
  rw [(hA.base j hj (A.chOf j c)).2] at h2
  have hinv : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ = ((((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1)⁻¹ : GL _ _).1 := by
    have e1 : finM _ (rankN (I.rec7 l Z) j hj) g⁻¹ * ((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1.1 = 1 := by
      rw [← hg, ← GlobalTheory.RepLattice.finM_mul', inv_mul_cancel, GlobalTheory.RepLattice.finM_one']
    rw [← Matrix.mul_one (finM _ _ g⁻¹), ← Units.mul_inv (((A.K j hj (A.chOf j c)).y ⟨c, rfl⟩).1), ← Matrix.mul_assoc, e1,
      Matrix.one_mul]
  intro x
  rw [hinv]
  exact GlobalTheory.RepLattice.mem_iff_of_carries _ _ _ ((I.stp u a j).rep c).1.1.deco.2.lat h1 h2 x

set_option maxHeartbeats 1600000 in

theorem moved_datum_val_tw : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) α γ, ∀ Φ : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ, IsSBHalf A.e (stdHom _ _) Φ → ∀ p : ℂ, (∀ z, Φ (z.map fun r => A.e * incA (I.rec7 l Z) r) = p * A.xi i hi α γ z) → ∀ (c : {c // A.chOf i c = α}) (c' : {c // A.chOf (i + 1) c = γ}), Moves _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (A.h i α c) ((I.stp u a i).rep c.1).1.1.deco.1.N ∧ Moves _ (rankN (I.rec7 l Z) (i + 1) hi) (A.h (i + 1) γ c') ((I.stp u a (i + 1)).rep c'.1).1.1.deco.1.N ∧ ∀ z : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E, Φ (actO _ _ (A.h i α c)⁻¹ (A.h (i + 1) γ c')⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) = p * B.embLL (xiAt I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) u i c.1.1 c'.1.1 ((I.stp u a i).rep c.1) ((I.stp u a (i + 1)).rep c'.1) (toHom _ _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) (rankN (I.rec7 l Z) (i + 1) hi) z)) := by
  intro B X I hOk hP l Z u a Ch A hA i hi α γ Φ hΦ p hΦv c c'
  obtain ⟨c, rfl⟩ := c
  obtain ⟨c', rfl⟩ := c'
  obtain ⟨hg, hy⟩ := hA.h i (Nat.le_of_succ_le hi) (A.chOf i c) ⟨c, rfl⟩
  obtain ⟨hg', hy'⟩ := hA.h (i + 1) hi (A.chOf (i + 1) c') ⟨c', rfl⟩
  refine ⟨moves_rep_tw A hA i _ c _ hy, moves_rep_tw A hA (i + 1) hi c' _ hy', fun z => ?_⟩
  obtain ⟨M, hM0, hM⟩ := GlobalTheory.T.chartBasePair_datum_rational_approx_eq_twisted I hOk hP l Z u a Ch A hA i hi c c' _ _ hg hg' hy hy'
  obtain ⟨-, k, hk0, hkinv, -⟩ := hΦ
  obtain ⟨γ₀, v, hv, hvh, he⟩ := GlobalTheory.AdForm.exists_rat_half_approx _ _ A.e _ hA.idem (M * k) (Nat.mul_pos hM0 hk0)
    (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r))
  have hx : actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r) =
      A.e • actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => incA (I.rec7 l Z) r) := by
    have : (z.map fun r => A.e * incA (I.rec7 l Z) r) = A.e • (z.map fun r => incA (I.rec7 l Z) r) := by
      ext a b; rfl
    simp only [actO, this, Matrix.mul_smul, Matrix.smul_mul]
  have half : ∀ (n : ℕ) (v : WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))), IsHalf A.e v → IsHalf A.e (n • v) :=
    fun n v h a b => by
      simp only [Matrix.smul_apply, nsmul_eq_mul]
      rw [mul_left_comm, h a b]
  have e1 : Φ (γ₀.map fun r => A.e * incA (I.rec7 l Z) r) =
      Φ (actO _ _ (A.h i (A.chOf i c) ⟨c, rfl⟩)⁻¹ (A.h (i + 1) (A.chOf (i + 1) c') ⟨c', rfl⟩)⁻¹ (z.map fun r => A.e * incA (I.rec7 l Z) r)) := by
    rw [he, ← hx, mul_nsmul]
    exact hkinv _ (nsmul_mem hv M) (half M v hvh) _
  rw [← e1, hΦv]
  congr 1
  refine hM z γ₀ (k • v) (nsmul_mem hv k) (half k v hvh) ?_
  rw [he, ← hx, mul_nsmul']

end GlobalTheory.AdForm.TwMovedVal
