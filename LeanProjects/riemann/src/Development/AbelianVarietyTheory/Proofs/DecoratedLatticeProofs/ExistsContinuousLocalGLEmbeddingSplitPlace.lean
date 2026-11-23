import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSplitPlaceHermitianFrameGLEmbedding
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LocEmb

theorem exists_gl : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (Y : Type) [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k V.rank Y),
    ∃ gl : GL Y k →* GA D V, Continuous gl ∧ (∀ x, SuppAt q.e V (gl x) ∧ (mt V (gl x)).map q.pr = F.β * x.val * F.γ) ∧
      ∀ g x, SuppAt q.e V g → (mt V g).map q.pr = F.β * x.val * F.γ → g = gl x := by
  intro D k _ _ _ _ q V Y _ _ F
  obtain ⟨h1, -, h3⟩ := (GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k (GlobalTheory.LocMod.ofSplit q)).1 V Y F
  choose f hf hu using h1
  have hmul : ∀ x y, f (x * y) = f x * f y := fun x y => (hu (x * y) _ (h3 _ _ _ _ (hf x) (hf y))).symm
  have hone : f 1 = 1 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact (mul_eq_left.1 h.symm)
  let gl : GL Y k →* GA D V := { toFun := f, map_one' := hone, map_mul' := hmul }
  let fr : GlobalTheory.FinPl.Frame q V Y := ⟨F.β, F.γ, F.βγ, F.γβ, gl, fun x => (hf x).1, fun x => (hf x).2⟩
  refine ⟨gl, GlobalTheory.FrameCont.continuous_gl D k q V Y fr, fun x => hf x, fun g x hs hm => hu x g ⟨hs, hm⟩⟩

end GlobalTheory.LocEmb
