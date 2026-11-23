import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AdjKInner
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth

noncomputable section

open Matrix Finset Filter Topology
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.WaveK.Base.RwLinPf

open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.RCalc (Rd_contDiffOn differentiableAt_of_smooth isOpen_GLs)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem word_smooth {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) (w : List (Bool × Fin n × Fin n)) :
    ContDiffOn ℝ ∞ (Rw w f) (GLs n) := by
  induction w with
  | nil => exact hf
  | cons p w ih => exact Rd_contDiffOn (bs p) ih

theorem rwLin : RwLin := by
  intro n V W _ _ _ _ ι _ L f hf w
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    have hs : ∀ i, ContDiffOn ℝ ∞ (Rw w (f i)) (GLs n) := fun i => word_smooth (hf i) w
    have e : Rw w (fun y => ∑ i, L i (f i y)) =ᶠ[𝓝 x] fun y => ∑ i, L i (Rw w (f i) y) :=
      Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hx) fun y hy => ih y hy
    have hd : ∀ i, HasFDerivAt (fun y => L i (Rw w (f i) y))
        ((L i).comp (fderiv ℝ (Rw w (f i)) x)) x := fun i =>
      (L i).hasFDerivAt.comp x (differentiableAt_of_smooth (hs i) hx).hasFDerivAt
    have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i).fderiv
    show fderiv ℝ (Rw w fun y => ∑ i, L i (f i y)) x (x * bs p) =
      ∑ i, L i (fderiv ℝ (Rw w (f i)) x (x * bs p))
    rw [e.fderiv_eq]
    refine (DFunLike.congr_fun hsum (x * bs p)).trans ?_
    exact ContinuousLinearMap.sum_apply _ _ _

end GlobalTheory.CompanionTheory.WaveK.Base.RwLinPf
