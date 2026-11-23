import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.AnalyticAtDet

noncomputable section

open Matrix Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.LVs.CK

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem isymm (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin n → F) (π : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n G x (u ∘ π) = iteratedFDeriv ℂ n G x u :=
  hG.contDiffAt.iteratedFDeriv_comp_perm u π

theorem ipeel0 (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u 0)) x (fun k => u k.succ) := by
  have hfd : ContDiffAt ℂ n (fderiv ℂ G) x := (hG.contDiffAt (n := ω)).fderiv_right le_top
  have happ := (ContinuousLinearMap.apply ℂ ℂ (u 0)).iteratedFDeriv_comp_left hfd (i := n) le_rfl
  have hfun : (fun y => fderiv ℂ G y (u 0)) = (ContinuousLinearMap.apply ℂ ℂ (u 0)) ∘ fderiv ℂ G := rfl
  rw [← isymm G x hG (n + 1) u (finRotate (n + 1)), iteratedFDeriv_succ_apply_right, hfun, happ]
  simp only [ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, finRotate_last]
  congr 2
  funext k
  simp [Fin.init, finRotate_succ_apply, Fin.coeSucc_eq_succ]

theorem ipeel (G : F → ℂ) (x : F) (hG : AnalyticAt ℂ G x) (n : ℕ) (u : Fin (n + 1) → F) (i0 : Fin (n + 1)) :
    iteratedFDeriv ℂ (n + 1) G x u = iteratedFDeriv ℂ n (fun y => fderiv ℂ G y (u i0)) x (fun k => u (i0.succAbove k)) := by
  rw [← isymm G x hG (n + 1) u i0.cycleRange.symm, ipeel0 G x hG n]
  simp [Fin.cycleRange_symm_zero, Fin.cycleRange_symm_succ]

theorem detD_fin (N : ℕ) (G : Matrix (Fin N) (Fin N) ℂ → ℂ) (hG : AnalyticAt ℂ G 0) :
    detD G = ∑ σ : Equiv.Perm (Fin N), (Equiv.Perm.sign σ : ℂ) *
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
  have hgen : ∀ (m : ℕ) (h : m = N) (e : Fin m ≃ Fin N) (σ : Equiv.Perm (Fin N)),
      iteratedFDeriv ℂ m G 0 (fun i => Matrix.single (e i) (σ (e i)) (1 : ℂ)) =
      iteratedFDeriv ℂ N G 0 (fun k => Matrix.single k (σ k) 1) := by
    intro m h e σ
    subst h
    exact isymm G 0 hG m (fun k => Matrix.single k (σ k) 1) e
  unfold detD
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [hgen _ (Fintype.card_fin N) _ σ]

end PositivityTheory.Rg.Sw.LVs.CK
