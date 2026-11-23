import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.Sh
open GlobalTheory.FGDepth GlobalTheory.CharDepth GlobalTheory.FactorDepth GlobalTheory.LawLog

theorem limPt_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  intro hAdd hAct hCont
  intro C _ _ v d R _ _ O _ _ B hB σ _ κ _ w hw A a hA
  have hdI : ∀ c e e', IsIntV v (dAct C B c e e') := fun c e _ => hB.2.1 c e _
  have hAI : ∀ b e e', IsIntV v (A b e e') := by
    intro b e e'
    have h0 : IsIntV v (A b e e' - dAct C B (a 0 b) e e') := by
      have := hA 0 b e e'
      simpa [IsIntV] using this
    have : A b e e' = (A b e e' - dAct C B (a 0 b) e e') + dAct C B (a 0 b) e e' := by ring
    rw [this]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h0) ((ptIsIntV_iff _).1 (hdI _ _ _)))
  have hN : ∀ N, IntLog (fglOf hB) (∑ b, mv (dAct C B (a N b)) (w b)) := fun N =>
    Finset.sum_induction _ (IntLog (fglOf hB)) (fun x y hx hy => (hAdd C v d (fglOf hB) σ).2.2 x y hx hy)
      (hAdd C v d (fglOf hB) σ).1 (fun b _ => (hAct C v d R O B hB σ (a N b)).2 _ (hw b))
  have hw0 : ∀ b i, constantCoeff (w b i) = 0 := fun b => (hw b).1
  have key : ∀ (M : κ → Matrix (Fin d) (Fin d) C) (i : Fin d),
      expPt (fglOf hB) (∑ b, mv (M b) (w b)) i =
        subst (fun q => ∑ x : κ × Fin d, M x.1 q x.2 • w x.1 x.2) (expOf (fglOf hB) i) := by
    intro M i
    unfold expPt
    congr 1
    funext q
    rw [Finset.sum_apply, Fintype.sum_prod_type]
    rfl
  refine ⟨fun i => ?_, fun i α => ?_⟩
  · rw [Finset.sum_apply, map_sum]
    exact Finset.sum_eq_zero fun b _ => cc_mv (A b) (hw0 b) i
  · obtain ⟨N₀, hN₀⟩ := hCont C v (Fin d) σ (κ × Fin d) (expOf (fglOf hB) i) (fun x => w x.1 x.2)
      (fun x => hw0 x.1 x.2) α
    have h1 := hN₀ (fun q x => A x.1 q x.2) (fun q x => dAct C B (a N₀ x.1) q x.2) (fun q x => hAI _ _ _)
      (fun q x => hdI _ _ _) (fun q x => hA N₀ x.1 q x.2)
    have h2 := (hN N₀).2 i α
    rw [key] at h2
    rw [key]
    rw [← sub_add_cancel (coeff α (subst (fun q => ∑ x : κ × Fin d, A x.1 q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))
      (coeff α (subst (fun q => ∑ x : κ × Fin d, dAct C B (a N₀ x.1) q x.2 • w x.1 x.2)
      (expOf (fglOf hB) i) : MvPowerSeries σ C))]
    exact (ptIsIntV_iff _).2 (Subring.add_mem _ ((ptIsIntV_iff _).1 h1) ((ptIsIntV_iff _).1 h2))

end GlobalTheory.IsoTriv
