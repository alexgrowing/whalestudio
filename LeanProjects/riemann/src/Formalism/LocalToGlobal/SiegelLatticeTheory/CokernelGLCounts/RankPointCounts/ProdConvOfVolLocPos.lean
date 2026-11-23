import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdConvCut

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def VolOneAEC : Prop :=
  {v : PlX X | ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧ (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)}.Finite

def MXAE : Prop := {v : PlX X | MX X u u' ψ v ≠ alX X u u' v}.Finite

private theorem multipliable_and_tprod_pos_of_finite_ne_one {α : Type*} (f : α → ℝ) (hpos : ∀ a, 0 < f a)
    (hfin : {a | ¬ f a = 1}.Finite) : Multipliable f ∧ 0 < ∏' a, f a := by
  have hs : ∀ b ∉ hfin.toFinset, f b = 1 := by
    intro b hb
    by_contra hne
    exact hb (hfin.mem_toFinset.2 hne)
  refine ⟨?_, ?_⟩
  · first
    | exact multipliable_of_ne_finset_one hs
    | exact (hasProd_prod_of_ne_finset_one hs).multipliable
  · rw [tprod_eq_prod hs]
    exact Finset.prod_pos (fun a _ => hpos a)

theorem prodConv_of_vol_locPos (h1 : VolOneAEC X u u' ψ) (hM : MXAE X u u' ψ) (h2 : LocPosC X u u' ψ) (h3 : AlConvC X u u') :
    ProdConv X u u' ψ := by
  unfold VolOneAEC at h1
  unfold LocPosC at h2
  unfold AlConvC at h3
  have hU := multipliable_and_tprod_pos_of_finite_ne_one (fun v : OrdX X => localVolumeUnit X ψ v.1) (fun v => (h2 v.1).2.1)
    (Set.Finite.preimage Subtype.val_injective.injOn
      (h1.subset (fun v (hv : ¬ localVolumeUnit X ψ v = 1) hall => hv hall.1)))
  have hZ := multipliable_and_tprod_pos_of_finite_ne_one (ZZX X u u' ψ) (fun v => (h2 v).2.2.1)
    (h1.subset (fun v hv hall => hv hall.2.1))
  have hP : ∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v := fun l =>
    multipliable_and_tprod_pos_of_finite_ne_one (PPX X u u' ψ l) (fun v => (h2 v).2.2.2.1 l)
      (h1.subset (fun v hv hall => hv (hall.2.2.1 l)))
  have hJ := multipliable_and_tprod_pos_of_finite_ne_one (jacX X) (fun v => (h2 v).2.2.2.2.2)
    (h1.subset (fun v hv hall => hv hall.2.2.2))
  unfold ProdConv
  exact ⟨fun v => ⟨fun _ => (h2 v).1, (h2 v).2.1, (h2 v).2.2.1, (h2 v).2.2.2.1, (h2 v).2.2.2.2.1⟩,
    trivial, trivial, hU.1, hU.2, hZ.1, hZ.2, hP, h3.1, h3.2, hJ.1, hJ.2⟩

end Formalism.L2.SG.Pf.ProdConvCut2
