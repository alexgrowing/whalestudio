import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.AbsNormGeTwo
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.UnramifiedFactorEqOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocalFactorsPosTypicalGeneral

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ProdConvCut2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.ProdConvCut

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)

def ProdConvNew : Prop :=
  (∀ v, (TypAt X v → 0 < MX X u u' ψ v) ∧ 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
    0 < alX X u u' v) ∧
  True ∧ True ∧
  Multipliable (fun v : OrdX X => localVolumeUnit X ψ v.1) ∧ 0 < ∏' v : OrdX X, localVolumeUnit X ψ v.1 ∧
  Multipliable (ZZX X u u' ψ) ∧ 0 < ∏' v : PlX X, ZZX X u u' ψ v ∧
  (∀ l, Multipliable (PPX X u u' ψ l) ∧ 0 < ∏' v : PlX X, PPX X u u' ψ l v) ∧
  Multipliable (fun v : OrdX X => alX X u u' v.1) ∧ 0 < ∏' v : OrdX X, alX X u u' v.1 ∧
  Multipliable (jacX X) ∧ 0 < ∏' v : PlX X, jacX X v

private theorem multipliable_and_tprod_pos_of_finite_mulSupport {ι : Type*} (f : ι → ℝ) (hpos : ∀ i, 0 < f i) (hfin : (Function.mulSupport f).Finite) :
    Multipliable f ∧ 0 < ∏' i, f i := by
  refine ⟨multipliable_of_finite_mulSupport hfin, ?_⟩
  rw [tprod_eq_prod' (s := hfin.toFinset) (by simp)]
  exact Finset.prod_pos fun i _ => hpos i

theorem prodConvNew_of (h1 : VolOneAEC X u u' ψ)
    (hpos : ∀ v, 0 < localVolumeUnit X ψ v ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧ 0 < jacX X v)
    (hM : ∀ v, TypAt X v → 0 < MX X u u' ψ v) (hal : ∀ v, 0 < alX X u u' v) (h3 : AlConvC X u u') :
    ProdConvNew X u u' ψ := by
  have hS : ∀ g : PlX X → ℝ, (∀ v, g v ≠ 1 → ¬ (localVolumeUnit X ψ v = 1 ∧ ZZX X u u' ψ v = 1 ∧
      (∀ l, PPX X u u' ψ l v = 1) ∧ jacX X v = 1)) → (Function.mulSupport g).Finite :=
    fun g hg => h1.subset fun v hv => hg v hv
  have hU : (Function.mulSupport fun v : OrdX X => localVolumeUnit X ψ v.1).Finite := by
    refine (h1.preimage Subtype.val_injective.injOn).subset fun v hv => ?_
    intro h
    exact hv h.1
  have hZ := hS (ZZX X u u' ψ) fun v hv h => hv h.2.1
  have hP : ∀ l, (Function.mulSupport (PPX X u u' ψ l)).Finite := fun l => hS _ fun v hv h => hv (h.2.2.1 l)
  have hJ := hS (jacX X) fun v hv h => hv h.2.2.2
  have rU := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v : OrdX X => (hpos v.1).1) hU
  have rZ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.1) hZ
  have rJ := multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.2) hJ
  exact ⟨fun v => ⟨hM v, (hpos v).1, (hpos v).2.1, (hpos v).2.2.1, hal v⟩, trivial, trivial, rU.1, rU.2, rZ.1, rZ.2,
    fun l => multipliable_and_tprod_pos_of_finite_mulSupport _ (fun v => (hpos v).2.2.1 l) (hP l), h3.1, h3.2, rJ.1, rJ.2⟩

theorem prodConvNew_gen (hb : Formalism.L2.SG.AdBridge.AdBridgeIso X.B.I) (hψ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsCharAF X.B.I.F ψ)
    (hs : IsStdChar ψ) (hloc : ∀ w : D.what₂.Word, LocCompatX X ψ w)
    (hpos : ∀ v, (¬ TypAt X v → 0 < localVolumeUnit X ψ v) ∧ 0 < ZZX X u u' ψ v ∧ (∀ l, 0 < PPX X u u' ψ l v) ∧
      0 < jacX X v) :
    ProdConvNew X u u' ψ := by
  have hk : 1 ≤ D.R.k := Formalism.MainNotions.S.k_pos (D := D)
  refine prodConvNew_of X u u' ψ (VolOneAEC_holds (X := X) (u := u) (u' := u') (ψ := ψ) hψ hs) (fun v => ⟨?_, (hpos v).2.1,
    (hpos v).2.2.1, (hpos v).2.2.2⟩) (fun v h => (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).1)
    (fun v => lt_of_lt_of_le (Real.exp_pos _) (alX_bounds (X := X) (u := u) (u' := u') hk v).1)
    (AlConvC_holds (X := X) (u := u) (u' := u'))
  by_cases h : TypAt X v
  · exact (local_factors_pos_typical_general X hb ψ hψ hs hloc u u' v h).2
  · exact (hpos v).1 h

theorem prodConvNew_ties (T : Formalism.L2.SG.SpectralTiesReal.STies D) (u u' : D.what₂.Word)
    (hpos : ∀ v, (¬ TypAt T.X v → 0 < localVolumeUnit T.X T.ψ v) ∧ 0 < ZZX T.X u u' T.ψ v ∧ (∀ l, 0 < PPX T.X u u' T.ψ l v) ∧
      0 < jacX T.X v) :
    ProdConvNew T.X u u' T.ψ := by
  exact prodConvNew_gen T.X u u' T.ψ T.hb T.ψ_char T.ψ_std T.locCompat hpos

end Formalism.L2.SG.Pf.ProdConvCut2
