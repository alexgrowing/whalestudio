import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GoodLiftOnto
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Lev GlobalTheory.OnTies
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelCharOrder

theorem prod_isOfFinOrder {ι M : Type} [CommMonoid M] (s : Finset ι) (f : ι → M) (h : ∀ i ∈ s, IsOfFinOrder (f i)) :
    IsOfFinOrder (∏ i ∈ s, f i) :=
  Finset.prod_induction f IsOfFinOrder (fun _ _ ha hb => ha.mul hb) IsOfFinOrder.one h

theorem residue_char_isOfFinOrder {E : Type} [Field E] [NumberField E] (PP : Formalism.L2.DIV.Pl E)
    (χ : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (u : (Formalism.L2.DIV.kP PP)ˣ) : IsOfFinOrder (χ u) := by
  have : Finite (Formalism.L2.DIV.kP PP) := Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  exact χ.isOfFinOrder (isOfFinOrder_of_finite u)

theorem levFn_flag1_isOfFinOrder {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (x : GL (Fin V.rank) (Lev.EAf D)) :
    IsOfFinOrder (Formalism.L2.DIV.levFn β (flag1L L) x) := by
  have h1 : Formalism.L2.DIV.ext1 (flag1L L).P.H (flag1L L).P.chi (Formalism.L2.DIV.rTup β (flag1L L) x) = 1 :=
    subgroupCharExtension_one_apply _ _
  unfold Formalism.L2.DIV.levFn
  rw [h1]
  refine (IsOfFinOrder.one.mul ?_).mul ?_
  · exact prod_isOfFinOrder _ _ fun PP _ => prod_isOfFinOrder _ _ fun c _ => residue_char_isOfFinOrder PP _ _
  · exact prod_isOfFinOrder _ _ fun PP _ => residue_char_isOfFinOrder PP _ _

theorem levEnv_chi_isOfFinOrder : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank)
    (k : (levEnv V β L).J), IsOfFinOrder ((levEnv V β L).χ k) := by
  intro D V β L k
  exact levFn_flag1_isOfFinOrder V β L _

end GlobalTheory.LevelCharOrder
