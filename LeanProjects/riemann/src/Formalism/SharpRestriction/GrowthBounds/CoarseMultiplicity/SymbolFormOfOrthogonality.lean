import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.WeightWLet
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FtFockZeroLeft
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.IoBlockSupported
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.FactorialExponentEqProd

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

theorem symPolAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X)
    (hO : OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) : SymPolAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  classical
  intro X _ O _ _ hD1 hH hc mm β hβ s hs
  have St := hstd X hD1 hH hc
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro μ hμ x
  have hwh : IsWeightedHomogeneous (wLet X x) (symFam (KK O) X.p C0 CE1 CE2 X β s)
      (∑ j, TD C0 CE1 CE2 X j (β j) (wLet X x)) :=
    IsWeightedHomogeneous.prod _ _ _ (fun j _ => ioBlock_wh C0 CE1 CE2 X j O mm (β j) (wLet X x) (fun _ _ _ => rfl)
      (fun _ => rfl) rfl (s j) (hs j))
  have h1 := hwh (mem_support_iff.1 (Finset.mem_coe.1 hμ))
  rw [weight_wLet] at h1
  rw [h1, Finset.sum_congr rfl fun j _ => TD_wLet C0 CE1 CE2 X j x (β j) (hβ j) (hO X hD1 hH hc j (β j) (hβ j)),
    ← natPartSum X.TT St.seg2 (fun s => if s = x.1.val then hhDegs X.TT X.aT X.bT x else 0), Finset.sum_ite_eq',
    if_pos x.1.2]

def RestOPlus : Prop := TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 _ Cc => OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc

theorem restSymPol_of (h : RestOPlus) : RestSymPol := by
  refine TransportedAlt.mono ?_ (thr_std.and h)
  rintro C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc ⟨⟨_, hstd⟩, hO⟩
  exact symPolAt_of hstd hO

theorem symbol_form_of_orthogonality (hB : RestBlockForm) (h1 : ∀ C0 CE1 CE2, OrthAt C0 CE1 CE2) (h3 : RestOPlus) : RestForm :=
  restForm_of' hB h1 prodAt (restSymPol_of h3) intAt numAt zProdAt

end Formalism.MainNotions.ColumnSystems.Pf
