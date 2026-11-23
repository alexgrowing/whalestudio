import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVZPrimHolds

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

def OmVDdLoc : Prop :=
  ∀ (v : PlX X) (a : Fin D.R.rS),
    (∀ x ∈ (aaD D a)⁻¹, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc) *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v) ∧
    (∀ x ∈ aaD D a, sc (E := X.B.I.E) v (alp v D.R.rS a.castSucc)⁻¹ *
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v)

def Pm (v : PlX X) (c : Fv X.B.I.F v) (w : (VS D).V) : Submodule (𝓞 D.host.E) (VS D).V where
  carrier := {y | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    simp only [Set.mem_ofPred_eq, map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro y y' hy hy'
    simp only [Set.mem_ofPred_eq, map_add, mul_add] at *
    exact Submodule.add_mem _ hy hy'
  smul_mem' := by
    intro o y hy
    simp only [Set.mem_ofPred_eq] at *
    rw [← algebraMap_smul D.host.E o y, map_smul, smul_eq_mul, map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hy

theorem pm_iff (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) : y ∈ Pm X v c w ↔
    sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((VS D).hT w y)) ∈ OEv (E := X.B.I.E) v :=
  Iff.rfl

theorem pm_zero (v : PlX X) (c : Fv X.B.I.F v) (w y : (VS D).V) (h : (VS D).hT w y = 0) : y ∈ Pm X v c w := by
  rw [pm_iff, h, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem hT_smul_right (w y : (VS D).V) (x : D.host.E) : (VS D).hT w (x • y) = x * (VS D).hT w y := by
  rw [map_smul, smul_eq_mul]

theorem base_lattice_le_first_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc) (X.eX a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ee, mul_zero])
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).1
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, X.ef]
    by_cases hab : a = b
    · subst hab; rw [if_pos rfl, mul_one]; exact (hD v a).1 x hx
    · rw [if_neg hab, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _

theorem base_lattice_le_second_isotropic (hD : OmVDdLoc X) (v : PlX X) (a : Fin D.R.rS) :
    (VS D).L0 ≤ Pm X v (alp v D.R.rS a.castSucc)⁻¹ (X.fY a) := by
  rw [X.Lam_split]
  refine sup_le (sup_le ?_ ?_) ?_
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, hx, rfl⟩
    refine (pm_iff X v _ _ _).2 ?_
    rw [hT_smul_right, ← (VS D).herm.eq (X.eX b) (X.fY a), X.ef]
    by_cases hab : b = a
    · subst hab; rw [if_pos rfl, map_one, mul_one]; exact (hD v b).2 x hx
    · rw [if_neg hab, map_zero, mul_zero, map_zero, map_zero, mul_zero]; exact Submodule.zero_mem _
  · intro y hy
    exact pm_zero X v _ _ _ (X.Lb_perp y hy a).2
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨b, x, _, rfl⟩
    exact pm_zero X v _ _ _ (by rw [hT_smul_right, X.ff, mul_zero])

theorem crd_of_L (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L) :
    ∃ y ∈ (VS D).L0, crdOf X.B.I X.ιE X.bas y = l := by
  refine ⟨∑ i, X.ιE (l i) • X.bas i, (X.L_eq l).1 hl, ?_⟩
  funext j
  have h : X.bas.repr (∑ i, X.ιE (l i) • X.bas i) j = X.ιE (l j) := by
    simp [map_sum, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [crdOf]
  rw [h, RingEquiv.symm_apply_apply]

theorem hform_star (l x : Fin X.B.I.n → X.B.I.E) :
    star (Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J l x) = Formalism.UG.hform (starRingEnd X.B.I.E) X.B.I.J x l := by
  have herm_entry : ∀ i j, star (X.B.I.J i j) = X.B.I.J j i := fun i j => by
    have := congrFun (congrFun X.B.I.J_herm j) i
    simpa [Formalism.UG.IsHerm, Formalism.UG.cT, starRingEnd_apply] using this
  unfold Formalism.UG.hform
  rw [Finset.sum_comm, star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [starRingEnd_apply, star_mul, star_star]
  rw [herm_entry]
  ring

theorem pair_mem (v : PlX X) (s : Fv X.B.I.F v) (w : (VS D).V) (l : Fin X.B.I.n → X.B.I.E) (hl : l ∈ X.B.I.L)
    (hP : (VS D).L0 ≤ Pm X v s w) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (sc (E := X.B.I.E) v s • ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) ∈ OEv (E := X.B.I.E) v := by
  obtain ⟨y, hy, rfl⟩ := crd_of_L X l hl
  rw [hR_smulE_right]
  have h1 : hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas y))
      (ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas w)) =
      inclR (F := X.B.I.F) (Fv X.B.I.F v) (hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w)) :=
    hR_ratTup (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ![crdOf X.B.I X.ιE X.bas y, crdOf X.B.I X.ιE X.bas w] 0 1
  have h2 : hE X.B.I.cm.sig X.B.I.J (crdOf X.B.I X.ιE X.bas y) (crdOf X.B.I X.ιE X.bas w) =
      X.B.I.cm.sig (X.ιE.symm ((VS D).hT w y)) := by
    rw [← hE_crdOf]
    exact (hform_star X _ _).symm
  rw [h1, h2, ← sigR_inclR]
  have hsc : sc (E := X.B.I.E) v s = sigR (Fv X.B.I.F v) X.B.I.cm.sig (sc (E := X.B.I.E) v s) :=
    (sigR_tmul_one (Fv X.B.I.F v) X.B.I.cm.sig s).symm
  rw [hsc, ← map_mul]
  exact sigR_oev X.B.I.cm.sig v ((pm_iff X v s w y).1 (hP hy))

theorem yTup_eq (v : PlX X) (i : Fin (D.R.rS + 1 + D.R.rS)) :
    yTup X u' v i = sc (E := X.B.I.E) v (scl X v i) •
      ratV (F := X.B.I.F) (Fv X.B.I.F v) (crdOf X.B.I X.ιE X.bas (hv X u' i)) := by
  rw [← tupH_eq]; rfl

theorem omVMemEF_of (hD : OmVDdLoc X) : OmVMemEF X u' := by
  intro v i hi
  have hpair : ∀ l ∈ X.B.I.L, hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F v) l)
      (yTup X u' v i) ∈ OEv (E := X.B.I.E) v := by
    intro l hl
    rw [yTup_eq]
    refine Fin.addCases (fun j hj => ?_) (fun b _ => ?_) i hi
    · rcases Fin.eq_castSucc_or_eq_last j with ⟨a, rfl⟩ | rfl
      · have hs : scl X v (Fin.castAdd D.R.rS a.castSucc) = alp v D.R.rS a.castSucc := by
          simp only [scl, Fin.append_left]
        have hw : hv X u' (Fin.castAdd D.R.rS a.castSucc) = X.eX a := by
          simp only [hv, Fin.append_left, Fin.snoc_castSucc]
        rw [hs, hw]
        exact pair_mem X v _ _ l hl (base_lattice_le_first_isotropic X hD v a)
      · exact absurd rfl hj
    · have hs : scl X v (Fin.natAdd (D.R.rS + 1) b) = (alp v D.R.rS b.castSucc)⁻¹ := by
        simp only [scl, Fin.append_right]
      have hw : hv X u' (Fin.natAdd (D.R.rS + 1) b) = X.fY b := by
        simp only [hv, Fin.append_right]
      rw [hs, hw]
      exact pair_mem X v _ _ l hl (base_lattice_le_second_isotropic X hD v b)
  refine ((omVSD_of X (omVSDBwd_holds X)) v _).2 fun x hx => ?_
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    exact hpair l hl
  | zero => rw [OmW.hR_zero_left]; exact Submodule.zero_mem _
  | add x x' _ _ h1 h2 => rw [OmW.hR_add_left]; exact Submodule.add_mem _ h1 h2
  | smul c x _ h =>
    change hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J ((c : Fv X.B.I.F v) • x) _ ∈ _
    rw [OmW.hR_smul_left]; exact oev_smul v h

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
