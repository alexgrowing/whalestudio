import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RsMemPerpIff

open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {f : Fin D.R.rS → (VS D).V}
  {M : Submodule (𝓞 D.host.E) (WbQ D F0)}

theorem rs_mem_lamC {v : (VS D).V} : v ∈ lamC D F0 f M ↔
    (∀ a, star ((VS D).hT (F0.e a) v) ∈ (aaI D a)⁻¹) ∧
    (∃ w : perpS (VS D) F0.X, (w : (VS D).V) = vPr D F0 f v ∧ (Submodule.Quotient.mk w : WbQ D F0) ∈ M) ∧
    ∀ a, (VS D).hT (f a) (vPr D F0 f v) ∈ aaI D a := Iff.rfl

theorem rs_mem_lamC_perp {v : (VS D).V} (hv : v ∈ perpS (VS D) F0.X) :
    v ∈ lamC D F0 f M ↔ (Submodule.Quotient.mk (⟨v, hv⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M ∧
      ∀ a, (VS D).hT (f a) v ∈ aaI D a := by
  have h0 : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => hv _ (Submodule.subset_span ⟨a, rfl⟩)
  have hvPr : vPr D F0 f v = v := by simp [vPr, h0]
  constructor
  · rintro ⟨-, ⟨w, hw, hwM⟩, h3⟩
    have hwv : w = ⟨v, hv⟩ := Subtype.ext (hw.trans hvPr)
    subst hwv
    exact ⟨hwM, fun a => by rw [← hvPr]; exact h3 a⟩
  · rintro ⟨hM, h3⟩
    refine ⟨fun a => ?_, ⟨⟨v, hv⟩, hvPr.symm, hM⟩, fun a => ?_⟩
    · simp only [h0, star_zero]
      exact fi_zero D _
    · rw [hvPr]
      exact h3 a

theorem rs_orth_perp {y : (VS D).V} (hy : y ∈ orth (VS D) F0.X) : y ∈ perpS (VS D) F0.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact fun x hx => hy x hx

theorem rs_z_mem (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    F0.z ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (z_mem_perp D F0)]
  refine ⟨hM.2.2.1, fun a => ?_⟩
  rw [hf.2.2 a]
  exact fi_zero D _

theorem rs_smul_e_mem (hf : PartnerOK D F0 f) {a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ aaI D a) :
    x • F0.e a ∈ lamC D F0 f M := by
  have hXe : ∀ y ∈ F0.X, ∀ b, (VS D).hT y (F0.e b) = 0 := by
    intro y hy b
    have hy' : y ∈ Submodule.span D.host.E (Set.range F0.e) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      exact F0.e_iso c b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  have hperp : x • F0.e a ∈ perpS (VS D) F0.X := by
    intro y hy
    rw [map_smul, hXe y hy a, smul_zero]
  rw [rs_mem_lamC_perp hperp]
  refine ⟨?_, fun b => ?_⟩
  · have hmem : x • F0.e a ∈ F0.X := Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    have h0 : (Submodule.Quotient.mk (⟨x • F0.e a, hperp⟩ : perpS (VS D) F0.X) : WbQ D F0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [h0]
    exact zero_mem _
  · have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [map_smul, ← hs, hf.1 a b, smul_eq_mul]
    split_ifs with hab
    · subst hab
      simpa using hx
    · simp only [map_zero, mul_zero]
      exact FractionalIdeal.zero_mem _

theorem rs_xlam (hf : PartnerOK D F0 f) : XLam (lamC D F0 f M) (lf D F0) = XS D F0 := by
  apply le_antisymm
  · rintro v ⟨hvΛ, hvX⟩
    have hvX' : v ∈ F0.X := hvX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hvX'
    have hα := ((rs_mem_lamC_perp (rs_X_le_perp D F0 hvX')).1 hvΛ).2
    have hca : ∀ a, c a ∈ aaI D a := by
      intro a
      have h := hα a
      rw [← hc, map_sum] at h
      simp only [map_smul, rs_hT_f_e hf, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h
      exact h
    rw [← hc]
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, c a, hca a, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    exact ⟨rs_smul_e_mem hf hx, Submodule.smul_mem _ x (rs_e_mem_X D F0 a)⟩

theorem rs_prim (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) (c : D.host.E)
    (hc : c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0)) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  obtain ⟨y, hy, x, hx, hyx⟩ := Submodule.mem_sup.1 hc.1
  have hyΛ : y ∈ lamC D F0 f M := hy.1
  have hyp : y ∈ perpS (VS D) F0.X := rs_orth_perp hy.2
  have hxX : x ∈ F0.X := hx
  have hxp : x ∈ perpS (VS D) F0.X := rs_X_le_perp D F0 hxX
  have hyM := ((rs_mem_lamC_perp hyp).1 hyΛ).1
  apply hM.2.2.2 c
  have hsum : c • (⟨F0.z, z_mem_perp D F0⟩ : perpS (VS D) F0.X) = ⟨y, hyp⟩ + ⟨x, hxp⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_add]
    exact hyx.symm
  rw [zbar, ← Submodule.Quotient.mk_smul, hsum, Submodule.Quotient.mk_add, rs_mk_X_zero D F0 hxX, add_zero]
  exact hyM

def rsLift (w : perpS (VS D) F0.X) : (VS D).V := (w : (VS D).V) - ∑ a, (VS D).hT (f a) w • F0.e a

theorem rs_lift_perp (w : perpS (VS D) F0.X) : rsLift (f := f) w ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (rsLift (f := f) w) = 0
  intro x hx
  have hxe : ∀ b, (VS D).hT x (F0.e b) = 0 := by
    intro b
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F0.e_iso a b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add, LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  simp only [rsLift, map_sub, map_sum, map_smul, hxe, smul_zero, Finset.sum_const_zero, sub_zero]
  exact w.2 x hx

theorem rs_lift_mk (w : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk (⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) : WbQ D F0) =
      Submodule.Quotient.mk w := by
  apply (Submodule.Quotient.eq _).mpr
  show (((⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) - w : perpS (VS D) F0.X) : (VS D).V) ∈ F0.X
  simp only [Submodule.coe_sub, rsLift, sub_sub_cancel_left]
  exact neg_mem (sum_mem fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem rs_hT_f_lift (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X) (b : Fin D.R.rS) :
    (VS D).hT (f b) (rsLift (f := f) w) = 0 := by
  have hfe : ∀ a, (VS D).hT (f b) (F0.e a) = if a = b then 1 else 0 := by
    intro a
    have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [← hs, hf.1 a b]
    split_ifs <;> simp
  simp only [rsLift, map_sub, map_sum, map_smul, hfe, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

theorem rs_lift_mem (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X)
    (hw : (Submodule.Quotient.mk w : WbQ D F0) ∈ M) : rsLift (f := f) w ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (rs_lift_perp w)]
  refine ⟨?_, fun a => ?_⟩
  · rw [rs_lift_mk]
    exact hw
  · rw [rs_hT_f_lift hf w a]
    exact FractionalIdeal.zero_mem _

theorem rs_mof (hf : PartnerOK D F0 f) : Mof D F0 (lamC D F0 f M) = M := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : (VS D).V) ∈ lamC D F0 f M := hw
    exact ((rs_mem_lamC_perp w.2).1 hw').1
  · intro m hm
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨⟨rsLift (f := f) w, rs_lift_perp w⟩, rs_lift_mem hf w hm, ?_⟩
    exact rs_lift_mk w

end Flag

theorem lattice_flag_exists : LamFlag := by
  intro D u F0 f M hf hM
  exact ⟨rs_z_mem hf hM, rs_xlam hf, rs_prim hf hM, rs_mof hf⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
