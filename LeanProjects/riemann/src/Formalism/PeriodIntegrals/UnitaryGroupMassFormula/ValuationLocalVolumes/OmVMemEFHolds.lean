import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.OmVPrimOfTrX

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

theorem mem_diff_iff {K : Type} [Field K] [NumberField K] (x : 𝓞 K) :
    x ∈ differentIdeal ℤ (𝓞 K) ↔ ∀ y : K, (∀ a : 𝓞 K, Algebra.trace ℚ K (y * a) ∈ (algebraMap ℤ ℚ).range) →
      IsIntegral ℤ ((x : K) * y) := by
  have h1 : x ∈ differentIdeal ℤ (𝓞 K) ↔ (x : K) ∈ IsLocalization.coeSubmodule K (differentIdeal ℤ (𝓞 K)) := by
    rw [IsLocalization.mem_coeSubmodule]
    constructor
    · intro h; exact ⟨x, h, rfl⟩
    · rintro ⟨x', hx', he⟩
      have : x' = x := Subtype.ext he
      rwa [← this]
  rw [h1, coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem]
  constructor
  · intro h y hy
    have h2 := h y (by
      rw [Submodule.mem_traceDual]
      intro a ha
      obtain ⟨a', rfl⟩ := Submodule.mem_one.1 ha
      simpa [Algebra.traceForm_apply] using hy a')
    obtain ⟨b, hb⟩ := Submodule.mem_one.1 h2
    rw [← hb]
    exact RingOfIntegers.isIntegral_coe b
  · intro h y hy
    rw [Submodule.mem_traceDual] at hy
    have hint := h y (fun a => by simpa [Algebra.traceForm_apply] using hy _ (Submodule.mem_one.2 ⟨a, rfl⟩))
    exact Submodule.mem_one.2 ⟨⟨_, (mem_integralClosure_iff ℤ K).2 hint⟩, rfl⟩

theorem diff_map {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : K ≃+* K')
    (x : 𝓞 K) (x' : 𝓞 K') (hxx : e (x : K) = (x' : K')) (hx : x ∈ differentIdeal ℤ (𝓞 K)) :
    x' ∈ differentIdeal ℤ (𝓞 K') := by
  rw [mem_diff_iff] at hx ⊢
  intro y' hy'
  have htr : ∀ z : K, Algebra.trace ℚ K' (e z) = Algebra.trace ℚ K z := fun z =>
    Algebra.trace_eq_of_algEquiv e.toRatAlgEquiv z
  have hy : ∀ a : 𝓞 K, Algebra.trace ℚ K (e.symm y' * a) ∈ (algebraMap ℤ ℚ).range := by
    intro a
    have hi : IsIntegral ℤ (e (a : K)) := (RingOfIntegers.isIntegral_coe a).map (e : K →+* K').toIntAlgHom
    have h3 := hy' ⟨e a, (mem_integralClosure_iff ℤ K').2 hi⟩
    rw [← htr, map_mul, RingEquiv.apply_symm_apply]
    exact h3
  have h4 := (hx _ hy).map (e : K →+* K').toIntAlgHom
  change IsIntegral ℤ (e ((x : K) * e.symm y')) at h4
  rwa [map_mul, RingEquiv.apply_symm_apply, hxx] at h4

variable {D : D7} (X : HidaSetting D)

def eF : X.B.I.F ≃+* D.host.F :=
  RingEquiv.ofBijective
    (((X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E)).codRestrict D.host.F
      (fun a => (X.ιE_F _).2 ⟨a, rfl⟩))
    ⟨fun a b h => iota_alg_inj X (congrArg Subtype.val h), fun y => by
      obtain ⟨a, ha⟩ := (X.ιE_F (y : D.host.E)).1 y.2
      exact ⟨a, Subtype.ext ha⟩⟩

theorem eF_val (a : X.B.I.F) : ((eF X a : D.host.F) : D.host.E) = X.ιE (algebraMap X.B.I.F X.B.I.E a) := rfl

theorem omVDdTr_holds : OmVDdTr X := by
  intro d
  constructor
  · intro hd
    obtain ⟨x, hx⟩ := pre_int X d
    refine ⟨x, diff_map (eF X).symm d x ?_ hd, hx⟩
    rw [RingEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [eF_val]; exact hx.symm)
  · rintro ⟨x, hx, hxd⟩
    exact diff_map (eF X) x d (Subtype.ext (by rw [eF_val]; exact hxd)) hx

theorem omVDdLoc_holds : OmVDdLoc X := omVDdLoc_of X (omVDdTr_holds X)

variable (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem omVPrim_holds : OmVPrim X u' := omVPrim_of_dd X u' (omVDdLoc_holds X)

theorem omVPrim_holdsX : Formalism.L2.SG.Pf.NcX.OmVSt.OmVPrim X u' := omVPrim_holds X u'

theorem omV_of_rest (hScale : OmVScale X u' ψ) (hBad : OmVBadT X u' ψ) (hLocU : OmVLocU X ψ) :
    Formalism.L2.SG.Pf.NcVal.OmV X u' ψ :=
  omV_of_dd X u' ψ (omVDdLoc_holds X) hScale hBad hLocU

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
