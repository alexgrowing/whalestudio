import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUArith
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolULeaf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUTr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolumeDeepCongruenceOfFubini

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace VolUT

section V

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_int (x : 𝓞 F) : Valued.v (algebraMap F (Fv F v) (x : F)) ≤ 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F x)
  rw [HeightOneSpectrum.valuation_of_algebraMap] at h
  have h' : Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := h
  rw [h']
  exact v.intValuation_le_one x

theorem val_unit (x : 𝓞 F) (hx : x ∉ v.asIdeal) : Valued.v (algebraMap F (Fv F v) (x : F)) = 1 := by
  have h := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 F) v (algebraMap (𝓞 F) F x)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hx] at h
  exact h

theorem val_dV (h : ¬ (differentIdeal ℤ (𝓞 F) ≤ v.asIdeal)) : Valued.v (dV v) = 1 := by
  obtain ⟨y, hy, hyv⟩ := Set.not_subset.1 h
  unfold dV
  split_ifs with hd
  · obtain ⟨-, hle, x, hx, hxe⟩ := hd.choose_spec
    have h1 := hle y hy
    rw [val_unit v y hyv] at h1
    rw [← hxe] at h1 ⊢
    exact le_antisymm (val_int v x) h1
  · exact map_one _

theorem absV_of_val_one {x : Fv F v} (h : Valued.v x = 1) : absV v x = 1 := by
  unfold absV
  rw [dif_neg (by rw [h]; exact one_ne_zero)]
  have : WithZero.unzero (show Valued.v x ≠ 0 by rw [h]; exact one_ne_zero) = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [this]
  simp

theorem absV_g (g : ℕ) (hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = g) (hg1 : (g : 𝓞 F) ∈ v.asIdeal)
    (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) : absV v (g : Fv F v) = (g : ℝ)⁻¹ := by
  have hv := VolUAr.val_natCast_of v g hg1 hg2
  have e1 : ((g : v.adicCompletionIntegers F) : v.adicCompletion F) = (g : Fv F v) := by simp
  rw [e1] at hv
  unfold absV
  rw [dif_neg (by rw [hv]; exact WithZero.coe_ne_zero)]
  have hu : WithZero.unzero (show Valued.v (g : Fv F v) ≠ 0 by rw [hv]; exact WithZero.coe_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, hv]
    rfl
  rw [hu, toAdd_ofAdd, Ideal.absNorm_apply, Submodule.cardQuot_apply, hcard, zpow_neg, zpow_one]

end V

section X

variable {D : D7} (X : HidaSetting D)

theorem gAt_mem (v : PlX X) (hv : TypAt X v) : ((gAt X v : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal := by
  have hty := (mem_typSet X.B.I.F (D.host.g 0) (D.host.g 1) (D.host.g_prime 0).ne_zero
    (D.host.g_prime 1).ne_zero v).1 hv
  unfold gAt
  split_ifs with h
  · exact h
  · exact hty.resolve_left h

theorem gAt_split (v : PlX X) : {w : HeightOneSpectrum (𝓞 X.B.I.E) |
    ((gAt X v : ℕ) : 𝓞 X.B.I.E) ∈ w.asIdeal}.ncard = Module.finrank ℚ X.B.I.E := by
  unfold gAt
  split_ifs
  · exact VolUAr.split_transport X.ιE _ (D.nd.g_split 0)
  · exact VolUAr.split_transport X.ιE _ (D.nd.g_split 1)

theorem typ_arith (v : PlX X) (hv : TypAt X v) :
    absV v (gAt X v : Fv X.B.I.F v) = (gAt X v : ℝ)⁻¹ ∧ Valued.v (dV v) = 1 ∧ absV v (dV v) = 1 := by
  haveI : Fact (gAt X v).Prime := ⟨gAt_prime X v⟩
  have hmem := gAt_mem X v hv
  obtain ⟨he, hf⟩ := VolUAr.locDeg_one_below (F := X.B.I.F) (E := X.B.I.E) (gAt X v) (gAt_split X v) v hmem
  obtain ⟨hc, hn⟩ := VolUAr.arith_of_loc (gAt X v) v hmem he hf
  have hun : Algebra.IsUnramifiedAt ℤ v.asIdeal :=
    (Algebra.isUnramifiedAt_iff_of_isDedekindDomain (R := ℤ) (S := 𝓞 X.B.I.F) (p := v.asIdeal)).2 he
  have hnd : ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 X.B.I.F) := not_dvd_differentIdeal_iff.mpr hun
  rw [Ideal.dvd_iff_le] at hnd
  have hval := val_dV v hnd
  exact ⟨absV_g v (gAt X v) hc hmem hn, hval, absV_of_val_one v hval⟩

end X

end VolUT

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem volU_steps_of (hC : CondAll) (hψ : IsCharAF X.B.I.F ψ) (hs : IsStdChar ψ) (v : PlX X) (hv : TypAt X v)
    (hH : VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS) (hT : VolTTFCong X u u' v) : VolUSteps X u u' ψ v := by
  obtain ⟨hg, hdv, hd⟩ := VolUT.typ_arith X v hv
  have hann : VolUL.AnnAt (E := X.B.I.E) ψ v := VolUTr.annX_of X ψ hC hψ hs v
  have hfin := X.B.I.cm.deg2
  have hg0 : gAt X v ≠ 0 := (gAt_prime X v).ne_zero
  exact ⟨VolUL.volTAff_of ψ v hψ hfin hann hd hg0 hg _, VolUL.volTLocPres_of ψ v hψ hfin hann hd _, hH, hT,
    volTUOEq_of v hdv hg0 _, VolUL.volTProdU_of' ψ v hψ hfin hann hd hg0 hg _,
    (VolUL.sd_facts ψ v hψ hfin hann hd _).2.2⟩

theorem volTypV_of_cnt (hC : CondAll)
    (hH : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS)
    (hT : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTTFCong X u u' v) : VolTypV X u u' ψ :=
  volTypV_of_steps' X u u' ψ fun hh v hv =>
    volU_steps_of X u u' ψ hC hh.1 hh.2.1 v hv (hH hh v hv) (hT hh v hv)

end OfX

end Formalism.L2.SG.Pf.NcVal
