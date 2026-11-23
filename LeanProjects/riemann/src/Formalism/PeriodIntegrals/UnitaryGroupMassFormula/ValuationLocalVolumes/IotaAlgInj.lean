import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.BaseLatticeLeSecondIsotropic
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.DVIsDiffVal

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmX

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D)

def OmVDdTr : Prop :=
  ∀ d : 𝓞 D.host.F, d ∈ differentIdeal ℤ (𝓞 D.host.F) ↔
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)

theorem iota_alg_inj : Function.Injective (fun x : X.B.I.F => X.ιE (algebraMap X.B.I.F X.B.I.E x)) :=
  X.ιE.injective.comp (algebraMap X.B.I.F X.B.I.E).injective

theorem pre_int (d : 𝓞 D.host.F) : ∃ x : 𝓞 X.B.I.F, X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  obtain ⟨a, ha⟩ := (X.ιE_F ((d : D.host.F) : D.host.E)).1 (d : D.host.F).2
  set f : X.B.I.F →+* D.host.E := (X.ιE : X.B.I.E →+* D.host.E).comp (algebraMap X.B.I.F X.B.I.E) with hf
  have hd : IsIntegral ℤ (((d : D.host.F) : D.host.E)) :=
    (RingOfIntegers.isIntegral_coe d).map ((D.host.F).subtype : D.host.F →+* D.host.E).toIntAlgHom
  have ha' : f a = ((d : D.host.F) : D.host.E) := ha
  rw [← ha'] at hd
  have hai : IsIntegral ℤ a := (isIntegral_algHom_iff f.toIntAlgHom (iota_alg_inj X)).1 hd
  exact ⟨⟨a, (mem_integralClosure_iff ℤ _).2 hai⟩, ha⟩

theorem pow_tr (hT : OmVDdTr X) (k : ℕ) (d : 𝓞 D.host.F) (hd : d ∈ differentIdeal ℤ (𝓞 D.host.F) ^ k) :
    ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ k ∧
      X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E) := by
  induction k generalizing d with
  | zero =>
    obtain ⟨x, hx⟩ := pre_int X d
    exact ⟨x, by simp, hx⟩
  | succ k ih =>
    rw [pow_succ'] at hd
    refine Submodule.mul_induction_on
      (C := fun d : 𝓞 D.host.F => ∃ x : 𝓞 X.B.I.F, x ∈ differentIdeal ℤ (𝓞 X.B.I.F) ^ (k + 1) ∧
        X.ιE (algebraMap X.B.I.F X.B.I.E (x : X.B.I.F)) = ((d : D.host.F) : D.host.E)) hd ?_ ?_
    · intro a ha b hb
      obtain ⟨x1, hx1, e1⟩ := (hT a).1 ha
      obtain ⟨x2, hx2, e2⟩ := ih b hb
      refine ⟨x1 * x2, by rw [pow_succ']; exact Submodule.mul_mem_mul hx1 hx2, ?_⟩
      have : ((x1 * x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) * (x2 : X.B.I.F) := rfl
      rw [this, map_mul, map_mul, e1, e2]; rfl
    · rintro a b ⟨x1, hx1, e1⟩ ⟨x2, hx2, e2⟩
      refine ⟨x1 + x2, Submodule.add_mem _ hx1 hx2, ?_⟩
      have : ((x1 + x2 : 𝓞 X.B.I.F) : X.B.I.F) = (x1 : X.B.I.F) + (x2 : X.B.I.F) := rfl
      rw [this, map_add, map_add, e1, e2]; rfl

def Qi (v : PlX X) (c : Fv X.B.I.F v) : Ideal (𝓞 D.host.E) where
  carrier := {i | sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm (i : D.host.E)) ∈
    OEv (E := X.B.I.E) v}
  zero_mem' := by
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((0 : 𝓞 D.host.E) : D.host.E)) ∈
      OEv (E := X.B.I.E) v
    simp only [map_zero, mul_zero]; exact Submodule.zero_mem _
  add_mem' := by
    intro i j hi hj
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((i : D.host.E) + (j : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_add, map_add, mul_add]; exact Submodule.add_mem _ hi hj
  smul_mem' := by
    intro o i hi
    show sc (E := X.B.I.E) v c * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm ((o : D.host.E) * (i : D.host.E))) ∈
      OEv (E := X.B.I.E) v
    rw [map_mul, map_mul, mul_left_comm]
    exact oev_mul v (incl_mem v (⟨X.ιE.symm (o : D.host.E),
      (RingOfIntegers.isIntegral_coe o).map (X.ιE.symm : D.host.E →+* X.B.I.E).toIntAlgHom⟩ : 𝓞 X.B.I.E)) hi

theorem alg_int_mem (v : PlX X) (c : Fv X.B.I.F v) (hc : Valued.v c ≤ 1) :
    algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c ∈ OEv (E := X.B.I.E) v := by
  have e : algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) c =
      (⟨c, hc⟩ : v.adicCompletionIntegers X.B.I.F) • (1 : Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) := by
    rw [Algebra.smul_def, mul_one]; rfl
  rw [e]; exact Submodule.smul_mem _ _ (one_mem_oev v)

theorem ddS_pow (k : ℕ) : ddS D ^ k = ((Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
    (differentIdeal ℤ (𝓞 D.host.F) ^ k) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
  rw [Ideal.map_pow, FractionalIdeal.coeIdeal_pow]; rfl

theorem dd1 (hT : OmVDdTr X) (v : PlX X) (k : ℕ) (x : D.host.E) (hx : x ∈ ddS D ^ k) :
    sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v) (X.ιE.symm x) ∈ OEv (E := X.B.I.E) v := by
  rw [ddS_pow, FractionalIdeal.mem_coeIdeal] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  have hle : Ideal.map (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) (differentIdeal ℤ (𝓞 D.host.F) ^ k) ≤
      Qi X v ((dV v)⁻¹ ^ k) := by
    rw [Ideal.map_le_iff_le_comap]
    intro d hd
    obtain ⟨x, hx, ex⟩ := pow_tr X hT k d hd
    show sc (E := X.B.I.E) v ((dV v)⁻¹ ^ k) * inclR (F := X.B.I.F) (Fv X.B.I.F v)
      (X.ιE.symm ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E)) ∈ OEv (E := X.B.I.E) v
    have e1 : ((algebraMap (𝓞 D.host.F) (𝓞 D.host.E) d : 𝓞 D.host.E) : D.host.E) = ((d : D.host.F) : D.host.E) := rfl
    rw [e1, ← ex, RingEquiv.symm_apply_apply, ← alg_alg]
    change algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) _ * _ ∈ _
    rw [← map_mul]
    refine alg_int_mem X v _ ?_
    rw [map_mul]
    show Valued.v ((dV v)⁻¹ ^ k) * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F)) ≤ 1
    rw [map_pow, map_inv₀]
    have h1 := val_pow_le v k x hx
    have h0 : Valued.v (dV v) ≠ 0 := (Valuation.ne_zero_iff _).2 (dV_ne_zero v)
    calc (Valued.v (dV v))⁻¹ ^ k * Valued.v (algebraMap X.B.I.F (Fv X.B.I.F v) (x : X.B.I.F))
        ≤ (Valued.v (dV v))⁻¹ ^ k * Valued.v (dV v) ^ k := mul_le_mul' le_rfl h1
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ h0, one_pow]
  exact hle hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmX
