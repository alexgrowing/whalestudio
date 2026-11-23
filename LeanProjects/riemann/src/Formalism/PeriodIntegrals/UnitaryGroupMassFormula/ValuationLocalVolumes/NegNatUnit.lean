import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.HRSmulERight

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.OmVSt.OmW

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  NumberField IsDedekindDomain Matrix
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word)

theorem negNat_unit (v : PlX X) (T : ℕ) (hT : ((T : ℕ) : 𝓞 X.B.I.F) ∉ v.asIdeal) :
    ∃ u ∈ OEv (E := X.B.I.E) v, inclR (Fv X.B.I.F v) (-((T : ℕ) : X.B.I.E)) * u = 1 := by
  set t : Fv X.B.I.F v := ((T : ℕ) : Fv X.B.I.F v) with ht_def
  have hv1 : Valued.v t = 1 := val_natCast_eq_one v _ hT
  have ht0 : t ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv1; exact zero_ne_one hv1
  have hti : t⁻¹ ∈ v.adicCompletionIntegers X.B.I.F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv1, inv_one]
  refine ⟨(⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E),
    Submodule.smul_mem _ _ (inclR_mem_OEv X v _), ?_⟩
  have e1 : (⟨t⁻¹, hti⟩ : v.adicCompletionIntegers X.B.I.F) • inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) =
      algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) t⁻¹ *
        inclR (Fv X.B.I.F v) (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) := by
    rw [← Algebra.smul_def]; rfl
  rw [e1, mul_left_comm, ← map_mul]
  have e2 : (-((T : ℕ) : X.B.I.E)) * (((-1 : ℤ) : 𝓞 X.B.I.E) : X.B.I.E) = ((T : ℕ) : X.B.I.E) := by
    push_cast; ring
  rw [e2, map_natCast, ← map_natCast (algebraMap (Fv X.B.I.F v) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)), ← map_mul,
    inv_mul_cancel₀ ht0, map_one]

theorem zi_val : (zi (D := D)).val = D.R.rS := by simp [zi]

theorem hR_comb (v : PlX X) (c : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)
    (j : Fin (D.R.rS + 1 + D.R.rS)) :
    hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v j) (∑ i, c i • yTup X u' v i) =
      c (piv D.R.rS j) * inclR (Fv X.B.I.F v) (cD X u' j) := by
  rw [hR_sum_right]
  have hg : ∀ i, hR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v j) (yTup X u' v i) =
      inclR (Fv X.B.I.F v) (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u')) j i) := fun i =>
    congrFun (congrFun (omVGram_holds X u' v) j) i
  simp only [hR_smulE_right, hg, gramE_entry, apply_ite (inclR (Fv X.B.I.F v)), map_zero, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem omVPrim_of (hM : OmVMem X u') (hZ : OmVZPrim X u') : OmVPrim X u' := by
  intro v
  refine ⟨hM v, fun c hc => ?_⟩
  have hne : ∀ i, i ≠ zi (D := D) → c i ∈ OEv (E := X.B.I.E) v := by
    intro i hi
    have hj : piv D.R.rS (piv D.R.rS i) = i := piv_invol D.R.rS i
    have hjz : (piv D.R.rS i).val ≠ D.R.rS := by
      intro h
      apply hi
      have : piv D.R.rS i = zi (D := D) := Fin.ext (by rw [h, zi_val])
      rw [← hj, this, pivot_castAdd_last]
    have h1 := hR_comb X u' v c (piv D.R.rS i)
    rw [hj, cD, if_neg hjz, map_one, mul_one] at h1
    rw [← h1]
    exact omVSD_fwd X v (hM v _) hc
  intro i
  by_cases hi : i = zi (D := D)
  · subst hi
    have hz : c (zi (D := D)) • yTup X u' v (zi (D := D)) ∈ latLoc (E := X.B.I.E) v (abelian₂ X) := by
      have e : c (zi (D := D)) • yTup X u' v (zi (D := D)) =
          (∑ i, c i • yTup X u' v i) - ∑ i ∈ Finset.univ.erase (zi (D := D)), c i • yTup X u' v i := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (zi (D := D))), add_sub_cancel_right]
      rw [e]
      refine Submodule.sub_mem _ hc (Submodule.sum_mem _ fun i hi => lat_oev_smul X v ?_ (hM v i))
      exact hne i (Finset.ne_of_mem_erase hi)
    by_cases hT : ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal
    · exact hZ v hT _ hz
    · obtain ⟨u, hu, hu1⟩ := negNat_unit X v (Tw u') hT
      have h1 := hR_comb X u' v c (zi (D := D))
      rw [pivot_castAdd_last, cD, if_pos zi_val] at h1
      have h2 : c (zi (D := D)) * inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E)) ∈ OEv (E := X.B.I.E) v := by
        rw [← h1]; exact omVSD_fwd X v (hM v _) hc
      have h3 : c (zi (D := D)) = (c (zi (D := D)) * inclR (Fv X.B.I.F v) (-((Tw u' : ℕ) : X.B.I.E))) * u := by
        rw [mul_assoc, hu1, mul_one]
      rw [h3]
      exact oev_mul v h2 hu
  · exact hne i hi

end Formalism.L2.SG.Pf.NcVal.OmVSt.OmW
