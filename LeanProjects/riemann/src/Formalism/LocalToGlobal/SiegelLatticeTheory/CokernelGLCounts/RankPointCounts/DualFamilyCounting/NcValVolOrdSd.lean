import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.SdNormHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalJacobianType.KitScale
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValVolOrdA

noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.SdW

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField IsDedekindDomain Topology Filter
open scoped TensorProduct

attribute [local instance] PI.VolStabSW.secondCountable_Fv PI.VolStabSW.locallyCompact_Fv
  PI.UnitaryGroupMassFormula.LocJacTyp.Sd.finDim

theorem boxScaleL_holds : BoxScaleL := by
  intro F E _ _ _ _ _ v ι _ hE μ _ x hx
  classical
  let z : ι → Fv F v ⊗[F] E := fun i => LocVol.sc v (x i)
  let f := PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL v z
  have hLM := PI.NglqJacSplitW.linModulusV_of
    (PI.NglqJacSplitW.linModulus_of PI.NglqJacSplitW.diagonal_one_jacobian)
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hdet : LinearMap.det f = ∏ i, x i ^ 2 := by
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.BM.det_mulL]
    refine Finset.prod_congr rfl fun i _ => ?_
    change Algebra.norm (Fv F v) (algebraMap (Fv F v) (Fv F v ⊗[F] E) (x i)) = _
    rw [Algebra.norm_algebraMap, hrank]
  have hdet0 : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hx i)
  set S := Set.univ.pi fun i : ι => {c : Fv F v ⊗[F] E | LocVol.sc v (x i) * c ∈ LocVol.OEv v} with hSdef
  have hpre : S = f ⁻¹' (Set.univ.pi fun _ : ι => LocVol.OEv v) := by
    ext y
    simp [S, f, z, PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
  have hcont : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have hS : MeasurableSet S := by
    rw [hpre]
    refine (IsOpen.preimage hcont ?_).measurableSet
    exact isOpen_set_pi Set.finite_univ fun i _ => PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_oev (E := E) v
  have himg : f '' S = Set.univ.pi fun _ : ι => LocVol.OEv v := by
    rw [hpre, Set.image_preimage_eq]
    intro y
    refine ⟨fun i => ((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i, ?_⟩
    funext i
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.BM.mulL_apply]
    change (x i ⊗ₜ[F] (1 : E)) * (((x i)⁻¹ ⊗ₜ[F] (1 : E)) * y i) = y i
    rw [← mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ (hx i), one_mul,
      ← Algebra.TensorProduct.one_def, one_mul]
  let b := Module.finBasis (Fv F v) (ι → Fv F v ⊗[F] E)
  let e0 := b.equivFun
  let e : (ι → Fv F v ⊗[F] E) ≃L[Fv F v] (Fin (Module.finrank (Fv F v) (ι → Fv F v ⊗[F] E)) → Fv F v) :=
    { e0 with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e0.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e0.symm.toLinearMap }
  have h := hLM (Fv F v) (ι → Fv F v ⊗[F] E) (Fin _) ⟨e⟩ f hdet0 μ inferInstance S hS
  have hne : (∏ i, x i ^ 2) ≠ 0 := hdet ▸ hdet0
  rw [himg, hdet, PI.UnitaryGroupMassFormula.LocJacTyp.BM.modF_Fv v _ hne, PI.UnitaryGroupMassFormula.LocJacTyp.BM.absV_prod] at h
  have hpos : ∀ i, 0 < PI.LocJacTyp.absV v (x i) := fun i => PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v (hx i)
  have hP : 0 < ∏ i, PI.LocJacTyp.absV v (x i ^ 2) :=
    Finset.prod_pos fun i _ => by rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow]; exact pow_pos (hpos i) 2
  have hR := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hP.le] at hR
  change (μ S).toReal = (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ∏ i, (PI.LocJacTyp.absV v (x i) ^ 2)⁻¹
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _ at hR
  rw [hR, Finset.prod_inv_distrib]
  simp_rw [PI.UnitaryGroupMassFormula.LocJacTyp.absV_pow] at hP ⊢
  field_simp

theorem sdFromAnn_holds : SdFromAnn := by
  intro F E _ _ _ _ _ ψ v d _ hE hd hann ι _
  classical
  have hone : (1 : Fv F v ⊗[F] E) ∈ PI.LocJacTyp.OEv v := by
    simpa using PI.UnitaryGroupMassFormula.LocJacTyp.Sd.inclR_mem (E := E) v 1
  have hrank : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
    rw [Module.finrank_baseChange]; exact hE
  have hinv : LocVol.sc v d * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1 := by
    change (d ⊗ₜ[F] (1 : E)) * (d⁻¹ ⊗ₜ[F] (1 : E)) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hd, one_mul,
      ← Algebra.TensorProduct.one_def]
  have hker : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.OpenKer v ψ := by
    refine PI.UnitaryGroupMassFormula.LocJacTyp.Sd.openKer_of v ψ (2 * d⁻¹) (mul_ne_zero two_ne_zero (inv_ne_zero hd)) ?_
    intro c hc
    have h1 := (hann (d⁻¹ ⊗ₜ[F] (1 : E))).mpr (by rw [hinv]; exact hone)
    have h2 := h1 (c • (1 : Fv F v ⊗[F] E)) (PI.UnitaryGroupMassFormula.LocJacTyp.Sd.oev_smul v hc hone)
    have htr : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E)))
        = c * (2 * d⁻¹) := by
      have : c • (1 : Fv F v ⊗[F] E) * (d⁻¹ ⊗ₜ[F] (1 : E))
          = algebraMap (Fv F v) (Fv F v ⊗[F] E) (c * d⁻¹) := by
        rw [Algebra.smul_def, mul_one, map_mul]; rfl
      rw [this, Algebra.trace_algebraMap, hrank]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      ring
    rw [← htr]; exact h2
  have hnt : ∃ r : Fv F v, psiV F ψ v r ≠ 1 := by
    by_contra hall
    push_neg at hall
    obtain ⟨t0, ht0⟩ := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_not_mem_oev (E := E) v
    have h1 := (hann ((d⁻¹ ⊗ₜ[F] (1 : E)) * t0)).mp (fun x _ => hall _)
    rw [← mul_assoc, hinv, one_mul] at h1
    exact ht0 h1
  obtain hex := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.exists_sd (E := E) v ψ hker hnt ι
  have hμ : LocVol.sdE ψ v ι = hex.choose := by
    change PI.LocJacTyp.sdE ψ v ι = _
    rw [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sdE_eq, dif_pos hex]
  have hsd := hex.choose_spec
  rw [hμ]
  haveI : hex.choose.IsAddHaarMeasure := hsd.1
  refine ⟨hsd.1, inferInstance, ?_⟩
  set μ := hex.choose
  have hDopen := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isOpen_dbox (E := E) v ψ hker ι
  have hDcpt := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.isCompact_dbox (E := E) v ψ hker hnt ι
  have htest := PI.UnitaryGroupMassFormula.LocJacTyp.Sd.sd_test v ψ ι μ hsd hDopen.measurableSet hDcpt.measure_lt_top
  have hD : PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox v ψ ι
      = Set.univ.pi fun _ : ι => {c : Fv F v ⊗[F] E | LocVol.sc v d * c ∈ LocVol.OEv v} := by
    ext y
    simp only [PI.UnitaryGroupMassFormula.LocJacTyp.Sd.Dbox, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_congr' fun i => hann (y i)
  have hbs := boxScaleL_holds v ι hE μ (fun _ => d) (fun _ => hd)
  rw [← hD] at hbs
  simp only [Measure.real] at htest
  rw [hbs] at htest
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal = _
  change (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
    ((μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal *
      ∏ _i : ι, (PI.LocJacTyp.absV v d ^ 2)⁻¹) = 1 at htest
  set a := (μ (Set.univ.pi fun _ : ι => PI.LocJacTyp.OEv v)).toReal
  have hpos : 0 < PI.LocJacTyp.absV v d := PI.UnitaryGroupMassFormula.LocJacTyp.absV_pos v hd
  rw [Finset.prod_const, Finset.card_univ] at htest
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hsq : a ^ 2 = (PI.LocJacTyp.absV v d ^ Fintype.card ι) ^ 2 := by
    have hq : 0 < ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι := by positivity
    have : a ^ 2 * ((PI.LocJacTyp.absV v d ^ 2)⁻¹) ^ Fintype.card ι = 1 := by
      rw [← htest]; ring
    rw [inv_pow, ← pow_mul] at this
    field_simp at this
    rw [this]; ring
  exact (pow_left_inj₀ ha (by positivity) two_ne_zero).mp hsq

end Formalism.L2.SG.Pf.NcVal.SdW
