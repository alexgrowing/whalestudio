import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CohomologicalCsdTemperedOfSegments
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpehShapeIffOfDiscreteSpectrum
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive

open NumberField IsDedekindDomain GlobalTheory.CuspRep

theorem UpperTheory.V.Af.pureK :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.PureK := by
  intro P K _ _ _ n hn m hm M π hπ w B hB b hb
  obtain ⟨hinf, hdual, -⟩ := hπ
  have A := P.litN.aut
  have hcsd : π.IsCsd := GlobalTheory.CsdBack.isCsd_of_paired A.fin K n π (A.gk K n π) hdual
  have hreg : (CG.mk π).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
    have h1 : (CG.mk π).HasInfChar τ (UpperTheory.V.Af.infOf m) := hinf τ
    rw [h1.infChar_eq]
    refine ⟨Finset.univ.nodup.map fun i j hij => hm.injective ?_, fun z hz => ?_⟩
    · exact_mod_cast add_left_cancel hij
    · obtain ⟨i, -, rfl⟩ := Multiset.mem_map.1 hz
      exact ⟨m i, add_comm _ _⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp A.fin K n π w
  have ht := GlobalTheory.Published.cohomologicalCsdTempered_of_caraianiTempered A.ctemp P.litN.loc.temp P.litN.loc.seg K n hn π hcsd
    (A.coh K n (by omega) π hreg) w σ hσ
  have h1 := GlobalTheory.TempSat.norm_eq_one_of_isTemperedGL ht ((GlobalTheory.BcSpehCompare.hasSat_iff hσ B).1 hB)
  obtain ⟨α, hα, rfl⟩ := Multiset.mem_map.1 hb
  obtain ⟨β, hβ, e⟩ := Multiset.mem_bind.1 hα
  obtain rfl := Multiset.mem_singleton.1 e
  rw [norm_mul, h1 β hβ, mul_one, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
