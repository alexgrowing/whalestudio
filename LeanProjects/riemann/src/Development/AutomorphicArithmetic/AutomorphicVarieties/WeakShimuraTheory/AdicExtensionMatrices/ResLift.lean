import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.AdicContMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicExtensionMatrices.PdMapAdj

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem res_ps {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsCO Λ (PowerSeries (ResidueField Λ))]
    (x : PowerSeries (ResidueField Λ)) :
    res Λ (PowerSeries (ResidueField Λ)) x = PowerSeries.constantCoeff x := by
  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (PowerSeries.constantCoeff x)
  have hm : x - algebraMap Λ (PowerSeries (ResidueField Λ)) a ∈
      maximalIdeal (PowerSeries (ResidueField Λ)) := by
    rw [mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, map_sub,
      PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C,
      IsLocalRing.ResidueField.algebraMap_eq, ha, sub_self]
    exact not_isUnit_zero
  have h0 := (res_eq_zero_iff Λ (PowerSeries (ResidueField Λ)) _).2 hm
  rw [map_sub, sub_eq_zero] at h0
  rw [h0, AlgHom.commutes, IsLocalRing.ResidueField.algebraMap_eq, ha]

theorem UpperTheory.V.Ws.sxResLift :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ] [IsLocalRing Λ] {a : O →+* Λ} [IsCO Λ (PowerSeries (ResidueField Λ))] (Q : PD Φ.ι Γ (ResidueField Λ)[X]), Φ.IsRes (C.comp ((residue Λ).comp a)) Q → Φ.IsRes ((residue Λ).comp a) (Q.map (evalRingHom 0)) ∧ Φ.Lifts a (Q.map (evalRingHom 0)) (Q.map (Polynomial.coeToPowerSeries.ringHom : (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ))) := by
  intro O Γ _ _ _ Φ Λ _ _ a _ Q h
  have hev : (evalRingHom (0 : ResidueField Λ)).comp (C.comp ((residue Λ).comp a)) =
      (residue Λ).comp a := by
    ext x
    simp
  have hco : (Polynomial.coeToPowerSeries.ringHom :
      (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)).comp (C.comp ((residue Λ).comp a)) =
      (algebraMap Λ (PowerSeries (ResidueField Λ))).comp a := by
    ext x
    simp [PowerSeries.algebraMap_apply, IsLocalRing.ResidueField.algebraMap_eq]
  have hcont : ∀ {R' : Type} [CommRing R'] (f : (ResidueField Λ)[X] →+* R') (J : Ideal R'),
      (Q.map f).Cont J := by
    intro R' _ f J i j
    exact adicCont_map f bot_le (h.cont i j)
  have hpt : ∀ p : (ResidueField Λ)[X],
      res Λ (PowerSeries (ResidueField Λ)) (p : PowerSeries (ResidueField Λ)) = eval 0 p := by
    intro p
    rw [res_ps, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      coeff_zero_eq_eval_zero]
  obtain ⟨_, hp1, hr1⟩ := sxPdMap (C.comp ((residue Λ).comp a)) (evalRingHom 0) Q
  obtain ⟨_, hp2, _⟩ := sxPdMap (C.comp ((residue Λ).comp a))
    (Polynomial.coeToPowerSeries.ringHom :
      (ResidueField Λ)[X] →+* PowerSeries (ResidueField Λ)) Q
  refine ⟨⟨?_, ?_, hcont _ _⟩, ⟨?_, hcont _ _, ?_⟩⟩
  · have := hp1 h.pair
    rwa [hev] at this
  · have := hr1 h.res
    rwa [hev] at this
  · have := hp2 h.pair
    rwa [hco] at this
  · apply PD.ext
    · refine MonoidHom.ext fun g => Matrix.ext fun i j => ?_
      exact hpt (Q.r g i j)
    · funext v
      refine Matrix.ext fun i j => ?_
      exact hpt (Q.n v i j)
