import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SplitFactsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartitionSolutions.SandCpt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.QhtFacts

open UpperTheory.V.Cj.A
open Matrix NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Geo

private theorem cont_inf (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) :
    Continuous (infGL E a) := by
  have hs : Continuous (sInf E : Cinf E → Ad E) := (GlobalTheory.CuspRep.continuous_infEq E).prodMk continuous_const
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem cont_fin (E : Type) [Field E] [NumberField E] (a : ℕ) :
    Continuous (finGL E a) := by
  have hs : Continuous (sFin E : Af E → Ad E) := continuous_const.prodMk continuous_id
  exact Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map hs))

private theorem mem_out {G : Type} [Group G] (U : Subgroup G) (y : G) :
    y ∈ (fun u => Quotient.out (y : G ⧸ U) * u) '' (U : Set G) :=
  ⟨(Quotient.out (y : G ⧸ U))⁻¹ * y, QuotientGroup.eq.1 (QuotientGroup.out_eq' _), mul_inv_cancel_left _ _⟩

theorem UpperTheory.V.Cj.A.suppBwd :
    SuppBwd := by
  intro E _ _ _ a ho U hU Ξ q α w h ⟨T, K, hT, hK, hKY, hw⟩
  obtain ⟨-, hq2, hq3, -⟩ := qhtFacts E a
  have hC := (sandCpt E a).2 K hKY hK
  have hD : IsCompact (⋃ s ∈ T, (fun u => Quotient.out s * u) '' (U : Set (GL (Fin a) (Af E)))) :=
    hT.isCompact_biUnion fun s _ => hU.image (continuous_const.mul continuous_id)
  obtain ⟨B, hB⟩ := hq3 _ ((hC.prod hD).image
    (((cont_inf E a).comp continuous_fst).mul ((cont_fin E a).comp continuous_snd)))
  refine ⟨B * qht (1 : GA E a), fun X g hg => ?_⟩
  have h0 : w (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U)
      (sand (GeneralLinearGroup.map (pInf E) g) (hOne E a)) = 0 := by
    refine hw _ _ ⟨_, rfl⟩ ?_
    rintro ⟨γ, r, hr, hσ, hρ⟩
    obtain ⟨t, ht⟩ := (splitFacts E a).2 r hr
    have h1 := ((splitFacts E a).1 t).1
    refine absurd (hB 1 (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g) ?_) ?_
    · refine ⟨(GeneralLinearGroup.map (pInf E) (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g),
        GeneralLinearGroup.map (pFin E) (ratGL E a γ.1 * GlobalTheory.UnitaryBC.splitCentre E a t * g)), ⟨?_, ?_⟩,
        infGL_mul_finGL _⟩
      · rw [geo_ρ, ← map_smul, ← ht] at hρ
        simp only [Set.mem_setOf_eq, map_mul, ContinuousLinearMap.mul_apply]
        exact hρ
      · simp only [map_mul, h1, mul_one]
        refine Set.mem_biUnion hσ ?_
        have e : (geo ho U Ξ).σ γ (GeneralLinearGroup.map (pFin E) g : GL (Fin a) (Af E) ⧸ U) =
            ((GeneralLinearGroup.map (pFin E) (ratGL E a γ.1) * GeneralLinearGroup.map (pFin E) g :
              GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
        rw [e]
        exact mem_out U _
    · rw [one_mul, hq2]
      exact not_le.2 hg
  have h2 := h (GeneralLinearGroup.map (pInf E) g) (GeneralLinearGroup.map (pFin E) g) X
  rw [h0, infGL_mul_finGL] at h2
  have h3 := congrArg (fun y => Ξ.mat (GeneralLinearGroup.map (pInf E) g)⁻¹ *ᵥ y) h2
  simp only [Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec,
    ContinuousAlternatingMap.coe_zero, Pi.zero_apply, Matrix.mulVec_zero] at h3
  exact h3.symm
