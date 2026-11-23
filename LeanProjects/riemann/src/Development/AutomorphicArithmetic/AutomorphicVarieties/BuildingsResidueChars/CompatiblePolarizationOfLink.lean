import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GuDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.Untwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdanStatement
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ConclusionAbsPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Gu

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem regAlg_twist {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] {n : ℕ} {P : CuspSub K n}
    (h : (CG.mk P).IsRegAlg) {κ : HChar K} {m : (K →+* ℂ) → ℤ} (hκ : κ.IsAlg m) : (CG.mk (P.twist κ)).IsRegAlg := (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => by
  have e := ((ParLaws.hasInfChar_infChar (CG.mk P) τ).twist κ).infChar_eq
  rw [CG.twist_mk] at e
  rw [e, (InfType.expo_of_infType K κ).1 m hκ τ]
  refine ⟨(h τ).1.map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := (h τ).2 y hy
  exact ⟨k + m τ, by push_cast; ring⟩

theorem UpperTheory.compatible_polarization_of_link :
    HypothesesH → CompatCsd → SatLink → CompatPol := by
  intro PH hC hS E Ω _ _ _ _ _ _ l _ ι a ha P χ ξ m hreg hpol hξ hd σ hσ
  have Pr := PH.toClassicalTheorems
  obtain ⟨r, wt, HT, H⟩ := (GlobalTheory.T.local_global_of_gelfand_kazhdan Pr.litN.aut.gk).2 Pr.litN.aut.gal E Ω l ι a ha P χ hreg hpol
  have hatt : AttC ι r P := by
    refine ⟨H.ss, (((hS E a P).2).and (eventually_not_mem E l)).mono ?_⟩
    rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, satFrob Pr E Ω l ι a r H.cont w hw (σ w) B (((hS E a P).1 w _ (hσ w) B).1 hB)
      fun A h rc hrc => H.away w hw A h rc hrc _ (hσ w)⟩
  obtain ⟨art, hart⟩ := Pr.litN.aut.art E Ω
  obtain ⟨μ, hμc, hμ⟩ := hart.exists_isLAdicOf ι (isAlgPos_of_isAlg hξ)
  have hL := hC E Ω l ι a ha (tw r μ) (P.twist ξ) (UpperTheory.galoisRep_irreducibility_criterion.2 _ _ a _ μ H.cont hμc) (regAlg_twist hreg hξ) hd
    (Cq.attTwist E Ω l ι a r P hatt art ξ m μ hart hμ)
  obtain ⟨T⟩ := Loc.tiedP l
  refine ⟨r, HT, ⟨H.cont, H.ss, fun w A h O _ _ _ Bw hj => ?_, fun w A h rc hrc => ⟨fun hw => ?_, fun O _ _ _ Bw hj => ?_⟩⟩,
    H.weights⟩
  · exact ⟨(H.above _ _ ⟨T⟩ w A h O Bw hj).deRham, (H.above _ _ ⟨T⟩ w A h O Bw hj).jumps⟩
  · exact H.away w hw A h rc hrc _ (hσ w)
  · have hpst : IsPstAt (Loc.PP l) Bw (r.comp (Dec (F := E) A).subtype) :=
      Pr.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (H.cont.comp continuous_subtype_val))
        (H.above _ _ ⟨T⟩ w A h O Bw hj).deRham
    obtain ⟨c1, c2⟩ := (hL w _ ((hσ w).twist ξ) A h rc hrc).2 O Bw hj
    exact ⟨hpst, Lev.untwistS Pr.litN.aut.chA Pr.litN.aut.chW Pr.litN.aut.berger E Ω l ι a r H.cont art ξ m μ hart
      (isAlgPos_of_isAlg hξ) hμc hμ w A h O Bw hj hpst c1 (σ w) rc hrc c2⟩
