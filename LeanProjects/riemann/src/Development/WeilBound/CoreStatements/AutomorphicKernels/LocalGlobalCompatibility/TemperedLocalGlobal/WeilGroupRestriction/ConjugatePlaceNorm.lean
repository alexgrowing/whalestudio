import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains
import Development.WeilBound.CoreStatements.SatakeConjugation.CsdIff
import Development.WeilBound.CoreStatements.SatakeConjugation.ThetaTwPf
import Development.WeilBound.CoreStatements.SatakeConjugation.ConjPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSatGLOfInvT
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual GlobalTheory.CuspRep

namespace PositivityTheory.Pf1.CLGD.K

namespace ConjugatePlaceNorm

theorem satFlip : PositivityTheory.NCmp.SatFlip := by
  intro L _ _ _ a π π' T hT w B hB
  let Tθ : π.V ≃ₗ[ℂ] (GlobalTheory.ThetaPull.thetaSub π).V := (GlobalTheory.ThetaPull.pull L a).submoduleMap π.V
  have hTθ : ∀ o φ, Tθ (π.op (thetaOp o) φ) = (GlobalTheory.ThetaPull.thetaSub π).op o (Tθ φ) :=
    fun o φ => Subtype.ext (GlobalTheory.ThetaPull.act_pull o φ.1).symm
  have hI : CuspSub.Iso (GlobalTheory.ThetaPull.thetaSub π) π' := by
    refine ⟨Tθ.symm.trans T, fun o ψ => ?_⟩
    obtain ⟨φ, rfl⟩ := Tθ.surjective ψ
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, ← hTθ, LinearEquiv.symm_apply_apply,
      LinearEquiv.symm_apply_apply, hT]
  have hiso : CG.mk (GlobalTheory.ThetaPull.thetaSub π) = CG.mk π' := Quotient.sound hI
  have e : conjSrc (IsCMField.complexConj L).toRingEquiv (conjSrc (IsCMField.complexConj L).toRingEquiv w) = w :=
    GlobalTheory.ThetaPull.conjSrc_conjSrc w
  have hB' : (CG.mk π).HasSat (conjSrc (IsCMField.complexConj L).toRingEquiv
      (conjSrc (IsCMField.complexConj L).toRingEquiv w)) B := by rw [e]; exact hB
  have h1 := GlobalTheory.ThetaSatake.hasSat_thetaSub π (conjSrc (IsCMField.complexConj L).toRingEquiv w) B hB'
  rw [hiso] at h1
  exact h1

theorem complexConj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M]
    [IsCMField M] [Algebra E M] (x : E) :
    IsCMField.complexConj M (algebraMap E M x) = algebraMap E M (IsCMField.complexConj E x) := by
  obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := ⟨(Classical.arbitrary (InfinitePlace M)).embedding⟩
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  exact (IsCMField.complexEmbedding_complexConj E (φ.comp (algebraMap E M)) x).symm

theorem ringOfIntegersComplexConj_algebraMap {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M]
    [NumberField M] [IsCMField M] [Algebra E M] (x : 𝓞 E) :
    IsCMField.ringOfIntegersComplexConj M (algebraMap (𝓞 E) (𝓞 M) x) =
      algebraMap (𝓞 E) (𝓞 M) (IsCMField.ringOfIntegersComplexConj E x) := by
  apply RingOfIntegers.ext
  rw [IsCMField.coe_ringOfIntegersComplexConj]
  show IsCMField.complexConj M (algebraMap E M (x : E)) = algebraMap E M ((IsCMField.ringOfIntegersComplexConj E x : 𝓞 E) : E)
  rw [IsCMField.coe_ringOfIntegersComplexConj, complexConj_algebraMap]

theorem under_conjSrc {E M : Type} [Field E] [NumberField E] [IsCMField E] [Field M] [NumberField M] [IsCMField M]
    [Algebra E M] (w : HeightOneSpectrum (𝓞 M)) :
    (conjSrc (PositivityTheory.NCmp.cc M) w).under (𝓞 E) = conjSrc (PositivityTheory.NCmp.cc E) (w.under (𝓞 E)) := by
  refine HeightOneSpectrum.ext (Ideal.ext fun x => ?_)
  rw [PositivityTheory.NCmp.mem_conjSrc_iff, HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal, Ideal.mem_under,
    Ideal.mem_under, PositivityTheory.NCmp.mem_conjSrc_iff, ringOfIntegersComplexConj_algebraMap]

theorem normV_eq_absNorm' {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) :
    normV w = Ideal.absNorm w.asIdeal := by
  rw [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem normV_conjSrc {L : Type} [Field L] [NumberField L] [IsCMField L] (w : HeightOneSpectrum (𝓞 L)) :
    normV (conjSrc (PositivityTheory.NCmp.cc L) w) = normV w := by
  rw [normV_eq_absNorm', normV_eq_absNorm']
  exact GlobalTheory.ThetaSatake.absNorm_cw w

theorem exists_normV_under {E M : Type} [Field E] [NumberField E] [Field M] [NumberField M] [Algebra E M]
    (w : HeightOneSpectrum (𝓞 M)) : ∃ f : ℕ, normV w = normV (w.under (𝓞 E)) ^ f := by
  classical
  have hcomap : (w.under (𝓞 E)).asIdeal = w.asIdeal.comap (algebraMap (𝓞 E) (𝓞 M)) := rfl
  have := (w.under (𝓞 E)).isMaximal
  have := w.isMaximal
  let _ := Ideal.Quotient.field (w.under (𝓞 E)).asIdeal
  let _ := Ideal.Quotient.field w.asIdeal
  have : Finite (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal) :=
    (w.under (𝓞 E)).asIdeal.finiteQuotientOfFreeOfNeBot (w.under (𝓞 E)).ne_bot
  have : Finite (𝓞 M ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  let _ := Fintype.ofFinite (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal)
  let _ := Fintype.ofFinite (𝓞 M ⧸ w.asIdeal)
  let _ : Algebra (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal) (𝓞 M ⧸ w.asIdeal) :=
    (Ideal.quotientMap w.asIdeal (algebraMap (𝓞 E) (𝓞 M)) hcomap.le).toAlgebra
  refine ⟨Module.finrank (𝓞 E ⧸ (w.under (𝓞 E)).asIdeal) (𝓞 M ⧸ w.asIdeal), ?_⟩
  rw [normV, normV, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Module.card_eq_pow_finrank

theorem hasSat_conj {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ} (π : CuspSub L a) (hc : π.IsCsd)
    (w : HeightOneSpectrum (𝓞 L)) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) :
    (CG.mk π).HasSat (conjSrc (PositivityTheory.NCmp.cc L) w) (B.map (·⁻¹)) :=
  PositivityTheory.NCmp.sat_conj_of_isCsd satFlip (CG.mk π) hc w B hB

theorem map_inv_pow (B : Multiset ℂˣ) (f : ℕ) :
    (B.map (·⁻¹)).map (· ^ f) = (B.map (· ^ f)).map (·⁻¹) := by
  rw [Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun u _ => (inv_pow u f).symm

end ConjugatePlaceNorm

open ConjugatePlaceNorm in
theorem conjugate_place_norm_under : InfinitePlaceStep := by
  intro hJ E Ω _ _ _ _ _ _ a ha π X P
  refine ⟨fun hc hP => ?_, fun hr hi => ?_⟩
  · have hP' := ((conjSrc_injective (PositivityTheory.NCmp.cc X.M)).tendsto_cofinite).eventually hP
    refine PositivityTheory.NCmp.isCsd_of_sat satFlip PositivityTheory.NCmp.thetaTw hJ ha (CG.mk P) ((hP.and hP').mono ?_)
    rintro w ⟨h1, h2⟩
    obtain ⟨f, hf⟩ := exists_normV_under (E := E) w
    obtain ⟨B, hB, hPB⟩ := h1 f hf
    have hf' : normV (conjSrc (PositivityTheory.NCmp.cc X.M) w) =
        normV ((conjSrc (PositivityTheory.NCmp.cc X.M) w).under (𝓞 E)) ^ f := by
      rw [under_conjSrc, normV_conjSrc, normV_conjSrc, hf]
    obtain ⟨B', hB', hPB'⟩ := h2 f hf'
    rw [under_conjSrc] at hB'
    have e : B' = B.map (·⁻¹) := CG.HasSat.unique hB' (hasSat_conj π hc _ B hB)
    refine ⟨B.map (· ^ f), hPB, ?_⟩
    rw [← map_inv_pow, ← e]
    exact hPB'
  · refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun τ => ?_
    have h1 := hi τ _ (GlobalTheory.CuspRep.ParLaws.hasInfChar_infChar (CG.mk π) (τ.comp (algebraMap E X.M)))
    have e : (CG.mk P).infChar τ = (CG.mk π).infChar (τ.comp (algebraMap E X.M)) :=
      CG.HasInfChar.infChar_eq (π := CG.mk P) h1
    rw [e]
    exact hr _

end PositivityTheory.Pf1.CLGD.K

end
