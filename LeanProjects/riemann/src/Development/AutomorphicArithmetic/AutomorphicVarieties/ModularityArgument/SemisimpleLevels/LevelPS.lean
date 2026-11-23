import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAway
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.WDAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.JumpsAbove
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.GlobFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {r R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

private theorem frob_of_away (P : Hypotheses₂) (hc : Continuous R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ)))
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ) (hB : (CG.mk π).HasSat w B) :
    FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
  exact satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
    fun A h rc hrc => H w hw A h rc hrc σ hσ

private theorem iso_of_away (P : Hypotheses₂) (hr : Continuous r) (ha : AttC ι r π) (hc : Continuous R) (hs : IsSSRep R)
    (H : ∀ (w : HeightOneSpectrum (𝓞 K)), ((l : ℕ) : 𝓞 K) ∉ w.asIdeal → ∀ (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (rc : IrrGL (w.adicCompletion K) → WD h), IsRec h rc → ∀ σ, π.IsLocComp w σ → IsWDOf ι R (rc (algNorm σ))) :
    RepIso r R := by
  refine isoOfFrob P K Ω l ι n r R hr hc ha.1 hs ((ha.2.and (eventually_not_mem K l)).mono ?_)
  rintro w ⟨⟨B, h1, h2⟩, hw⟩
  exact ⟨_, h2, frob_of_away P hc H w hw B h1⟩

private theorem infOf_of_weights {m : Fin n → ℤ} {x : Multiset ℂ}
    (h : (Finset.univ.val.map fun i => -m i).map (fun k : ℤ => (k : ℂ)) = x.map fun z => ((n : ℂ) - 1) / 2 - z) :
    x = infOf m := by
  have h2 := congrArg (Multiset.map fun z : ℂ => ((n : ℂ) - 1) / 2 - z) h
  simp only [Multiset.map_map, Function.comp_def, sub_sub_cancel, Multiset.map_id'] at h2
  rw [← h2, infOf]
  exact Multiset.map_congr rfl fun i _ => by push_cast; ring

end UpperTheory.V.Lev

open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Br UpperTheory.V.Lev in
theorem UpperTheory.V.Lev.levelPS :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Lev.CompatPS → UpperTheory.V.Lev.FixedSs → UpperTheory.V.Lev.UnlGap → UpperTheory.V.Lev.LevelPS := by
  intro P hC hF hU K _ _ _ hK n hn m _ M hM l _ hl Ω _ _ _ ι r π hL hsafe hreg hd ha
  obtain ⟨η, hpol⟩ := hd
  obtain ⟨R₁, wt, HT, H₁⟩ := P.litN.aut.gal K Ω l ι n (by omega) π η hreg hpol
  have hiso := iso_of_away P hL.cont ha H₁.cont H₁.ss H₁.away
  have L₁ : LevelF l M m R₁ := ⟨H₁.cont, hL.away.of_iso hiso, fun w hw => by
    obtain ⟨A, hA, κ, χ, h1, h2, h3⟩ := hL.above w hw
    exact ⟨A, hA, κ, χ, h1, h2.of_iso hiso, h3⟩⟩
  have Hab := hC K hK n hn l Ω ι R₁ π H₁.cont hreg ⟨η, hpol⟩
    ⟨H₁.ss, ha.2.mono fun w ⟨B, h1, h2⟩ => ⟨B, h1, h2.of_iso hiso⟩⟩
  refine ⟨⟨fun φ => ?_, ⟨η, hpol⟩, ?_⟩,
    fun w hw B hB => (frob_of_away P H₁.cont H₁.away w hw B hB).of_iso hiso.symm'⟩
  · let τ : K →+* Qbar l := ι.symm.toRingHom.comp φ
    have hφ : ι.toRingHom.comp τ = φ := RingHom.ext fun x => ι.apply_symm_apply _
    obtain ⟨w, hw, hτ⟩ := GlobalTheory.GalFirstClause.existsIsInduced l K Ω τ
    obtain ⟨A, hA, κ, χ, h1, h2, h3⟩ := L₁.above w hw
    obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
    obtain ⟨τ', hτ'⟩ := hτ A hA O Bw hj
    have hJ := jumpsAbove P K Ω l hl n M hM m R₁ H₁.cont w A hA O Bw hj κ ⟨χ, h1, h2, h3⟩ τ _
      ((H₁.above _ _ (UpperTheory.V.Loc.tiedP l) w A hA O Bw hj).jumps τ _ τ' hτ')
    have hw := H₁.weights τ
    rw [hJ, hφ] at hw
    rw [← infOf_of_weights hw]
    exact ParLaws.hasInfChar_infChar (CG.mk π) φ
  · refine globFixed P K n M hM _ π.finPart π.isSmooth_finPart fun w => ?_
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    refine ⟨σ, hi σ hσ, ?_⟩
    by_cases hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal
    · obtain ⟨A, hA, κ, χ, h1, h2, h3⟩ := L₁.above w hw
      obtain ⟨O, _, _, _, Bw, hj⟩ := exists_bridge (l := l) hA hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      obtain ⟨hp, he⟩ := Hab w A hA O Bw hj
      refine hF K Ω l ι n M hM m R₁ H₁.cont w A hA O Bw hj κ ⟨χ, h1, h2, h3⟩ hp rc hrc σ (he σ hσ rc hrc) ?_
      exact hsafe.imp_right fun hg => Or.inl (hU K Ω l n M hM m R₁ w hw A hA κ ⟨χ, h1, h2, h3⟩ hg)
    · obtain ⟨A, hA, χ, h1, h2⟩ := L₁.away w hw
      obtain ⟨rc, hrc⟩ := P.exists_rec hA
      exact locFixed P K Ω n M hM w A hA rc hrc σ
        (wdAway P K Ω l ι n M hM R₁ H₁.cont w hw A hA χ h1 h2 _ (H₁.away w hw A hA rc hrc σ hσ))

end
