import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SstConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

private theorem galRepOfR_iso (P : Hypotheses₂) {F Ω : Type} [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {n : ℕ} {π : TR.CuspSub F n}
    {r r' : G F Ω →* GL (Fin n) (Qbar l)} {wt : ℤ} {HT : (F →+* Qbar l) → Multiset ℤ} (H : IsGalRepOfR π ι r wt HT)
    (hs : IsSSRep r') (hi : RepIso r r') : IsGalRepOfR π ι r' wt HT := by
  obtain ⟨p, hp⟩ := id hi
  refine ⟨continuous_of_iso H.cont hi, hs, fun w hw A h rc hrc σ hσ => ?_, fun w hw A h => ?_, H.weights, H.weights_sym,
    fun Q AI hT w A h O _ _ _ Bw hj => ?_⟩
  · exact (H.away w hw A h rc hrc σ hσ).of_conj hw p fun g => by rw [hp, inv_mul_cancel_right]
  · obtain ⟨x, h1, h2⟩ := H.pure w hw A h
    exact ⟨x, h1.of_conj hw p fun g => by rw [hp, inv_mul_cancel_right], h2⟩
  · obtain ⟨h1, h2, h3, h4⟩ := H.above Q AI hT w A h O Bw hj
    have hc : ∀ g : ↥(Dec (F := F) A), r'.comp (Dec (F := F) A).subtype g =
        p * r.comp (Dec (F := F) A).subtype g * p⁻¹ := fun g => hp g
    obtain ⟨k1, k2, -, k4⟩ := GlobalTheory.T.padicHodgeProperties_conj_invariant l Q F Ω O _ Bw n _ _ p hc
    refine ⟨k1 h1, fun τ LL' τ' hτ => k4 τ _ (h2 τ LL' τ' hτ), fun σ hσ hI => ⟨isSstAt_conj Q Bw p hc (h3 σ hσ hI).1,
      fun rc hrc => ?_⟩, fun σ hσ hS => k2 (h4 σ hσ hS)⟩
    obtain ⟨T⟩ := hT
    exact (GlobalTheory.PstConj.main F Ω l ι n Q AI ⟨T⟩ w A h O Bw hj _ _ p hc
      (P.litN.aut.berger.isPstAt T Bw _ (Units.continuous_val.comp (H.cont.comp continuous_subtype_val)) h1)).2.trans
      ((h3 σ hσ hI).2 rc hrc)

end UpperTheory.V.Af

theorem UpperTheory.V.Af.realExistence_from_published :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.ExR := by
  intro P F Ω _ _ _ _ _ _ l _ ι n _ hn π χ hreg hpol
  obtain ⟨r, wt, HT, H⟩ := P.galR F Ω l ι n hn π χ hreg hpol
  have key : ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ B, π.HasSat w B →
      FrobEig ι r w (algSat n (normV w) B) := fun w hw B hB => by
    obtain ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
    exact satFrob P F Ω l ι n r H.cont w hw σ B (((satLoc P F n w σ).2 _ π.finPart (hiso σ hσ) B).1 hB)
      fun A h rc hrc => H.away w hw A h rc hrc σ hσ
  have hsm : GlobalTheory.PRep.IsSmooth π.finPart := fun v => by
    convert (π.cusp v.1 v.2).1.level using 1
    ext k
    exact Subtype.ext_iff
  have : Nontrivial π.V := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  refine ⟨r, wt, HT, H, ⟨H.ss, ?_⟩, fun r' hr' ha => galRepOfR_iso P H ha.1 ?_⟩
  · filter_upwards [sat_ae_of_smooth (satLoc P) π.finPart hsm fun w =>
      let ⟨⟨σ, hσ⟩, hiso⟩ := locCompR P F n π w
      ⟨σ, hiso σ hσ⟩, eventually_not_mem F l] with w ⟨B, hB⟩ hw
    exact ⟨B, hB, key w hw B hB⟩
  · refine isoOfFrob P F Ω l ι n r r' H.cont hr' H.ss ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem F l] with w ⟨B, hB, hf⟩ hw
    exact ⟨_, key w hw B hB, hf⟩

theorem UpperTheory.V.Af.exR :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.ExR := fun PH => UpperTheory.V.Af.realExistence_from_published PH.toClassicalTheorems

end
