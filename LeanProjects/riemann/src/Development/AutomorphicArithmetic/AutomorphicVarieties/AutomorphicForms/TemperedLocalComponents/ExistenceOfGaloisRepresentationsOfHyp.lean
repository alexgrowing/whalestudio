import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsGalRepOfOfIso
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Af

variable {K Ω : Type} [Field K] [NumberField K] [IsCMField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {l : ℕ} [Fact l.Prime] {n : ℕ} {ι : Qbar l ≃+* ℂ} {R : G K Ω →* GL (Fin n) (Qbar l)} {π : CuspSub K n}

private theorem frob_of_galRep (P : Hypotheses₂) {χ : HChar (maximalRealSubfield K)} {wt : ℤ} {HT : (K →+* Qbar l) → Multiset ℤ}
    (H : IsGalRepOf π χ ι R wt HT) (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∉ w.asIdeal) (B : Multiset ℂˣ)
    (hB : (CG.mk π).HasSat w B) : FrobEig ι R w (algSat n (normV w) B) := by
  obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
  exact satFrob P K Ω l ι n R H.cont w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
    fun A h rc hrc => H.away w hw A h rc hrc σ hσ

private theorem exists_sign (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) :
    ∃ m : ℕ, ∀ v, χ.locInf v (-1) = (-1) ^ m := by
  obtain ⟨v⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have h2 : χ.locInf v (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e
  · exact ⟨0, fun u => (h u v).trans (Units.ext (by simpa using e))⟩
  · exact ⟨1, fun u => (h u v).trans (Units.ext (by simpa using e))⟩

end UpperTheory.V.Af

open UpperTheory.V.Af in
theorem UpperTheory.V.Af.galoisExistence_from_published :
    UpperTheory.V.Af.Hypotheses₂ → UpperTheory.V.Af.ExC := by
  intro P K Ω _ _ _ _ _ _ l _ ι n hn π χ hreg hsign hd
  obtain ⟨m, hm⟩ := exists_sign χ hsign
  have hN : compNorm K (χ * quadChar K ^ (m + n)) = compNorm K χ := by
    rw [map_mul, map_pow, compNorm_quadChar, one_pow, mul_one]
  have hpol : GlobalTheory.ContraPair.PolarizedPair π (χ * quadChar K ^ (m + n)) :=
    ⟨fun v => by
      rw [HChar.locInf_mul, locInf_pow, hm, quadChar_locInf, ← pow_add, ← add_assoc, pow_add, ← two_mul, pow_mul]
      simp, hN ▸ hd⟩
  obtain ⟨R, wt, HT, H⟩ := P.litN.aut.gal K Ω l ι n hn π _ hreg hpol
  have hsat : ∀ᶠ w : HeightOneSpectrum (𝓞 K) in Filter.cofinite, ∃ B, (CG.mk π).HasSat w B :=
    ExLib.eventually_sat (satLoc P) π.finPart π.isSmooth_finPart fun w =>
      let ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
      ⟨σ, hi σ hσ⟩
  refine ⟨_, R, wt, HT, hN, H, ⟨H.ss, (hsat.and (eventually_not_mem K l)).mono ?_⟩, fun r hr ha => ?_⟩
  · rintro w ⟨⟨B, hB⟩, hw⟩
    exact ⟨B, hB, frob_of_galRep P H w hw B hB⟩
  · refine ExLib.isGalRepOf_of_iso H ha.1
      (isoOfFrob P K Ω l ι n R r H.cont hr H.ss ha.1 ((ha.2.and (eventually_not_mem K l)).mono ?_))
    rintro w ⟨⟨B, h1, h2⟩, hw⟩
    exact ⟨_, frob_of_galRep P H w hw B h1, h2⟩

theorem UpperTheory.V.Af.exC :
    UpperTheory.V.Af.HypothesesH → UpperTheory.V.Af.ExC := fun PH => UpperTheory.V.Af.galoisExistence_from_published PH.toClassicalTheorems

end
