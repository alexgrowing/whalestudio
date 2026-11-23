import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.MonoOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsMonoOdd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CountRankThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.SsCalcP
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.IsoOfFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompC
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SatFrob
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.ExistenceOfGaloisRepresentationsOfHyp
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.ExtReal
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.SignFix
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.CsdTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.UntwistS
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.GaloisRepIrreducibilityCriterion
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeLAdicCharacterAndPrincipalIdealSt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Lev

private theorem monodromy_zero_of_dim_one {K Ω : Type} [Field K] [NumberField K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 K)} {h : IsPlaceOver A w} (x : WD h) (hx : x.lpDim = 1) : x.mono0 := by
  obtain ⟨n, b, rfl⟩ := WD.exists_rep x
  obtain rfl : n = 1 := by simpa using hx
  refine (WD.monodromyZero_ofWeilDeligneRepClass_iff b).2 ?_
  have h1 := (LinearMap.isNilpotent_iff_charpoly b.N).1 b.nilpotent
  have h2 := LinearMap.aeval_self_charpoly b.N
  rw [h1] at h2
  simpa using h2

theorem monoOddOf : UpperTheory.V.Af.Hypotheses₂ → CsdMonoOdd → MonoOdd := by
  intro P hS K _ _ _ n hodd l _ Ω _ _ _ ι r π hr hreg hd ha w A h ⟨O, _, _, _, Bw, hj, hpc⟩ σ hσ rc hrc
  rcases (show n = 1 ∨ 2 ≤ n by obtain ⟨k, rfl⟩ := hodd; omega) with rfl | hn
  · refine monodromy_zero_of_dim_one _ ?_
    rw [rec_algNorm hrc, WD.lpDim_tw]
    obtain ⟨a, ha, ε, -, H⟩ := hrc
    exact H.dim _
  obtain ⟨R, hc, hs, Haw, Hab⟩ := hS K Ω l ι n hn hodd π hd (P.litN.aut.coh K n (by omega) π hreg)
  obtain ⟨p, hp⟩ : RepIso R r := by
    refine isoOfFrob P K Ω l ι n R r hc hr hs ha.1 ?_
    filter_upwards [ha.2, eventually_not_mem K l] with w ⟨B, hB, hf⟩ hw
    obtain ⟨⟨σ, hσ⟩, hi⟩ := locCompC P K n π w
    exact ⟨_, satFrob P K Ω l ι n R hc w hw σ B (((satLoc P K n w σ).2 _ π.finPart (hi σ hσ) B).1 hB)
      fun A h rc hrc => Haw w hw A h rc hrc σ hσ, hf⟩
  have h1 := Hab _ _ (Loc.tiedP l) w A h O Bw hj
  have h3 := GlobalTheory.PstConj.main K Ω l ι n _ _ (Loc.tiedP l) w A h O Bw hj (R.comp (Dec (F := K) A).subtype)
    (r.comp (Dec (F := K) A).subtype) p (fun g => hp g.1) h1.1
  refine h1.2 σ hσ rc hrc ?_
  rw [← h3.2]
  exact (GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj _ ι _ h3.1).2 hpc

theorem monoOdd (P : UpperTheory.V.Af.Hypotheses₂) : MonoOdd := monoOddOf P P.mono

end UpperTheory.V.Lev

end
