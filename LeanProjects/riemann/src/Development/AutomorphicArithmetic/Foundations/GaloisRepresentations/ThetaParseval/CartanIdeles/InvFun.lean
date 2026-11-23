import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import GroundTheory.GlobalFields.Artin.Places
open scoped nonZeroDivisors Matrix Pointwise
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

theorem UpperTheory.Gal.TP.Skew.invFun :
    UpperTheory.Gal.TP.Skew.InvFun := by
  intro F E _ _ _ _ _ _ m hfin hinv
  have : IsGaloisGroup Gal(E/F) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ F E
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
    intro v
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
    refine ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext ?_⟩
    rw [HeightOneSpectrum.under_asIdeal]
    exact hl.over.symm
  choose W hW using hex
  have key : ∀ w : HeightOneSpectrum (𝓞 E), m (W (w.under (𝓞 F))) = m w := by
    intro w
    have h1 : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
      ⟨by rw [HeightOneSpectrum.under_asIdeal]⟩
    have h2 : (W (w.under (𝓞 F))).asIdeal.LiesOver (w.under (𝓞 F)).asIdeal :=
      ⟨by conv_lhs => rw [← hW (w.under (𝓞 F)), HeightOneSpectrum.under_asIdeal]; rfl⟩
    obtain ⟨g, hg⟩ := Ideal.exists_smul_eq_of_isGaloisGroup (w.under (𝓞 F)).asIdeal w.asIdeal
      (W (w.under (𝓞 F))).asIdeal Gal(E/F)
    have h3 : W (w.under (𝓞 F)) = g • w := HeightOneSpectrum.ext hg.symm
    rw [h3, hinv]
  have hn : ∀ᶠ v in Filter.cofinite, m (W v) = 0 := by
    rw [Filter.eventually_cofinite] at hfin ⊢
    refine (hfin.image fun w : HeightOneSpectrum (𝓞 E) => w.under (𝓞 F)).subset fun v hv => ?_
    exact ⟨W v, hv, hW v⟩
  obtain ⟨a, ha⟩ := toFractionalIdeal_surjective (K := F) (∏ᶠ v, primeIdealUnit v ^ m (W v))
  refine ⟨a, fun w => ?_⟩
  rw [toFractionalIdeal_eq_iff.1 ha, count_finprod_primeIdealUnit_zpow _ hn, key]
