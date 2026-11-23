import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusPowerCompatibility
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.AttResTower

theorem normV_under_pow {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    (w : HeightOneSpectrum (𝓞 K')) : normV w = normV (w.under (𝓞 K)) ^ w.asIdeal.inertiaDeg (𝓞 K) := by
  have : w.asIdeal.LiesOver (w.under (𝓞 K)).asIdeal := ⟨rfl⟩
  have := w.isMaximal
  have := (w.under (𝓞 K)).isMaximal
  show Ideal.absNorm w.asIdeal = Ideal.absNorm (w.under (𝓞 K)).asIdeal ^ w.asIdeal.inertiaDeg (𝓞 K)
  rw [← Ideal.absNorm_relNorm (𝓞 K) (𝓞 K') w.asIdeal,
    Ideal.relNorm_eq_pow_of_isMaximal w.asIdeal (w.under (𝓞 K)).asIdeal, map_pow]

theorem two_le_normV {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) : 2 ≤ normV v := by
  show 2 ≤ Ideal.absNorm v.asIdeal
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  omega

theorem under_under {F K M : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Field M] [NumberField M]
    [Algebra F K] [Algebra F M] [Algebra K M] [IsScalarTower F K M] (w : HeightOneSpectrum (𝓞 M)) :
    (w.under (𝓞 K)).under (𝓞 F) = w.under (𝓞 F) := by
  apply HeightOneSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ w.asIdeal) = Ideal.comap _ w.asIdeal
  rw [Ideal.comap_comap]
  congr 1
  ext x
  first
  | exact (IsScalarTower.algebraMap_eq (𝓞 F) (𝓞 K) (𝓞 M)).symm ▸ rfl
  | (apply RingOfIntegers.coe_injective; simp only [RingHom.comp_apply, RingOfIntegers.algebraMap_coe]; exact (IsScalarTower.algebraMap_apply F K M (x : F)).symm)
  | (apply RingOfIntegers.ext; simp [IsScalarTower.algebraMap_apply F K M])

end GlobalTheory.AttResTower

theorem GlobalTheory.AttResTower.attRes_comp_res : ∀ (F Ω : Type) [Field F] [NumberField F] [IsTotallyReal F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (M : Type) [Field M] [NumberField M] [Algebra F M] [Algebra M Ω] [IsScalarTower F M Ω] [IsAlgClosure M Ω] [Algebra K M] [IsScalarTower F K M] [IsScalarTower K M Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (π : TR.CuspSub F a) (r : G K Ω →* GL (Fin a) (Qbar l)), AttRes π ι K r → AttRes π ι M (r.comp (res K Ω M)) := by
  intro F Ω _ _ _ _ _ _ K _ _ _ _ _ _ M _ _ _ _ _ _ _ _ _ l _ ι a π r hatt
  unfold AttRes at hatt ⊢
  filter_upwards [(GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.tendsto_under K M).eventually hatt] with w h f hf
  have huv := GlobalTheory.AttResTower.under_under (F := F) (K := K) w
  have h1 := GlobalTheory.AttResTower.normV_under_pow (K := F) (w.under (𝓞 K))
  have h2 := GlobalTheory.AttResTower.normV_under_pow (K := K) w
  obtain ⟨B, hB, hF⟩ := h _ h1
  rw [huv] at hB hF h1
  refine ⟨B, hB, ?_⟩
  have h3 := (UpperTheory.frobenius_power_compatibility K M Ω l ι w _ h2).1 a r _ hF
  have hff : f = (w.under (𝓞 K)).asIdeal.inertiaDeg (𝓞 F) * w.asIdeal.inertiaDeg (𝓞 K) := by
    apply Nat.pow_right_injective (GlobalTheory.AttResTower.two_le_normV (w.under (𝓞 F)))
    simp only
    rw [← hf, h2, h1, ← pow_mul]
  rw [Multiset.map_map] at h3
  rw [hff]
  convert h3 using 2
  simp [Function.comp_def, pow_mul]
