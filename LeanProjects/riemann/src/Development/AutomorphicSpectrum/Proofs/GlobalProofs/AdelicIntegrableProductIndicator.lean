import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IntegralIndicatorCharOfTrivial
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CharEqOneOfNear
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.SelfDualMap
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test

theorem integral_pure_indicator_char : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (db : Measure (AF F)) (laminf : Measure (Ainf F)) (lf : Measure (Af F)), laminf.IsAddHaarMeasure → lf.IsAddHaarMeasure → ∀ e : (Ainf F × Af F) ≃ᵐ AF F, (∀ p, e p = pairA F p.1 p.2) → MeasurePreserving e (laminf.prod lf) db → ∀ (g : Ainf F → ℂ) (B : AddSubgroup (Af F)), MeasurableSet (B : Set (Af F)) → lf (B : Set (Af F)) ≠ ⊤ → ∀ b : AF F, ∫ y, (g (fstA F y) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F y)) * ψ (y * b) ∂db = (∫ x, g x * psiInf F ψ (x * fstA F b) ∂laminf) * ((lf (B : Set (Af F))).toReal : ℂ) * (annF ψ (B : Set (Af F))).indicator (fun _ => (1 : ℂ)) (sndA F b) := by
  intro F _ _ ψ _ db laminf lf hl hf e he hmp g B hB hfin b
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.1
  haveI : SecondCountableTopology (Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).2.2.1
  haveI : SecondCountableTopology (Ainf F) := by
    haveI : SecondCountableTopology (Ainf F × Af F) := (GlobalTheory.CompanionTheory.AdeleTop.adele_top F).1.2.1
    exact (Topology.IsEmbedding.of_comp (f := fun x : Ainf F => (x, (0 : Af F))) (g := Prod.fst)
      (by fun_prop) continuous_fst Topology.IsEmbedding.id).secondCountableTopology
  haveI : LocallyCompactSpace (Ainf F) := inferInstance
  haveI : IsLocallyFiniteMeasure laminf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : IsLocallyFiniteMeasure lf := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  haveI : SFinite laminf := inferInstance
  haveI : SFinite lf := inferInstance
  set χ : Af F → ℂ := fun u => psiF ψ (u * sndA F b) with hχ
  have hχadd : ∀ x y, χ (x + y) = χ x * χ y := fun x y => by
    simp only [hχ, add_mul, psiF_add]
  have hpt : ∀ p : Ainf F × Af F,
      (g (fstA F (e p)) * (B : Set (Af F)).indicator (fun _ => (1 : ℂ)) (sndA F (e p))) * ψ (e p * b) =
        (g p.1 * psiInf F ψ (p.1 * fstA F b)) * (B : Set (Af F)).indicator χ p.2 := by
    rintro ⟨x, u⟩
    have h1 : e (x, u) * b = pairA F (x * fstA F b) (u * sndA F b) := by
      rw [he]; rfl
    have h2 : fstA F (e (x, u)) = x := by rw [he]; rfl
    have h3 : sndA F (e (x, u)) = u := by rw [he]; rfl
    rw [h1, h2, h3, psi_pairA]
    by_cases hu : u ∈ (B : Set (Af F))
    · simp only [Set.indicator_of_mem hu, hχ]
      ring
    · simp only [Set.indicator_of_notMem hu]
      ring
  rw [← hmp.integral_comp e.measurableEmbedding]
  simp only [hpt]
  rw [integral_prod_mul (fun x => g x * psiInf F ψ (x * fstA F b))
    (fun u => (B : Set (Af F)).indicator χ u), mul_assoc]
  congr 1
  by_cases hb : sndA F b ∈ annF ψ (B : Set (Af F))
  · rw [integral_indicator_char_of_trivial lf B hB χ (fun x hx => hb x hx),
      Set.indicator_of_mem hb, mul_one]
  · obtain ⟨y, hy, hne⟩ : ∃ y ∈ (B : Set (Af F)), psiF ψ (y * sndA F b) ≠ 1 := by
      simpa [annF] using hb
    rw [integral_indicator_char_of_ne lf B χ hχadd hy hne, Set.indicator_of_notMem hb, mul_zero]

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
