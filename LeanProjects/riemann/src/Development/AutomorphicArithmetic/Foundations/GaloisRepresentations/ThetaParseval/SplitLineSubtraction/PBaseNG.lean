import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
import Development.WeilBound.ThetaLifts.LeviDeterminants.MixedModels.PsiUnrOfNotLe
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Formalism.BasicNotions GlobalTheory.HeckeGal GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open UpperTheory.V.Af (algSat)
open UpperTheory.Gal.TP.Sub

private theorem unram_of_forall {E : Type} [Field E] [NumberField E] [IsCMField E]
    (hE : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := by
    rw [Algebra.formallyUnramified_iff_forall]
    intro q
    obtain ⟨Q, hQ, hqQ⟩ := Ideal.exists_le_maximal q.1 q.2.ne_top
    have hne : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField E)
    have hU := hE ⟨Q, hQ.isPrime, hne⟩
    have hopen := Algebra.isOpen_unramifiedLocus (R := 𝓞 (maximalRealSubfield E)) (A := 𝓞 E)
    exact hopen.stableUnderGeneralization
      ((PrimeSpectrum.le_iff_specializes q ⟨Q, hQ.isPrime⟩).mp hqQ) hU
  exact ⟨inferInstance, inferInstance⟩

private theorem under_eq_of_inert {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : HeightOneSpectrum (𝓞 F)} {w : HeightOneSpectrum (𝓞 E)} (h : Formalism.UG.IsInertAt F E v w) :
    w.under (𝓞 F) = v := by
  apply HeightOneSpectrum.ext
  have hle : v.asIdeal ≤ (w.under (𝓞 F)).asIdeal := by
    show v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 F) (𝓞 E))
    rw [← Ideal.map_le_iff_le_comap]
    exact h.le
  exact (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top hle).symm

private theorem not_split_of_inert {E : Type} [Field E] [NumberField E] [IsCMField E]
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {w : HeightOneSpectrum (𝓞 E)}
    (h : Formalism.UG.IsInertAt (maximalRealSubfield E) E v w) : ¬ GlobalTheory.UnitaryBC.IsSplitAt w := by
  rintro ⟨u, hne, hu⟩
  apply hne
  have hv : u.under (𝓞 (maximalRealSubfield E)) = v := hu.trans (under_eq_of_inert h)
  have hle : w.asIdeal ≤ u.asIdeal := by
    rw [← show Ideal.map (algebraMap (𝓞 (maximalRealSubfield E)) (𝓞 E)) v.asIdeal = w.asIdeal from h, Ideal.map_le_iff_le_comap, ← hv]
    exact le_rfl
  exact (HeightOneSpectrum.ext ((w.isMaximal.eq_of_le u.isPrime.ne_top hle))).symm

theorem UpperTheory.Gal.TP.Sub.baseNG_holds :
    UpperTheory.Gal.TP.Skew.SkewLine → BaseNG := by
  intro hS E _ _ _ hE hI
  have hcm : IsCMExt (maximalRealSubfield E) E (UpperTheory.TP.cj E) :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  have hu := unram_of_forall hE
  obtain ⟨B, δ, 𝔞, -, -, hP, hstd, -, h1, h2⟩ := hS (maximalRealSubfield E) E (UpperTheory.TP.cj E) hcm hu
  refine ⟨B, δ, 𝔞, ?_, h1, h2⟩
  exact
    { cm := hcm
      unram := hu
      std := hstd
      inert := fun v w h => by
        obtain ⟨a, b, c⟩ := hI w (not_split_of_inert h)
        rw [under_eq_of_inert h] at a b c
        exact ⟨a, b, PositivityTheory.Mix.psiUnr_of_not_le hstd v c⟩
      psiP := fun v hv => absurd hv (by simp [hP]) }
