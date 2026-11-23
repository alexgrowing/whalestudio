import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ClosedProperAlt
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.RegOkPi
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.PushTens
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic

open MeasureTheory NumberField

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_tens (R S : Type) [CommRing R] [CommRing S] [TopologicalSpace R]
    [TopologicalSpace S] [IsTopologicalRing R] [IsTopologicalRing S] [LocallyCompactSpace R] [T2Space R]
    [SecondCountableTopology R] [T2Space S] (ι : R →+* S) (s : S →+* S) (m : ℕ) (D : UpperTheory.ConvolutionTheory.L1.Split ι s m) (n : ℕ)
    [MeasurableSpace (GL (Fin n) R)] [BorelSpace (GL (Fin n) R)] (μ : Measure (GL (Fin n) R)) [μ.IsHaarMeasure]
    (φ : Fin (m + 1) → GL (Fin n) R → ℂ) (hφ : ∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i)) :
    Continuous (D.tens n φ) ∧ HasCompactSupport (D.tens n φ) ∧
      D.transfer n μ (D.tens n φ) = UpperTheory.ConvolutionTheory.L1.cvAll μ m φ := by
  obtain ⟨h1, h2, -, h4, h5, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic R S ι s m D n
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isClosedEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) R)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin n) R) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) R)).locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin n) R) :=
    (Units.isEmbedding_embedProduct (M := Matrix (Fin n) (Fin n) R)).secondCountableTopology
  refine ⟨?_, ?_, ?_⟩
  · exact continuous_finset_prod _ fun i _ => (hφ i).1.comp (h5 i)
  · have hK : IsCompact (D.glue n '' Set.pi Set.univ fun i => tsupport (φ i)) :=
      (isCompact_univ_pi fun i => (hφ i).2.isCompact).image h4
    refine HasCompactSupport.intro hK fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨fun i => D.comp n i x, fun i _ => subset_tsupport _ ?_, h2 x⟩
    intro h0
    exact hne (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  · rw [← UpperTheory.ConvolutionTheory.L1.pushTens (GL (Fin n) R) μ m φ (fun i => (hφ i).1) (fun i => (hφ i).2)]
    unfold UpperTheory.ConvolutionTheory.L1.Split.transfer UpperTheory.ConvolutionTheory.L1.Split.tens
    simp only [h1]

private theorem UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space ((v : InfinitePlace F) → v.Completion))

private theorem UpperTheory.ConvolutionTheory.L1.matchInf_sc (F : Type) [Field F] [NumberField F] :
    SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ v : InfinitePlace F, SecondCountableTopology v.Completion := fun v =>
    (InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

theorem UpperTheory.ConvolutionTheory.L1.matchInf :
    UpperTheory.ConvolutionTheory.L1.MatchInf := by
  intro F E _ _ _ _ _ σ m D n _ _ _ _ μE μF hE hF
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' F
  haveI := UpperTheory.ConvolutionTheory.L1.t2Space_infiniteAdeleRing' E
  haveI := UpperTheory.ConvolutionTheory.L1.matchInf_sc F
  obtain ⟨c, hc, hμ, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchSplit _ _ _ _ m D n μE μF hE hF (UpperTheory.ConvolutionTheory.L1.regOkPi.2.2 F n)
  exact ⟨c, hc, hμ, fun φ h1 h2 => (hM φ h1 h2).2.2,
    fun φ hφ => UpperTheory.ConvolutionTheory.L1.matchInf_tens _ _ _ _ m D n μF φ hφ⟩
