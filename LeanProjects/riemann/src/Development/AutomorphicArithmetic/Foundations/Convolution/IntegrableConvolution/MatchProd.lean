import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.FinSplit
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchFin
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SplitLoc
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.GlueBasic

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

private lemma haar_unique {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ μ' : Measure G) [μ.IsHaarMeasure] [μ'.IsHaarMeasure]
    (K : Set G) (h : μ K = 1) (h' : μ' K = 1) : μ' = μ := by
  have e := Measure.isMulLeftInvariant_eq_smul μ' μ
  have hK : (Measure.haarScalarFactor μ' μ : ENNReal) = 1 := by
    have := congrArg (fun ν : Measure G => ν K) e
    simpa [h, h'] using this.symm
  have h1 : Measure.haarScalarFactor μ' μ = 1 := by exact_mod_cast hK
  rw [e, h1, one_smul]

private lemma cmp_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E ≃ₐ[F] E} {m n : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} (D : UpperTheory.ConvolutionTheory.L1.Split (incFin E v) (galFin σ v) m)
    (w : Fin (m + 1) ≃ PlacesOver E v)
    (hD : ∀ (b : CompletionsOver E v) i, completionMap v (w i).1 (D.e b i) = b (w i)) (i : Fin (m + 1))
    (g : GL (Fin n) (CompletionsOver E v)) :
    UpperTheory.ConvolutionTheory.GM.cmp (w i) g = mapGL n (completionMap v (w i).1) (D.comp n i g) := by
  ext a b
  simp [UpperTheory.ConvolutionTheory.GM.cmp, UpperTheory.ConvolutionTheory.L1.Split.comp, hD]

theorem UpperTheory.ConvolutionTheory.L1.matchProd :
    UpperTheory.ConvolutionTheory.L1.MatchProd := by
  intro F E _ _ _ _ _ _ σ hσ m hm n v w₀ hs
  obtain ⟨D, w, hw0, hD⟩ := UpperTheory.ConvolutionTheory.L1.finSplit F E σ hσ m hm v w₀ hs
  refine ⟨w, hw0, ?_⟩
  intro h hh iF bF mF hHaar hvol iE' bE' iF' bF' mE mF' hE hF' hmE hmF'
  obtain rfl : iF' = iF := by rw [bF'.measurable_eq, bF.measurable_eq]
  haveI := hHaar
  haveI := hF'
  haveI := hE
  have hmm : mF' = mF := haar_unique mF mF' _ hvol hmF'
  rw [hmm]
  have hsl := fun i => UpperTheory.ConvolutionTheory.L1.splitLoc F E v (w i) (hs (w i)) n
  set φ : Fin (m + 1) → GL (Fin n) (v.adicCompletion F) → ℂ :=
    fun i g => h (w i) (mapGL n (completionMap v (w i).1) g) with hφ
  have hφc : ∀ i, Continuous (φ i) ∧ HasCompactSupport (φ i) := by
    intro i
    obtain ⟨⟨e, he⟩, -⟩ := hsl i
    have : φ i = h (w i) ∘ e := funext fun g => by simp [hφ, he]
    rw [this]
    exact ⟨(hh _).1.comp e.continuous, (hh _).2.comp_homeomorph e.toHomeomorph⟩
  obtain ⟨c, hc, hμ, hM, hT⟩ := UpperTheory.ConvolutionTheory.L1.matchFin F E σ m v D n mE mF hE hHaar
  obtain ⟨hc1, hc2, hT'⟩ := hT φ hφc
  obtain ⟨-, -, -, hgc, hcc, -⟩ := UpperTheory.ConvolutionTheory.L1.glueBasic _ _ (incFin E v) (galFin σ v) m D n
  have hpf : UpperTheory.ConvolutionTheory.GM.prodFn h = D.tens n φ := by
    funext g
    simp only [UpperTheory.ConvolutionTheory.GM.prodFn, UpperTheory.ConvolutionTheory.L1.Split.tens]
    rw [← finprod_comp_equiv w, finprod_eq_prod_of_fintype]
    exact Finset.prod_congr rfl fun i _ => by rw [cmp_eq D w hD i g]
  have hU : ∀ g, g ∈ unitSet E n v ↔ ∀ i, D.comp n i g ∈ GLnLocal.integralGL (v.adicCompletion F) n := by
    intro g
    constructor
    · intro hg i
      have h1 : UpperTheory.ConvolutionTheory.GM.cmp (w i) g ∈ GLnLocal.integralGL ((w i).1.adicCompletion E) n := hg (w i)
      rw [cmp_eq D w hD i g] at h1
      exact ((hsl i).2.1 _).1 h1
    · intro hg u
      obtain ⟨i, rfl⟩ := w.surjective u
      have h1 := ((hsl i).2.1 _).2 (hg i)
      rw [← cmp_eq D w hD i g] at h1
      exact h1
  have hcomp := (UpperTheory.ConvolutionTheory.L1.glueBasic _ _ (incFin E v) (galFin σ v) m D n).1
  have hset : D.glue n ⁻¹' unitSet E n v =
      Set.pi Set.univ fun _ => (GLnLocal.integralGL (v.adicCompletion F) n : Set _) := by
    ext g
    simp [hU, hcomp]
  have hKm : MeasurableSet (GLnLocal.integralGL (v.adicCompletion F) n : Set (GL (Fin n) (v.adicCompletion F))) :=
    (GLnLocal.isOpen_integralGL _ n).measurableSet
  have hmeas : MeasurableSet (unitSet E n v) := by
    have : unitSet E n v = ⋂ i, D.comp n i ⁻¹' (GLnLocal.integralGL (v.adicCompletion F) n : Set _) := by
      ext g
      simp [hU]
    rw [this]
    exact MeasurableSet.iInter fun i => (hcc i).measurable hKm
  have hpi : Measure.pi (fun _ : Fin (m + 1) => mF)
      (Set.pi Set.univ fun _ => (GLnLocal.integralGL (v.adicCompletion F) n : Set _)) = 1 := by
    rw [Measure.pi_pi]
    simp [hvol]
  have hone : ENNReal.ofReal c = 1 := by
    have h1 := hmE
    rw [hμ, Measure.smul_apply, Measure.map_apply hgc.measurable hmeas, hset, hpi] at h1
    simpa using h1
  have hc1' : c = 1 := ENNReal.ofReal_eq_one.1 hone
  have hfin := hM (D.tens n φ) hc1 hc2
  rw [hT', hc1', ← hpf, ← hm] at hfin
  simpa using hfin
