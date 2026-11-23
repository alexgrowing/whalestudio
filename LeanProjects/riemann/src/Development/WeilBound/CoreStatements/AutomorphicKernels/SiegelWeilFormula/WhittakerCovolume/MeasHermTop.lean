import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.IsPureTIff
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasProps
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.CovolUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.TupSplit
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasND
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.MeasTop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.ColEApply
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RationalHermitianMeasures.HOfMain
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianCovolumeFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TupleSpaceCovolumeFormulaStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KWhit

open PositivityTheory.SiegelWeilFormula

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem meas_herm_top (d : SD σ) : IsTopologicalAddGroup (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    LocallyCompactSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ SecondCountableTopology (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧
    BorelSpace (HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n) ∧ Countable (MeasP.ratHerm F E σ d.n) := meas_herm_top' d

theorem meas_mx_top (d : SD σ) : IsTopologicalAddGroup (Mx F E d.m d.n) ∧ LocallyCompactSpace (Mx F E d.m d.n) ∧
    SecondCountableTopology (Mx F E d.m d.n) ∧ BorelSpace (Mx F E d.m d.n) ∧ Countable d.ratM := meas_mx_top' d

theorem meas_cm (d : SD σ) : HeckeCharacterZeroLocus.SiegelWeilU.IsCMExt F E σ := d.ok.good.cm

theorem meas_char (d : SD σ) : HeckeCharacterZeroLocus.SiegelWeilU.IsCharAF F d.B.ψ := GlobalTheory.StdCharFromIsStd.isCharAF d.ok.good.std

theorem meas_hermND (d : SD σ) {η : E} (hη : η ≠ 0) (hh : ∀ i j, σ (η * d.A.J j i) = η * d.A.J i j) :
    HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ (Jd d η) := meas_hermND' d hη hh

theorem meas_hOf {d : SD σ} {R : RD d} {x : d.G} {t u : GL (Fin d.n) (AE F E)} {T : nF σ d.Y d.b} {η : E}
    {T₀ : Matrix (Fin d.n) (Fin d.n) E} {hOf : nA σ d.Y d.b → HeckeCharacterZeroLocus.SiegelWeilU.HermR (AF F) σ d.n}
    {θ : InfinitePlace F → (HeckeCharacterZeroLocus.SiegelWeilU.Ainf F ⊗[F] E →+* ℂ)} {fr : InfinitePlace F → GL (Fin d.m) ℂ}
    {g : InfinitePlace F → GL (Fin d.n) ℂ} (hR : Rel d R x t u T η T₀ hOf θ fr g)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hc : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) :
    MeasurableEmbedding hOf ∧ (lam.map hOf).IsAddHaarMeasure ∧
      IsAddFundamentalDomain (MeasP.ratHerm F E σ d.n) (hOf '' 𝓖) (lam.map hOf) ∧ lam.map hOf (hOf '' 𝓖) = 1 :=
  PositivityTheory.SiegelWeilFormula.MeasD.meas_hOf hR hc

theorem meas_toMx (d : SD σ) (μ : Measure (Fin d.n → Fin d.m → AF F ⊗[F] E)) (𝓕 : Set (Fin d.n → Fin d.m → AF F ⊗[F] E))
    (hμ : μ.IsAddHaarMeasure) (hF : IsAddFundamentalDomain (MeasP.ratTupA F E d.n d.m) 𝓕 μ) (h1 : μ 𝓕 = 1) :
    MeasurableEmbedding (toMx (F := F) (E := E) (m := d.m) (n := d.n)) ∧ (μ.map toMx).IsAddHaarMeasure ∧
      IsAddFundamentalDomain d.ratM (toMx '' 𝓕) (μ.map toMx) ∧ μ.map toMx (toMx '' 𝓕) = 1 :=
  PositivityTheory.SiegelWeilFormula.MeasD.meas_toMx d μ 𝓕 hμ hF h1

theorem measDict_of (hH : MeasP.HermCovol) (hT : MeasP.TupCovol) : MeasDict := by
  intro F E _ _ _ _ _ σ d R x t u T η T₀ hOf θ fr g hR
  constructor
  · intro nb lam 𝓖 hc ν hν
    obtain ⟨i1, i2, i3, i4, i5⟩ := meas_herm_top d
    haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
    obtain ⟨hemb, hH', hfd, h1⟩ := meas_hOf hR hc
    haveI := hH'
    obtain ⟨𝓕, hF, hF1⟩ := hH F E σ (meas_cm d) d.B.ψ (meas_char d) d.n ν hν
    haveI := hν.1
    exact ⟨hemb, hemb.measurable, @MeasG.covol_unique _ _ _ _ _ _ _ _ (MeasP.ratHerm F E σ d.n) _ _ _ hν.1 hH' _ _ hF hfd hF1 h1⟩
  · intro μ νc hμ hνc
    obtain ⟨i1, i2, i3, i4, i5⟩ := meas_mx_top d
    haveI := i1; haveI := i2; haveI := i3; haveI := i4; haveI := i5
    obtain ⟨𝓕, hF, hF1⟩ := hT F E σ (meas_cm d) d.m (Jd d η) (meas_hermND d hR.ne hR.herm) d.B.ψ (meas_char d) d.n μ hμ
    obtain ⟨hemb, hH', hfd, h1⟩ := meas_toMx d μ 𝓕 hμ.1 hF hF1
    obtain ⟨hνH, 𝓖, hG, hG1⟩ := hνc
    haveI := hνH; haveI := hH'
    exact ⟨hemb, hemb.measurable, @MeasG.covol_unique _ _ _ _ _ _ _ _ d.ratM _ _ _ hνH hH' _ _ hG hfd hG1 h1⟩

theorem measDict : MeasDict := measDict_of GlobalTheory.T.hermitian_covolume_formula GlobalTheory.T.tuple_space_covolume_formula

end PositivityTheory.SiegelWeilFormula.KWhit

end
