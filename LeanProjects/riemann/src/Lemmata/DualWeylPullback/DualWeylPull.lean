import Mathlib
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LatRetract
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TensorKP
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.LemmaSMat
import Formalism.PolynomialDimension.MultinomialDepth.WeylDimPosOfAntitone
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.HarProjEqZeroIff
import Formalism.PolynomialDimension.DigitClassSize
import Formalism.PolynomialDimension.DigitClassCount
import Formalism.SharpRestriction.GrowthBounds.ObjSeg
import Formalism.SharpRestriction.GrowthBounds.ObjBridge
import Formalism.LocalRingCardinality.Params
import Formalism.LocalRingCardinality.DataSpaces
import Formalism.LocalRingCardinality.DataCoeff
import Formalism.LocalRingCardinality.DataArith
import Formalism.LocalRingCardinality.DataKernels
import Formalism.LocalRingCardinality.DataRows
import Formalism.SharpRestriction.CuspSpanNormBounds.DataS
import Formalism.SharpRestriction.GrowthBounds.DataG
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GrowthBounds.ObjPol
import Formalism.MahlerMeasure.WithMargin
import Formalism.SubspaceCounting.ChoiceOfTopsRefined
import Formalism.GrowthSums.LemmaATwoFactList
import Formalism.FrobeniusOrbits.DiscrMaximalRealCyclotomic
import Formalism.FrobeniusOrbits.HostOrbitsPlaces
import Formalism.FrobeniusOrbits.HostDiffSupport
import Formalism.FrobeniusOrbits.HostThickExists
import Formalism.FrobeniusOrbits.HostOrbitCountSg
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ConjEMemHostFIff
import Formalism.CoboundaryTransfers.Statement
import Formalism.DegreeFormula.FlagDegFormula
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport
import Formalism.SharpRestriction.GrowthBounds.UnramifiedQuadraticSetting
import Formalism.SharpRestriction.GrowthBounds.DataGChain
import Formalism.SharpRestriction.GrowthBounds.SegRing
import Formalism.PolynomialDimension.DetMulEqSumAdjugate
import Formalism.PolynomialDimension.FinalNum
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.RealCyclotomicSubfield
import Formalism.LocalRingCardinality.DataLevel
import Formalism.SatakeDualWeyl.Statement
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.GrowthBounds.Imports
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.OrbitSum
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ChainScalar
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.LatLiftIndep
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.GaussOp
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.EigenSwap
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.FFPlancherel
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.DetSwap
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.DiscriminantRealSubfield
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickOrbit
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickFrames
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.ZsmulGeneratorEqZeroOfProjection
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermodZ
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ExistsSmulMemOfFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FinSup
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SatBasic
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RatioMax
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DegSupermod
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.MuChar
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNStep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HNSlopes
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Duality
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PiSumForallInsertOnly
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Example
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.DiscreteSpanOfLinIndep
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SizeMu
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PlaceSplit
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.GramBlock
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.RescaleCovol
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.TwistFinrankEq
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.SlopeIneqMean
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtGram
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.HtImage
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.Rerealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.QuotRealize
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.FrameLinearAlgebraFirst
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Actions
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.AutomorphicFormsDecompositionHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeAssoc
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Bridge
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.HeckeConvolutionMemHolds
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LocalAlgebraInertPrime
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckebasic
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.InclusionInjective
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Ipindep
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Levelvsplit
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.LinSubstIsHomogeneous
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Nabladual
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureConjugationInvariant
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SignatureExists
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SplitUnitaryGroupIso
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabfin
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stabstd
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Stdform
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Transport
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.DualWeylModuleStable
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Wlocal
import Formalism.SatakeDualWeyl.DualWeylRepApply
import Formalism.FrobeniusOrbits.Statement
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.CuspSpanNormBounds.Point
import Formalism.ThetaLiftIndependence.Statement
import Formalism.HarderNarasimhan.StatementFrame
import Formalism.LatticeSlopes.ExistsSaturatedSlopeEqMuMax
import Formalism.CorankShare.CorankShareProofs.LayerCakeFormula
import Formalism.CorankShare.CorankShareProofs.SumNormSqLeHilbertSchmidt
import Formalism.HarderNarasimhan.StatementFrameF
import Formalism.SatakeDualWeyl.StatementC
import Formalism.SatakeDualWeyl.StatementE
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Heckecomm
import Formalism.SatakeDualWeyl.StatementF
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SphericalA
import Formalism.TameInertiaTowers.FinalGroup
import Formalism.TameInertiaTowers.CentralOrderTwo.Galois
import Formalism.TameInertiaTowers.CentralOrderTwo.ConjEqInvOfPowEqOne
import Formalism.FormalDegreeBessel.StatementBF
import Formalism.FormalDegreeBessel.StatementWR
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomAct
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.ThetaBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.ExampleZ
import Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice
import Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
import Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
import Formalism.HermitianLattices.HermitianLatticesProofs.DualOrthSum
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusScale
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.OpBound
import Formalism.HermitianLattices.HermitianLatticesProofs.MajBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovol
import Formalism.HermitianLattices.HermitianLatticesProofs.UnimodUnramUnique
import Formalism.DirichletDensity.DirichletDensityProofs.QuadDiscr
import Formalism.DirichletDensity.DirichletDensityProofs.APLogDensity
import Formalism.DirichletDensity.DirichletDensityProofs.HostDensityArith
import Formalism.CMTypeGalois.CMTypeFrobenius.MQGalois
import Formalism.CMTypeGalois.CMTypeFrobenius.MQKummer
import Formalism.CMTypeGalois.CMTypeFrobenius.MQFrob
import Formalism.CMTypeGalois.CMTypeFrobenius.KroneckerMeaning
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesA
import Formalism.CMTypeGalois.CMTypeFrobenius.TypesB
import Formalism.CMTypeGalois.CMTypeFrobenius.HostFrob
import Formalism.CMTypeGalois.CMTypeFrobenius.HostConj
import Formalism.CMTypeGalois.CMTypeFrobenius.HostInertia
import Formalism.CMTypeGalois.CMTypeFrobenius.HostMu
import Formalism.CMTypeGalois.CMTypeFrobenius.HostEmb
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeComb
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.SatakeMat
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.TjcosetsFF
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.HermitianLattices.DefsCS
import Formalism.HermitianLattices.GenusCovolBound
import Formalism.HermitianLattices.StatementMaj
import Formalism.HermitianLattices.DiscrFinite
import Formalism.LatticeTheta.ThetaShiftInversion
import Formalism.DirichletDensity.Statement
import Formalism.SatakeDualWeyl.StatementB
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CompactCasimirHighestWeight
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantCompactSpan
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IsCompactInvariantOrthogonalInf
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkCore
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjLevel
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.SuccMin
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.AdaptedBasis
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MeasureEqCovolumeMulVolumeImage
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NewtonSlope
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.MinkowskiIILowerOf
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPWDivision
import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.NPUnit
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ComplexifiedDerivativeCommutator
import Formalism.RealPlaceAnalysis.StatementU
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.MemUnitaryGroupIffMulConjTranspose
import Formalism.RealPlaceAnalysis.StatementD
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuadraticInequalityBoundHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.SumOfSquaresIdentityHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CasKHW
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.HWDiag
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.TrPowSumFilterZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.QuantumDetHighestWeightHolds
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.ShiftedGeneratorEqIteSmulAdd
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.GeneratorCommutatorQuantumDet
import Formalism.RealPlaceAnalysis.SmoothOnG
import Formalism.RealPlaceAnalysis.StatementA
import Formalism.RealPlaceAnalysis.StatementC

namespace Bl.DualWeylPullback

private lemma map_aeval_nat {O K σ τ : Type} [CommRing O] [CommRing K] (φ : O →+* K)
    (h : σ → MvPolynomial τ O) (f : MvPolynomial σ O) :
    MvPolynomial.map φ (MvPolynomial.aeval h f) =
      MvPolynomial.aeval (fun v => MvPolynomial.map φ (h v)) (MvPolynomial.map φ f) := by
  induction f using MvPolynomial.induction_on with
  | C a => simp only [MvPolynomial.aeval_C, MvPolynomial.map_C, MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, MvPolynomial.map_X, MvPolynomial.aeval_X, hp]

private lemma rowAct_map {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {k n : ℕ}
    (A : Matrix (Fin k) (Fin k) O) (f : MvPolynomial (Fin k × Fin n) O) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.rowAct O A f) = Formalism.GradedWeylDivisibility.rowAct K (A.map φ) (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.rowAct
  rw [map_aeval_nat]
  congr 1
  congr 1
  funext v
  simp [map_sum]

private lemma colAddGen_map {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K) {k n : ℕ}
    (l j : Fin n) (f : MvPolynomial (Fin k × Fin n) O) :
    MvPolynomial.map φ (Formalism.GradedWeylDivisibility.colAddGen O l j f) = Formalism.GradedWeylDivisibility.colAddGen K l j (MvPolynomial.map φ f) := by
  unfold Formalism.GradedWeylDivisibility.colAddGen
  rw [map_aeval_nat]
  congr 1
  congr 1
  funext v
  split_ifs <;> simp

private lemma dualWeyl_pull {O K : Type} [CommRing O] [CommRing K] (φ : O →+* K)
    (hφ : Function.Injective φ) {r n : ℕ} (ν : Fin n → ℕ) (f : MvPolynomial (Fin r × Fin n) O)
    (hf : MvPolynomial.map φ f ∈ Formalism.GradedWeylDivisibility.dualWeyl K r n ν) : f ∈ Formalism.GradedWeylDivisibility.dualWeyl O r n ν := by
  unfold Formalism.GradedWeylDivisibility.dualWeyl at hf ⊢
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, MvPolynomial.mem_weightedHomogeneousSubmodule] at hf ⊢
  refine ⟨?_, ?_⟩
  · intro d hd
    exact hf.1 (by
      rw [MvPolynomial.coeff_map]
      intro h0
      exact hd (hφ (by rw [h0, map_zero])))
  · intro l j hlj
    apply MvPolynomial.map_injective φ hφ
    rw [colAddGen_map, MvPolynomial.map_rename]
    exact hf.2 l j hlj

private lemma span_mat {O K : Type} [CommRing O] [Field K] [Algebra O K] {k : ℕ}
    (g g' : Matrix (Fin k) (Fin k) K) (h : Formalism.MainNotions.G.colSpan O g' ≤ Formalism.MainNotions.G.colSpan O g) :
    ∃ A : Matrix (Fin k) (Fin k) O, g' = g * A.map (algebraMap O K) := by
  have hc : ∀ c : Fin k, ∃ a : Fin k → O, ∑ i, a i • (fun r => g r i) = fun r => g' r c := by
    intro c
    have h1 : (fun r => g' r c) ∈ Formalism.MainNotions.G.colSpan O g' := Submodule.subset_span ⟨c, rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun O).1 (h h1)
  choose a ha using hc
  refine ⟨Matrix.of fun i c => a c i, ?_⟩
  ext r c
  have h2 := congrFun (ha c) r
  simp only [Finset.sum_apply, Pi.smul_apply] at h2
  rw [← h2, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [Algebra.smul_def, mul_comm]

private lemma span_unit {O K : Type} [CommRing O] [Field K] [Algebra O K]
    (hφ : Function.Injective (algebraMap O K)) {k : ℕ} (g g' : Matrix (Fin k) (Fin k) K)
    (hg : IsUnit g.det) (h : Formalism.MainNotions.G.colSpan O g = Formalism.MainNotions.G.colSpan O g') :
    ∃ A : Matrix (Fin k) (Fin k) O, IsUnit A.det ∧ g' = g * A.map (algebraMap O K) := by
  obtain ⟨A, hA⟩ := span_mat g g' h.ge
  obtain ⟨B, hB⟩ := span_mat g' g h.le
  refine ⟨A, ?_, hA⟩
  have h1 : g * (A * B).map (algebraMap O K) = g * 1 := by
    rw [Matrix.map_mul, ← Matrix.mul_assoc, ← hA, ← hB, Matrix.mul_one]
  have h2 : (A * B).map (algebraMap O K) = 1 := by
    have h3 := congrArg (fun M => g⁻¹ * M) h1
    simpa [← Matrix.mul_assoc, Matrix.nonsing_inv_mul g hg] using h3
  have h3 : A * B = 1 := by
    apply Matrix.map_injective hφ
    simpa using h2
  have h4 : A.det * B.det = 1 := by rw [← Matrix.det_mul, h3, Matrix.det_one]
  exact ⟨⟨A.det, B.det, h4, by rw [mul_comm]; exact h4⟩, rfl⟩

private lemma clear_den {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (w : O) (hw : Irreducible w) {σ : Type} (G : MvPolynomial σ K) :
    ∃ n : ℕ, ∃ G0 : MvPolynomial σ O,
      MvPolynomial.map (algebraMap O K) G0 = algebraMap O K (w ^ n) • G := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors O) G.coeffs
  have hb0 : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero b
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hw
  refine ⟨n, ?_⟩
  have hr : algebraMap O K (w ^ n) • G ∈ Set.range (MvPolynomial.map (algebraMap O K)) := by
    rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
    intro x hx
    rw [Finset.mem_coe, MvPolynomial.mem_coeffs_iff] at hx
    obtain ⟨d, hd, rfl⟩ := hx
    rw [MvPolynomial.coeff_smul, smul_eq_mul]
    have hd' : G.coeff d ≠ 0 := by
      intro h0
      apply MvPolynomial.mem_support_iff.1 hd
      rw [MvPolynomial.coeff_smul, h0, smul_zero]
    obtain ⟨y, hy⟩ := hb _ (MvPolynomial.coeff_mem_coeffs _ hd')
    have hu1 : algebraMap O K (↑u⁻¹ : O) * algebraMap O K (↑u : O) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    refine ⟨(↑u⁻¹ : O) * y, ?_⟩
    rw [map_mul, hy, Algebra.smul_def, hu, map_mul]
    linear_combination (algebraMap O K (w ^ n) * G.coeff d) * hu1
  obtain ⟨G0, h0⟩ := hr
  exact ⟨G0, h0⟩

theorem goal1 :
  ∀ {O K : Type} [inst : CommRing.{0} O] [inst_1 : IsDomain.{0} O] [IsDiscreteValuationRing.{0} O] [inst_3 : Field.{0} K]
  [inst_4 : Algebra.{0, 0} O K] [IsFractionRing.{0, 0} O K] (w : O),
  Irreducible.{0} w →
    ∀ (m : Nat) (mu : Fin (HAdd.hAdd.{0, 0, 0} m 1) → Int),
      Antitone.{0, 0} mu →
        ∀ (g : Matrix.{0, 0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1)) K),
          IsUnit.{0} (Matrix.det.{0, 0} g) →
            ∀ (F : MvPolynomial.{0, 0} (Prod.{0, 0} (Fin (HAdd.hAdd.{0, 0, 0} m 1)) (Fin (HAdd.hAdd.{0, 0, 0} m 1))) K),
              Membership.mem.{0, 0}
                  (Formalism.GradedWeylDivisibility.dualWeyl.{0} K (HAdd.hAdd.{0, 0, 0} m 1) (HAdd.hAdd.{0, 0, 0} m 1) (Formalism.MainNotions.G.nuOf mu)) F →
                Exists.{1} fun (n : Nat) ↦
                  Membership.mem.{0, 0} (Formalism.MainNotions.G.H0.{0, 0} O m mu (Formalism.MainNotions.G.colSpan.{0, 0} O g))
                    (HSMul.hSMul.{0, 0, 0} (HPow.hPow.{0, 0, 0} w n) F) := by
  intro O K _ _ _ _ _ _ w hw m mu hmu g hg F hF
  have hinj : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
  have hG : g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F ∈
      Formalism.GradedWeylDivisibility.dualWeyl K (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable K _ _ _ g F hF)
  obtain ⟨n, G0, hG0⟩ := clear_den w hw (g.det ^ mu (Fin.last m) • Formalism.GradedWeylDivisibility.rowAct K g F)
  have hG0m : G0 ∈ Formalism.GradedWeylDivisibility.dualWeyl O (m + 1) (m + 1) (Formalism.MainNotions.G.nuOf mu) :=
    dualWeyl_pull _ hinj _ G0 (by rw [hG0]; exact Submodule.smul_mem _ _ hG)
  refine ⟨n, ?_⟩
  unfold Formalism.MainNotions.G.H0
  rw [if_pos hmu]
  simp only [Submodule.mem_iInf]
  rintro g' ⟨hg', hspan⟩
  obtain ⟨A, hA, rfl⟩ := span_unit hinj g g' hg hspan
  rw [Formalism.GradedWeylDivisibility.nablaLTwMem O K m mu _ hg']
  obtain ⟨U, hU⟩ := hA
  refine ⟨(↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0,
    Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable O _ _ _ A G0 hG0m), ?_⟩
  change MvPolynomial.map (algebraMap O K) ((↑(U ^ mu (Fin.last m)) : O) • Formalism.GradedWeylDivisibility.rowAct O A G0) = _
  have hz : algebraMap O K ↑(U ^ mu (Fin.last m)) = (algebraMap O K ↑U) ^ mu (Fin.last m) := by
    have h5 : ((Units.map (algebraMap O K).toMonoidHom (U ^ mu (Fin.last m)) : Kˣ) : K) =
        algebraMap O K ↑(U ^ mu (Fin.last m)) := rfl
    rw [← h5, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  have hdet : (A.map (algebraMap O K)).det = algebraMap O K A.det := by
    rw [RingHom.map_det]
    rfl
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, ← MvPolynomial.smul_eq_C_mul,
    rowAct_map, hG0, Matrix.det_mul, hdet, ← hU, hz,
    ← Formalism.GradedWeylDivisibility.rowActMul K (m + 1) (m + 1) (A.map (algebraMap O K)) g, AlgHom.comp_apply,
    ← algebraMap_smul K (w ^ n) F]
  simp only [map_smul, smul_smul]
  congr 1
  rw [mul_zpow]
  ring

end Bl.DualWeylPullback
