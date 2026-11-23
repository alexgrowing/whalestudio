import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdaptedReduction
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PAdelicCovolumeFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchInvariant
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArchLatticeDiscrete
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PArithmeticCovolumeFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedGenerators
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedIndexSubgroupsFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PBoundedInverseCompact
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCoeffLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PComplementForm
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PCongruenceUnitsFiniteIndex
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PDiscreteFundamentalDomain
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflection
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenReflectionMaps
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PEigenspacesOrthogonal
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramAtData
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PGramDetermines
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHermAtPlace
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PHyperbolicPairTransitive
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIdealClassesFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIndexLeDet
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegerSmallAtPlaces
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIntegralFamilyBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIsotropicScaling
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PIsotropicSplit
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PKTransitive
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLatticeOrbitsFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenCauchySchwarz
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLenSq
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineCoeffsFG
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexCoeffs
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLineIndexNeZero
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PLinePairOrbitsFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMahlerCompactness
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMajorantExists
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PMinkowskiVolumeForm
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PParabolicDecomposition
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PPhaseOnMinus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PScalingLaw
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PShortestVectorIndex
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PShortVectorIsotropic
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PTorusIntegralHomogeneous
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingIntegral
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldingTorus
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PUnfoldOrbit
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVecAtNeZero
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVectorOrbitsFinite
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PVolumeFormIntComb
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedIndexBound
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedLenSmul
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedNormSq
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightedSpaceDim
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWeightPos
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.PWittPartner

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory IsDedekindDomain
open scoped Pointwise ComplexOrder ENNReal NumberField.AdeleRing

noncomputable section

universe u

section Matrices

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

theorem MajorantBound.full : MajorantBound.Statement ι := MajorantBound.proof ι

theorem EigenspacesOrthogonal.full : EigenspacesOrthogonal.Statement ι :=
  EigenspacesOrthogonal.proof ι

theorem EigenReflection.full : EigenReflection.Statement ι := EigenReflection.proof ι

theorem EigenReflectionMaps.full : EigenReflectionMaps.Statement ι :=
  EigenReflectionMaps.proof ι (EigenReflection.full ι) (EigenspacesOrthogonal.full ι)

theorem IsotropicSplit.full : IsotropicSplit.Statement ι :=
  IsotropicSplit.proof ι (EigenspacesOrthogonal.full ι)

theorem PhaseOnMinus.full : PhaseOnMinus.Statement ι := PhaseOnMinus.proof ι

theorem KTransitive.full : KTransitive.Statement ι :=
  KTransitive.proof ι (IsotropicSplit.full ι) (EigenReflectionMaps.full ι) (PhaseOnMinus.full ι)
    (EigenspacesOrthogonal.full ι)

end Matrices

section Groups

theorem UnfoldOrbit.full (G : Type*) [Group G] [MeasurableSpace G] [MeasurableMul G] :
    UnfoldOrbit.Statement G :=
  UnfoldOrbit.proof G

theorem DiscreteFundamentalDomain.full (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] : DiscreteFundamentalDomain.Statement G :=
  DiscreteFundamentalDomain.proof G

theorem TorusIntegralHomogeneous.full (κ : Type*) [Fintype κ] :
    TorusIntegralHomogeneous.Statement κ :=
  TorusIntegralHomogeneous.proof κ

theorem BoundedIndexSubgroupsFinite.full (G : Type*) [AddCommGroup G] :
    BoundedIndexSubgroupsFinite.Statement G :=
  BoundedIndexSubgroupsFinite.proof G

theorem MinkowskiVolumeForm.full (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) [Fact (finrank ℝ V = d)] : MinkowskiVolumeForm.Statement V d :=
  MinkowskiVolumeForm.proof V d

theorem VolumeFormIntComb.full (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (d : ℕ) [Fact (finrank ℝ V = d)] : VolumeFormIntComb.Statement V d :=
  VolumeFormIntComb.proof V d

end Groups

section Numbers

variable (E : Type*) [Field E] [NumberField E]

theorem IntegerSmallAtPlaces.full : IntegerSmallAtPlaces.Statement E := IntegerSmallAtPlaces.proof E

theorem CoeffLatticeBasis.full : CoeffLatticeBasis.Statement E := CoeffLatticeBasis.proof E

theorem IndexLeDet.full : IndexLeDet.Statement E := IndexLeDet.proof E

theorem WeightedNormSq.full : WeightedNormSq.Statement E := WeightedNormSq.proof E

theorem IdealClassesFinite.full : IdealClassesFinite.Statement E := IdealClassesFinite.proof E

theorem IntegralFamilyBound.full : IntegralFamilyBound.Statement E := IntegralFamilyBound.proof E

theorem CongruenceUnitsFiniteIndex.full : CongruenceUnitsFiniteIndex.Statement E :=
  CongruenceUnitsFiniteIndex.proof E

theorem WeightedSpaceDim.full [IsTotallyComplex E] : WeightedSpaceDim.Statement E :=
  WeightedSpaceDim.proof E

theorem WeightedIndexBound.full [IsTotallyComplex E] : WeightedIndexBound.Statement E :=
  WeightedIndexBound.proof E (CoeffLatticeBasis.full E) (IndexLeDet.full E) (WeightedNormSq.full E)
    (WeightedSpaceDim.full E) (MinkowskiVolumeForm.full _ _) (VolumeFormIntComb.full _ _)

variable (W : Type*) [AddCommGroup W] [Module E W]

theorem LineIndexNeZero.full : LineIndexNeZero.Statement E W := LineIndexNeZero.proof E W

theorem LineIndexCoeffs.full : LineIndexCoeffs.Statement (E := E) W := LineIndexCoeffs.proof E W

theorem LineCoeffsFG.full : LineCoeffsFG.Statement (E := E) W := LineCoeffsFG.proof W

end Numbers

section Spaces

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (h : HermitianForm F E W) (v : Basis ι E W)

theorem HermAtPlace.full : HermAtPlace.Statement h v := HermAtPlace.proof h v

theorem GramAtData.full : GramAtData.Statement h v := GramAtData.proof h v

theorem ArchInvariant.full : ArchInvariant.Statement h v := ArchInvariant.proof h v

theorem LenSq.full : LenSq.Statement h v := LenSq.proof h v

theorem VecAtNeZero.full : VecAtNeZero.Statement v := VecAtNeZero.proof v

theorem WeightedLenSmul.full : WeightedLenSmul.Statement h v :=
  WeightedLenSmul.proof h v (LenSq.full h v)

theorem WeightPos.full : WeightPos.Statement h v := WeightPos.proof h v (VecAtNeZero.full v)

theorem MajorantExists.full : MajorantExists.Statement h v :=
  MajorantExists.proof h v (GramAtData.full h v)

theorem ArchLatticeDiscrete.full : ArchLatticeDiscrete.Statement h v := ArchLatticeDiscrete.proof h v

theorem LenCauchySchwarz.full : LenCauchySchwarz.Statement h v := LenCauchySchwarz.proof h v

theorem BoundedInverseCompact.full : BoundedInverseCompact.Statement h v :=
  BoundedInverseCompact.proof h v

theorem GramDetermines.full : GramDetermines.Statement h := GramDetermines.proof h

theorem WittPartner.full : WittPartner.Statement h := WittPartner.proof h

theorem ComplementForm.full : ComplementForm.Statement h := ComplementForm.proof h

theorem IsotropicScaling.full : IsotropicScaling.Statement h :=
  IsotropicScaling.proof h (WittPartner.full h)

theorem HyperbolicPairTransitive.full [FiniteDimensional E W] :
    HyperbolicPairTransitive.Statement h :=
  HyperbolicPairTransitive.proof h

theorem ShortVectorIsotropic.full : ShortVectorIsotropic.Statement h v :=
  ShortVectorIsotropic.proof h v (HermAtPlace.full h v) (GramAtData.full h v) (ArchInvariant.full h v)
    (MajorantBound.full ι) (LenSq.full h v) (IntegerSmallAtPlaces.full E)

theorem ShortestVectorIndex.full : ShortestVectorIndex.Statement h v :=
  ShortestVectorIndex.proof h v (LineIndexCoeffs.full E W) (LineCoeffsFG.full E W)
    (WeightedLenSmul.full h v) (WeightPos.full h v) (WeightedIndexBound.full E)

theorem ParabolicDecomposition.full : ParabolicDecomposition.Statement h v :=
  ParabolicDecomposition.proof h v (KTransitive.full ι) (HermAtPlace.full h v) (GramAtData.full h v)
    (ArchInvariant.full h v) (VecAtNeZero.full v)

end Spaces

section Conditional

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]

theorem MahlerCompactness.full_of {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) : MahlerCompactness.Statement h v :=
  MahlerCompactness.proof h v (BoundedGenerators.proof h v hR hA hT) (LenCauchySchwarz.full h v)
    (GramDetermines.full h) (BoundedInverseCompact.full h v)

theorem AdaptedReduction.full_of {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    (h : HermitianForm F E W) (hLN : LineNormalForm.Statement h)
    (hCL : ComplementLattice.Statement h) : AdaptedReduction.Statement h :=
  AdaptedReduction.proof h (HyperbolicPairTransitive.full h) hLN hCL

theorem LinePairOrbitsFinite.full_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : HermitianForm F E W)
    (hB : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (hCE : ComplementExtension.Statement h)
    (hLN : LineNormalForm.Statement h) (hCL : ComplementLattice.Statement h) :
    LinePairOrbitsFinite.Statement h :=
  LinePairOrbitsFinite.proof h hB (WittPartner.full h) (ComplementForm.full h) hCE
    (AdaptedReduction.full_of h hLN hCL)

theorem LatticeOrbitsFinite.step_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] (h : HermitianForm F E W)
    (hB : LatticeOrbitsFiniteBelow.{u} F E (finrank E W)) (hR : ReducedBasisBound.Statement)
    (hA : ArchCovolumeBound.Statement h (Module.finBasis E W))
    (hT : MajorantTransport.Statement h (Module.finBasis E W))
    (hCE : ComplementExtension.Statement h) (hLN : LineNormalForm.Statement h)
    (hCL : ComplementLattice.Statement h) : LatticeOrbitsFinite.Statement h :=
  LatticeOrbitsFinite.proof h (Module.finBasis E W) (MahlerCompactness.full_of h _ hR hA hT)
    (MajorantExists.full h _) (ShortVectorIsotropic.full h _)
    (LinePairOrbitsFinite.full_of h hB hCE hLN hCL)

theorem LatticeOrbitsFiniteBelow.of_steps (hR : ReducedBasisBound.Statement)
    (hA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchCovolumeBound.Statement h v)
    (hT : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantTransport.Statement h v)
    (hCE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementExtension.Statement h)
    (hLN : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), LineNormalForm.Statement h)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementLattice.Statement h)
    (N : ℕ) : LatticeOrbitsFiniteBelow.{u} F E N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ h hN
    exact LatticeOrbitsFinite.step_of h (ih _ hN) hR (hA W h _ _) (hT W h _ _) (hCE W h)
      (hLN W h) (hCL W h)

theorem ScalingLaw.full_of {W : Type*} [AddCommGroup W] [Module E W] [FiniteDimensional E W]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hP : LinePairOrbitsFinite.Statement h) (hU : UnfoldingIntegral.Statement h v) :
    ScalingLaw.Statement h v :=
  ScalingLaw.proof h v hU
    (VectorOrbitsFinite.proof h hP (IsotropicScaling.full h) (BoundedIndexSubgroupsFinite.full W)
      (LineIndexNeZero.full E W))
    (UnfoldOrbit.full _) (DiscreteFundamentalDomain.full _) (ArchLatticeDiscrete.full h v)

theorem UnfoldingIntegral.full_of {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*}
    [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W) (v : Basis ι E W)
    (hUA : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : HaarParabolicCoordinates.Statement h v) (hSC : StabilizerCovolumeFinite.Statement h v) :
    UnfoldingIntegral.Statement h v :=
  UnfoldingIntegral.proof h v (UnfoldingTorus.proof h v hUA hHP hSC)
    (TorusIntegralHomogeneous.full _) (DiscreteFundamentalDomain.full _)

theorem ArithmeticCovolumeFinite.step_of {W : Type u} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W)
    (v : Basis ι E W) (hL : LatticeOrbitsFiniteBelow.{u} F E (finrank E W))
    (hR : ReducedBasisBound.Statement) (hA : ArchCovolumeBound.Statement h v)
    (hT : MajorantTransport.Statement h v) (hCE : ComplementExtension.Statement h)
    (hLN : LineNormalForm.Statement h) (hCL : ComplementLattice.Statement h)
    (hUA : ∀ M : Majorant h v,
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : HaarParabolicCoordinates.Statement h v) (hSC : StabilizerCovolumeFinite.Statement h v)
    (hPB : LatticePointsBelowFinite.Statement h v) : ArithmeticCovolumeFinite.Statement h v :=
  ArithmeticCovolumeFinite.proof h v
    (ScalingLaw.full_of h v (LinePairOrbitsFinite.full_of h hL hCE hLN hCL)
      (UnfoldingIntegral.full_of h v hUA hHP hSC))
    (MahlerCompactness.full_of h v hR hA hT) (ShortVectorIsotropic.full h v)
    (ShortestVectorIndex.full h v) (IntegralFamilyBound.full E) (MajorantExists.full h v)
    (ArchLatticeDiscrete.full h v) hPB

theorem CovolumeFiniteBelow.of_steps (hR : ReducedBasisBound.Statement)
    (hA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), ArchCovolumeBound.Statement h v)
    (hT : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W), MajorantTransport.Statement h v)
    (hCE : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementExtension.Statement h)
    (hLN : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), LineNormalForm.Statement h)
    (hCL : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W), ComplementLattice.Statement h)
    (hUA : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W) (M : Majorant h v),
      UnfoldAlongSubgroup.Statement (archUnitary h v) ((InfinitePlace E → ℂ) × M.stab))
    (hHP : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      HaarParabolicCoordinates.Statement h v)
    (hSC : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      CovolumeFiniteBelow.{u} F E (finrank E W) → StabilizerCovolumeFinite.Statement h v)
    (hPB : ∀ (W : Type u) [AddCommGroup W] [Module E W] [FiniteDimensional E W]
      (h : HermitianForm F E W) (n : ℕ) (v : Basis (Fin n) E W),
      LatticePointsBelowFinite.Statement h v)
    (N : ℕ) : CovolumeFiniteBelow.{u} F E N := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro W _ _ _ h n v hN
    exact ArithmeticCovolumeFinite.step_of h v
      (LatticeOrbitsFiniteBelow.of_steps hR hA hT hCE hLN hCL _) hR (hA W h n v) (hT W h n v)
      (hCE W h) (hLN W h) (hCL W h) (hUA W h n v) (hHP W h n v) (hSC W h n v (ih _ hN))
      (hPB W h n v)

theorem AdelicCovolumeFinite.full_of {W : Type*} [AddCommGroup W] [Module E W]
    [FiniteDimensional E W] {ι : Type*} [Fintype ι] [DecidableEq ι] (h : HermitianForm F E W)
    (v : Basis ι E W) (hL : LatticeOrbitsFinite.Statement h)
    (hC : ArithmeticCovolumeFinite.Statement h v) (hAU : ArchimedeanUnitaryEquiv.Statement h v)
    (hAL : AdelicLatticeDictionary.Statement h v)
    (hDC : DoubleCosetCovolume.Statement (unitaryPoints F E (gram h.toSesq v) 𝔸[F])
      (archUnitary h v) (unitaryPoints F E (gram h.toSesq v) (FiniteAdeleRing (𝓞 F) F))) :
    AdelicCovolumeFinite.Statement h v :=
  AdelicCovolumeFinite.proof h v hL hC hAU hAL hDC

end Conditional

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
