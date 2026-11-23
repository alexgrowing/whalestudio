import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalModelNonvanishingWeights
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppInjectiveOfFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticCurveSubbundleCover
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure

set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.LatticeTransfer Formalism.MainNotions.WeightThresholdDefs
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains
open GlobalTheory.VB (IsVB IsSubbundle)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normal_model_nonvanishing_weights : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (B : GlobalTheory.Vert.Model O), GlobalTheory.IsNormalScheme B.X → ∀ (A ι : Type) [Finite A] [Finite ι]
    (w : A → ι → B.X.functionField), (∀ α, ∃ i, w α i ≠ 0) →
    ∃ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (hη : f.f (genericPoint B'.X) = genericPoint B.X),
      GlobalTheory.IsNormalScheme B'.X ∧ f.relDim = 0 ∧ ∀ (y : B'.X) (α : A), ∃ i, w α i ≠ 0 ∧ ∀ j, ∃ g,
        GlobalTheory.Cartier.RegAt y g ∧ g * GlobalTheory.TrueGeo.SmallSec.fnMap f.f (specializes_of_eq hη) (w α i) =
          GlobalTheory.TrueGeo.SmallSec.fnMap f.f (specializes_of_eq hη) (w α j) := by
  first | exact @GlobalTheory.CorankOneNormal.exists_modification | exact GlobalTheory.CorankOneNormal.exists_modification | (intros; apply GlobalTheory.CorankOneNormal.exists_modification <;> assumption)
