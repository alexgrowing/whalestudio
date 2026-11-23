import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolSub0LeSpanRaw
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdaptedStandardBasis
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsIsNabUncond
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovGmin

def Hyp (D : D7) (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o Lb : ℝ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    Prop :=
  LawsJ T ∧ 1 ≤ (T.Q.Dw j).p ∧ 1 ≤ (T.Q.Dw j).q ∧ 2 < Module.finrank ℚ D.host.E / 2 ∧ InR D j ∧ Y.Good e o ∧
    1 ≤ Lb ∧ Real.log Y.d.l₂.M ≤ 30 * Lb ∧ fieldSz D.host.E ≤ 3 * Lb ∧ Real.log (D.R.f * D.R.r) ≤ Lb ∧
    o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 ∧ Dom a n ∧ Even n ∧ 8 * D.R.f * D.R.r + 4 ≤ n ∧
    (∀ (τ : Psi T.Q.H) (k : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (k : ℕ) < (T.Q.Dw j).p →
      ((n / 2 : ℕ) : ℤ) < laOf (T.Q.Dw j) a n τ k) ∧
    Real.log (sizeK (T.Q.Dw j) a n) ≤ 20 * Lb

def badC {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) : ℕ := D.host.QS * D.host.q * D.host.d * Y.d.l₂.M

def thFam {D : D7} {T : Core D} {j : ℕ} (Y : Deep T j) (nab : NabV Y.d.Xo₂ Y.d.c₂) (a : (D.host.E →+* ℂ) × ℕ → ℕ)
    (n : ℕ) (ρ : ℝ) : Set (Y.V (wtZ a n)) :=
  {y | ∃ (x0 : Fin n → LevQc (T.Q.Dw j) Y.d.l₂) (La : GenLat D.host.E n) (N : ℕ)
      (P : MvPolynomial (LtN (T.Q.Dw j) n) Y.d.c₂.F),
    Submodule.span (𝓞 D.host.E) (Set.range x0) = ⊤ ∧ La.Unimod ∧ La.TrivAt (badC Y) ∧ La.TrivAt Y.d.l₂.M ∧
      La.LevOK N Y.d.l₂.M ∧ P ∈ harmL Y.d.c₂ La a ∧ GlobalTheory.IndefiniteRowSideFullHecke.ThetaWeightData.polyNorm Y.d.c₂ P ≤ ρ ∧
      ∀ (p : TRing Y.d.c₂.F) (y' : FrPt Y.d.Xo₂ Y.d.c₂ p.R),
        thLaValAt Y.d.Xo₂ Y.d.c₂ nab (phiHat Y.d.c₂ (indPhi Y.d.c₂ x0)) La N P y' ((y : Rul Y.d.Xo₂ Y.d.c₂) p y')}

end GlobalTheory.CovGmin
