import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopSelfCurveCharNotInBadSet
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB
open ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.top_self_curve_char_not_in_bad_set : GlobalTheory.CovTop.HypothesesXH → Hypotheses2 → HypothesesH → GlobalTheory.Published.ScholzeWeinsteinB → ∀ (D : D7) (O : Setup D), O.Core → 2 < D.R.f * (O.N - 1) →
    ∀ (B : ℝ), 2 ≤ B → ∀ (c : O.s.Comp) (W : O.LatModel (GlobalTheory.FlagAr.setB O.Y B) c) (τ : D.what₂.Tau)
    (Z : Scheme.{0}) (i : Z ⟶ W.V.X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ]
    [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → ringChar κ ∉ GlobalTheory.FlagAr.setB O.Y B →
    ∀ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y) (h : O.Reads A T H), h.mdl (GlobalTheory.FlagAr.setB O.Y B) c = W → topSelfIntersection κ ((comb (W.gens (GlobalTheory.FlagAr.setB O.Y B)) (fun o : Option (D.what₂.Tau × Fin O.N) => o.elim (0 : ℤ) fun x => if x.1 = τ then (-1 : ℤ) else 0)).B.pull i) 1 = 0 := by
  first | exact @GlobalTheory.DetDRVert.topSelf_detDR_eq_zero | exact GlobalTheory.DetDRVert.topSelf_detDR_eq_zero | (intros; apply GlobalTheory.DetDRVert.topSelf_detDR_eq_zero <;> assumption)
