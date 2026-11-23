import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArithmeticVarietyCover
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_arithmetic_variety_cover : Hypotheses2 → HypothesesH → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (e : ℕ), Y.dim = e →
    ∀ (A' : Adl (cxSt F) Y) (M M' : TrueGeo.Model Y) (L' : HermLB M'.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ),
    A'.Induced M' L' k cf →
    ∃ (X' : Scheme.{0}) (_ : IsIntegral X') (q : X' ⟶ Sp (𝓞 F)) (π : X' ⟶ M.X) (_ : π ≫ M.p = q) (H : HermLB q)
      (n d : ℕ), IsArithVar q e ∧ Surjective π ∧ π.residueDegree (genericPoint X') = d ∧ 0 < d ∧ 0 < n ∧
      H.IsSelfInter ((Module.finrank ℤ (𝓞 F) : ℝ) * d * (n : ℝ) ^ (e + 1) * A'.arTop) ∧
      gdeg H e = (Module.finrank ℤ (𝓞 F) : ℝ) * d * (n : ℝ) ^ e * A'.deg ∧
      (A'.SemiPos ↔ H.SemiPos e) ∧ (A'.NefFib ↔ NefFib H) ∧
      ∀ (y : Y.X) (x : X'), IsAlgPt x → π x = M.j y → IsPtHt H x (n * A'.ht y) := by
  first | exact @GlobalTheory.ReadModel.readModel | exact GlobalTheory.ReadModel.readModel | (intros; apply GlobalTheory.ReadModel.readModel <;> assumption)
