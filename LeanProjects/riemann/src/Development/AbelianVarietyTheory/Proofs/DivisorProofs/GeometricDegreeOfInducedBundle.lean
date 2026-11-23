import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonRefinementModels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InducedMetricPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArTopOfInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibPullback
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BijectiveCompAlgebraMap
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.TrueGeo GlobalTheory.ArInt ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.ProjVar

noncomputable section

namespace GlobalTheory.ReadModel

theorem gdeg_induced : GlobalTheory.Published.ArDegree → ∀ (F : Type) [Field F] [NumberField F] (C : CxSt F) (Y : Var F) (A : Adl C Y) (P : TrueGeo.Model Y) (L : HermLB P.p) (k : ℕ+) (cf : HeightOneSpectrum (𝓞 F) → ℝ), A.Induced P L k cf → gdeg L Y.dim = (Module.finrank ℤ (𝓞 F) : ℝ) * (((k : ℕ) : ℝ) * ((A.n : ℕ) : ℝ)) ^ Y.dim * A.deg := by
  intro hD F _ _ C Y A P L k cf ⟨_, r, hr, _⟩
  let E := Equiv.ofBijective _ (GlobalTheory.TwistTop.bijective_comp_algebraMap F)
  have e (σ : F →+* ℂ) : (L.φ (E σ)).chernInt Y.dim Set.univ (fun _ => 1) =
      ((k : ℕ) : ℝ) ^ Y.dim * (Y.inter (fun _ => A.D) : ℝ) := by
    have h := GlobalTheory.TwistTop.chernInt_model hD.2 P L hr σ
    rw [Var.inter_const_nsmul] at h
    push_cast at h
    exact h
  have hn : ((A.n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast A.n.ne_zero
  simp only [gdeg, chInt]
  rw [← finsum_comp_equiv E, finsum_eq_sum_of_fintype]
  simp only [e, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [NumberField.Embeddings.card, ← NumberField.RingOfIntegers.rank, Adl.deg, mul_pow]
  field_simp

end GlobalTheory.ReadModel

end
