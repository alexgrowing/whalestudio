import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormFieldDbarCohomologousTwoConnectionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRealPolyEqOfDbarCohomologousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFlagGradedLineChernFormsSmoothDbarClosedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGramConnectionPairGramLowerTriangularFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormTriangularConnectionEqEsymmGradedStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChernCalc

theorem evalF_rename_mul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α β : Type}
    (u : α → A.Pt → Ev n) (v : β → A.Pt → Ev n) (R : MvPolynomial α ℝ) (Q : MvPolynomial β ℝ) :
    evalF A (Sum.elim u v) (rename Sum.inl R * rename Sum.inr Q) = evalF A u R * evalF A v Q := by
  funext x
  simp only [evalF, LineForm.fld, Pi.mul_apply, Polynomial.map_mul, MvPolynomial.map_rename, map_mul, aeval_rename]
  rfl

theorem evalF_chernRoots {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {ι : Type} (m : ι → ℕ)
    (c : ι × ℕ → A.Pt → Ev n) (g : Root m → A.Pt → Ev n)
    (h : ∀ τ j p, c (τ, j) p = aeval (fun i => g ⟨τ, i⟩ p) (esymm (Fin (m τ)) ℂ j))
    (R : MvPolynomial (ι × ℕ) ℝ) : evalF A c R = evalF A g (chernRoots m R) := by
  funext p
  simp only [evalF, LineForm.fld]
  congr 1
  rw [aeval_map_algebraMap, aeval_map_algebraMap, chernRoots, ← AlgHom.comp_apply, comp_aeval]
  congr 2
  funext x
  rw [h x.1 x.2 p, aeval_rename, aeval_esymm_eq_multiset_esymm, aeval_esymm_eq_multiset_esymm]
  rfl

theorem integral_chernF_mul_grF : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ) (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) (Q : MvPolynomial (Root m) ℝ), (atlas X σ).integral (evalF (atlas X σ) (chernF E H) R * evalF (atlas X σ) (grF E H) Q) = (atlas X σ).integral (evalF (atlas X σ) (grF E H) (chernRoots m R * Q)) := by
  intro F _ σ X ι _ m E H hH R Q
  let ld : ι × ℕ → (atlas X σ).Pt → Ev X.dim := fun x => chernFld (atlas X σ) (fun y z => ldPart (gramAt E H x.1 y z)) x.2
  have hc : ∀ i, DbarCoh (atlas X σ) (Sum.elim (chernF E H) (grF E H) i) (Sum.elim ld (grF E H) i) := by
    rintro (⟨τ, j⟩ | x)
    · exact GlobalTheory.T.chernFormField_dbarCohomologous_two_connections _ _ _ _ _ _ (GlobalTheory.T.isGramConnectionPair_gram_lower_triangular_factor F σ X ι m E H hH τ) j
    · exact GlobalTheory.T.fullFlagGradedLineChernForms_smooth_dbarClosed F σ X ι m E H hH x
  have key := GlobalTheory.T.integral_realPoly_eq_of_dbarCohomologous (CxPts X.str σ) X.dim (atlas X σ) _ _ _ hc (rename Sum.inl R * rename Sum.inr Q)
  rw [evalF_rename_mul, evalF_rename_mul] at key
  rw [key, evalF_chernRoots (atlas X σ) m ld (grF E H) (fun τ j p => GlobalTheory.T.chernForm_triangular_connection_eq_esymm_graded F σ X ι m E H hH τ j p) R]
  simp only [evalF, LineForm.fld, map_mul]
  rfl

end GlobalTheory.ChernCalc
