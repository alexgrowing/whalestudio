import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MetricConjugationSymmetry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjRiemannData
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

namespace GlobalTheory.HodgeConj

theorem hermForm_star {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm (Hm.map star) (star z) (star w) = starRingEnd ℂ (hermForm Hm z w) := by
  unfold hermForm
  simp [dotProduct, Matrix.mulVec, map_sum, Complex.star_def]

open scoped CategoryTheory.Obj in

theorem exists_conj_tangent {T : Scheme.{0}} {P : PPAS T} {y : Sp ℂ ⟶ T} (d : P.RiemannData y) {z : Fin P.g → ℂ}
    {v : epsR ℂ ⟶ d.B} (ht : IsTangent v) (hd : d.u.IsDiff z v) :
    ∃ v' : epsR ℂ ⟶ d.conj.B, IsTangent v' ∧ d.conj.u.IsDiff (star z) v' ∧
      v'.left ≫ d.conj.φ = spMap (Formalism.L2.Pj.dualMap (starRingEnd ℂ)) ≫ v.left ≫ d.φ := by
  have hc : IsGrpPullback d.conj.B d.B GlobalTheory.ArchMetricCompare.cj _ := isGrpPullback_pullback d.B GlobalTheory.ArchMetricCompare.cj
  obtain ⟨v', hv'⟩ := (GlobalTheory.existsUnique_isVecOver (f := starRingEnd ℂ) (A' := d.conj.B) hc.1 v).exists
  refine ⟨v', hv'.isTangent hc ht, GlobalTheory.ArchMetricCompare.cj_isDiff hc (ConjUnif.pullId d.u) ht hv' hd, ?_⟩
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ d.φ) hv')).trans (Category.assoc _ _ _)

theorem hodge_eq_riemann_of_good : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (T : Scheme.{0}) (b : T ⟶ s.T.Z.X) (Q : Out.PolAV T) (θ : Q.A.left ⟶ s.T.Z.t.G.left), IsGrpPullback Q.A s.T.Z.t.G b θ → LBIso (s.T.Z.t.PP.L.pull θ) Q.L → (∀ (σ' : κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb κ.c σ' → ∀ (yc : CxPts (genStr s.T.Z) σ') (y₀ : Sp ℂ ⟶ T), y₀ ≫ b = yc.1 ≫ genι s.T.Z → ∀ (u : EigFrame s.T.Z σ' (yc.1 ≫ genι s.T.Z)) (d : (PPAS.ofPolAV Q).RiemannData y₀) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → Fin Q.g → ℂ), (∀ τ i, ∃ v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff (z τ i) v ∧ v.left ≫ d.φ ≫ θ = u.v τ i) → (∀ τ b₁ b₂, (x.hodge σ').gram yc u τ b₁ b₂ = (Real.pi : ℂ) * hermForm d.H (z τ b₂) (z τ b₁)) ∧ ∀ τ τ' b₁ b₂, τ ≠ τ' → hermForm d.H (z τ b₁) (z τ' b₂) = 0) → ∀ (σ' : κ.c.F →+* ℂ), ∀ (yc : CxPts (genStr s.T.Z) σ') (y₀ : Sp ℂ ⟶ T), y₀ ≫ b = yc.1 ≫ genι s.T.Z → ∀ (u : EigFrame s.T.Z σ' (yc.1 ≫ genι s.T.Z)) (d : (PPAS.ofPolAV Q).RiemannData y₀) (z : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → Fin Q.g → ℂ), (∀ τ i, ∃ v : epsR ℂ ⟶ d.B, IsTangent v ∧ d.u.IsDiff (z τ i) v ∧ v.left ≫ d.φ ≫ θ = u.v τ i) → (∀ τ b₁ b₂, (x.hodge σ').gram yc u τ b₁ b₂ = (Real.pi : ℂ) * hermForm d.H (z τ b₂) (z τ b₁)) ∧ ∀ τ τ' b₁ b₂, τ ≠ τ' → hermForm d.H (z τ b₁) (z τ' b₂) = 0 := by
  intro D A N j S κ s x T b Q θ _ _ H σ' yc y₀ hy u d z hz
  by_cases hσ : Formalism.L2.PjFree.GoodEmb κ.c σ'
  · exact H σ' hσ yc y₀ hy u d z hz
  have h1 : Formalism.L2.PjFree.GoodEmb κ.c ((starRingEnd ℂ).comp σ') := by
    have h0 : ¬ Formalism.L2.Pj.GoodEmb κ.c σ' := hσ
    have h2 : Formalism.L2.Pj.GoodEmb κ.c ((starRingEnd ℂ).comp σ') := by
      simpa only [Formalism.L2.Pj.goodOf, if_neg h0] using Formalism.L2.Pj.goodEmb_goodOf κ.c σ'
    exact h2
  let y' : CxPts (genStr s.T.Z) ((starRingEnd ℂ).comp σ') :=
    ⟨spMap (starRingEnd ℂ) ≫ yc.1, by rw [Category.assoc, yc.2, ← Spec.map_comp]; rfl⟩
  obtain ⟨u', hu'⟩ := u.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ') (x' := y'.1 ≫ genι s.T.Z) rfl
    (Category.assoc _ _ _)
  obtain ⟨k₁, k₂⟩ := H _ h1 y' (spMap (starRingEnd ℂ) ≫ y₀) (by rw [Category.assoc, hy]; exact (Category.assoc _ _ _).symm)
    u' d.conj (fun τ i => star (z τ i)) fun τ i => by
      obtain ⟨v, ht, hd, hv⟩ := hz τ i
      obtain ⟨v', ht', hd', hv'⟩ := exists_conj_tangent d ht hd
      refine ⟨v', ht', hd', ?_⟩
      rw [hu' τ i, ← hv]
      exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ θ) hv')).trans
        ((Category.assoc _ _ _).trans (congrArg _ (Category.assoc _ _ _)))
  refine ⟨fun τ b₁ b₂ => ?_, fun τ τ' b₁ b₂ hτ => ?_⟩
  · have e := k₁ τ b₁ b₂
    rw [ConjMet.hodge_conj x (y := yc) (y' := y') rfl rfl hu' τ, Matrix.map_apply] at e
    have e' := e.trans (congrArg _ (hermForm_star d.H (z τ b₂) (z τ b₁)))
    rw [← Complex.conj_ofReal, ← map_mul] at e'
    exact (starRingEnd ℂ).injective e'
  · have e := (hermForm_star d.H (z τ b₁) (z τ' b₂)).symm.trans (k₂ τ τ' b₁ b₂ hτ)
    exact (map_eq_zero _).1 e

end GlobalTheory.HodgeConj
