import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

theorem GlobalTheory.ArcQ.frChg_exists_unique_units : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y : FrPt Xo c S), ((∀ τ, IsUnit (g τ).det) → IsUnit s → ∃ y', FrChg g s y y') ∧ (∀ y' y'', FrChg g s y y' → FrChg g s y y'' → y' = y'') ∧ (∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s) ∧ ∀ y' : FrPt Xo c S, y'.x = y.x → ∃ (g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s' : S), FrChg g' s' y y' := by
  intro E _ _ _ H Dw l Xo c S _ _ g s y
  have hunit : ∀ y', FrChg g s y y' → (∀ τ, IsUnit (g τ).det) ∧ IsUnit s := by
    intro y' h
    obtain ⟨h1, h2⟩ := GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y'
    obtain ⟨g', a, hg', h'⟩ := h1 h.1
    obtain ⟨e1, e2⟩ := h2 g g' s a h h'
    subst e1 e2
    exact ⟨hg', a.isUnit⟩
  refine ⟨fun hg hs => ?_, fun y' y'' h' h'' => ?_, hunit, fun y' hx => ?_⟩
  · obtain ⟨a, rfl⟩ := hs
    exact (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y g a hg).exists
  · obtain ⟨hg, a, rfl⟩ := hunit y' h'
    exact (GlobalTheory.Frames.existsUnique_frChg E H Dw l Xo c S y g a hg).unique h' h''
  · obtain ⟨g', a, -, h⟩ := (GlobalTheory.Frames.frChg_exists_unique E H Dw l Xo c S y y').1 hx
    exact ⟨g', a, h⟩
