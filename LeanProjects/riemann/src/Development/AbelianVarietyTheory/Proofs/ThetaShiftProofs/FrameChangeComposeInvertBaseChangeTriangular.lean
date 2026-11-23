import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFramedPointChangedByLetters
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeCommBaseChange
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LowerTriIsUnitDet

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frChg_calculus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S], (∀ (g g' : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s s' : S) (y y' y'' : FrPt Xo c S), FrChg g s y y' → (FrChg g' s' y' y'' ↔ FrChg (fun τ => g' τ * g τ) (s' * s) y y'')) ∧ (∀ y : FrPt Xo c S, FrChg (fun _ => 1) 1 y y) ∧ (∀ (T : Type) [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T) (g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S) (s : S) (y y' : FrPt Xo c S) (z z' : FrPt Xo c T), FrChg g s y y' → FrMap φ y z → (FrMap φ y' z' ↔ FrChg (fun τ => (g τ).map φ) (φ s) z z')) ∧ ∀ (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S), FrBor t y y' ↔ ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S, (∀ τ i, g τ i i = (t (some ⟨τ, i⟩) : S)) ∧ (∀ τ i j, i < j → g τ i j = 0) ∧ FrChg g (t none : S) y y' := by
  intro E _ _ _ H Dw l Xo c S _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g g' s s' y y' y'' h
    refine ⟨fun h' => (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 g g' s s' h h', fun h' => ?_⟩
    have hx : y'.x = y.x := h.1
    have hx' : y''.x = y.x := h'.1
    obtain ⟨g₀, a₀, hg₀, h₀⟩ := (frChg_exists_unique E H Dw l Xo c S y y').1 hx
    obtain ⟨rfl, rfl⟩ := (frChg_exists_unique E H Dw l Xo c S y y').2 _ _ _ _ h h₀
    obtain ⟨k, b, -, hk⟩ := (frChg_exists_unique E H Dw l Xo c S y' y'').1 (hx'.trans hx.symm)
    have hc := (frChg_refl_and_comp E H Dw l Xo c S y y' y'').2 _ _ _ _ h hk
    obtain ⟨e₁, e₂⟩ := (frChg_exists_unique E H Dw l Xo c S y y'').2 _ _ _ _ h' hc
    have e₃ : g' = k := by
      funext τ
      exact ((Matrix.isUnit_iff_isUnit_det _).2 (hg₀ τ)).mul_right_cancel (congrFun e₁ τ)
    have e₄ : s' = (b : S) := a₀.isUnit.mul_right_cancel e₂
    rw [e₃, e₄]
    exact hk
  · intro y
    exact (frChg_refl_and_comp E H Dw l Xo c S y y y).1
  · intro T _ _ φ g s y y' z z' h hm
    exact ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g s h hm
  · intro t y y'
    rw [(frBor_calculus E H Dw l Xo c S y y' y').1 t]
    exact ⟨fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩, fun ⟨g, a, b, c⟩ => ⟨g, b, a, c⟩⟩

end GlobalTheory.Frames
