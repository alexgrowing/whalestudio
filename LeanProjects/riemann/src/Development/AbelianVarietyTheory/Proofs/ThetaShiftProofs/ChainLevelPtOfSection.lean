import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.LevelPointsOfArcEqPeriodDivLevelStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcLevelPointTangentVectorTransportIffStatement

noncomputable section
namespace GlobalTheory.ArcPts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

theorem chain_levelPt_of_section (h1 : Out.Laws) (h2 : Out.Laws2) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ)
    (k : ℕ) [NeZero k] (p₀ : Out.QkPt a.D₀ (FractionRing ℂ) k) (ξ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G)
    (ξ₀ : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G) (la : Λ.A.La)
    (hξ : ξ.left ≫ Y.m0.toSABMap.φ = pullback.fst _ _ ≫ ξ₀.left)
    (hk : (k = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ ξ = Y.oF.etaA v) ∨
      (k = l.M ∧ ∃ v ∈ idealPart D l, HEq p₀ (a.eta v) ∧ ξ = Y.oF.eta v))
    (hrep : Λ.Rep k p₀ la) : C.Φ.LevelPt k (toUnit _ ≫ ξ₀) la := by
  have hξw : ξ.left ≫ Y.oF.t.G.hom = 𝟙 _ := Over.w ξ
  have hY : (C.yF ≫ ξ.left ≫ Y.m.φ) ≫ Y.t.G.hom = gen ≫ χ := by
    have := Y.m.cart.1.w
    rw [Category.assoc, Category.assoc, this, ← Category.assoc ξ.left, hξw, Category.id_comp]
    exact C.yF_j
  let p : Over.mk gen ⟶ W.t.G :=
    Over.homMk (W.m.cart.1.lift (C.yF ≫ ξ.left ≫ Y.m.φ) gen hY) (W.m.cart.1.lift_snd _ _ _)
  have hp : p.left ≫ W.m.φ = C.yF ≫ ξ.left ≫ Y.m.φ := W.m.cart.1.lift_fst _ _ _
  let pY : Over.mk (gen ≫ χ) ⟶ Y.t.G := Over.homMk (C.yF ≫ ξ.left ≫ Y.m.φ) hY
  let pF : Over.mk C.yF ⟶ Y.oF.t.G := toUnit _ ≫ ξ
  have hpF : pF.left = C.yF ≫ ξ.left := rfl
  have hW := GlobalTheory.T.levelPoints_of_arc_eq_period_div_level h1 h2 E H D l Xo c O β Y (bF.comp β) a χ W Λ C.Ξ C.ΦW C.yF k p₀ ξ la p C.isGen C.yF_j
    hk hrep hp
  have h₂ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ W.m C.w₂ _ _ C.ΦW C.ΦY C.rig₂.1 C.rel₂).1 k p pY la hp
  have h₁ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m C.w₁ _ _ C.ΦF C.ΦY C.rig₁.1 C.rel₁).1 k pF pY la
    (by rw [hpF, Category.assoc]; rfl)
  have h₀ := (GlobalTheory.T.arcLevelPoint_tangentVector_transport_iff E H _ _ Λ.A _ _ _ Y.m0.toSABMap C.w₀ _ _ C.ΦF C.Φ C.rig₀.1 C.rel₀).1 k pF
    (toUnit _ ≫ ξ₀) la (by rw [hpF, Category.assoc, hξ, ← Category.assoc]; rfl)
  exact h₀.1 (h₁.2 (h₂.1 hW))

theorem chain_levels : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (bF : c.F →+* ℂ) (a : ArcIn D l β ℂ (bF.comp β)) (χ : Sp ℂ⟦X⟧ ⟶ Y.X) (W : ArcWit Y a (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := ℂ)) PowerSeries.X χ) (Λ : GtAn a) (C : Chain W Λ) (laA laM : D.La → Λ.A.La), (∀ v, Λ.Rep l.A (a.etaA v) (laA v)) → (∀ v, Λ.Rep l.M (a.eta v) (laM v)) → (∀ v, C.Φ.LevelPt l.A (toUnit _ ≫ Xo.univ.etaA v) (laA v)) ∧ ∀ v ∈ idealPart D l, C.Φ.LevelPt l.M (toUnit _ ≫ Xo.univ.eta v) (laM v) := by
  intro h1 h2 E _ _ _ H _ D l Xo c O _ β Y _ _ bF a χ W Λ C laA laM hA hM
  haveI : NeZero l.A := ⟨l.A_pos.ne'⟩
  haveI : NeZero l.M := ⟨by have := l.three_le; omega⟩
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.A (a.etaA v) (Y.oF.etaA v)
      (Xo.univ.etaA v) (laA v) (Y.m0.etaA v) (Or.inl ⟨rfl, v, HEq.rfl, rfl⟩) (hA v)
  · exact chain_levelPt_of_section h1 h2 E H D l Xo c O β Y bF a χ W Λ C l.M (a.eta v) (Y.oF.eta v)
      (Xo.univ.eta v) (laM v) (Y.m0.eta v) (Or.inr ⟨rfl, v, hv, HEq.rfl, rfl⟩) (hM v)

end GlobalTheory.ArcPts
