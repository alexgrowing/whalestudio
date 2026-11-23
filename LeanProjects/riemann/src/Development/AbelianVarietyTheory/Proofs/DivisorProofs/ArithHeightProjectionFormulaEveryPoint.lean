import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightPullbackResidueDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaPointCurveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightProjectionFormulaInductiveStepStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem hasDim_iff_clo {Y : Scheme.{0}} (y : Y) (e : ℕ) : HasDim y e ↔ topologicalKrullDim (clo y) = (e : ℕ) := by
  have hemb := (cloι y).isClosedEmbedding
  have hr : Set.range (cloι y) = closure ({y} : Set Y) := by
    rw [← Set.image_univ, ← (genericPoint_spec (clo y)).def, ← hemb.isClosedMap.closure_image_eq_of_continuous
      hemb.continuous, Set.image_singleton, cloι_genericPoint]
  have h := (hemb.toIsEmbedding.toHomeomorph).isHomeomorph.topologicalKrullDim_eq
  unfold HasDim
  rw [h, hr]

theorem heightProj : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (D E : ℕ),
    IsArithVar p D → IsArithVar q E → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q) (L : HermLB p) (h : X → ℝ) (h' : Y → ℝ),
    L.IsArithHeight h → (L.pull π hπ).IsArithHeight h' → ∀ y : Y, h' y = (π.residueDegree y : ℝ) * h (π y) := by
  intro k _ X Y p q D E hX hY π hπ L h h' H H'
  have key : ∀ (n : ℕ) (w : Y), HasDim w (n + 1) → h' w = (π.residueDegree w : ℝ) * h (π w) := by
    intro n
    induction n with
    | zero =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_pointCurve k X Y p q D E hX hY π hπ L h h' H H' w hc hw
    | succ m ih =>
      intro w hw
      rcases hY.vertical_or_horizontal (cloι w) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
      · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' w l hl
      · exact GlobalTheory.T.arithHeight_projectionFormula_inductiveStep k X Y p q D E hX hY π hπ L h h' H H' w m hc hw ih
  intro y
  rcases hY.vertical_or_horizontal (cloι y) with ⟨l, _, hl⟩ | ⟨hc, e, he⟩
  · exact GlobalTheory.T.arith_height_pullback_residue_degree k X Y p q D E hX hY π hπ L h h' H H' y l hl
  · exact key e y ((hasDim_iff_clo y (e + 1)).2 he)

end GlobalTheory.MixHt
