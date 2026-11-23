import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameDescendsSubfield
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_descends_subfield : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} {c : Coeff l}
    {X : Scheme.{0}} (t : SAB H X) (ty : (E →+* ℂ) → Finset ℕ) {K' : Type} [Field K'] (L₀ : Subfield K')
    (f : c.F →+* L₀) (y₀ : Sp L₀ ⟶ X) (v : Vecs Dw t L₀) (u : Vecs Dw t K'),
    (∀ (R : Type) [Field R] (g : L₀ →+* R), IsFrame t (g.comp f) (spMap g ≫ y₀) (v.bc g)) →
    IsFrame t (L₀.subtype.comp f) (spMap L₀.subtype ≫ y₀) u →
    ∃ (L : Subfield K') (hL : L₀ ≤ L) (cf : Fin (∑ τ : E →+* ℂ, (Dw.mult τ).choose 2) → K'),
      L ≤ Subfield.closure ((L₀ : Set K') ∪ Set.range cf) ∧ ∃ uL : Vecs Dw t L,
        IsFrame t ((Subfield.inclusion hL).comp f) (spMap (Subfield.inclusion hL) ≫ y₀) uL ∧
        IsFrame t (L₀.subtype.comp f) (spMap L₀.subtype ≫ y₀) (uL.bc L.subtype) ∧
        SameFlag ty t (spMap L₀.subtype ≫ y₀) u (uL.bc L.subtype) := by
  first | exact @GlobalTheory.FrameDescent.exists_frame_flag | exact GlobalTheory.FrameDescent.exists_frame_flag | (intros; apply GlobalTheory.FrameDescent.exists_frame_flag <;> assumption)
