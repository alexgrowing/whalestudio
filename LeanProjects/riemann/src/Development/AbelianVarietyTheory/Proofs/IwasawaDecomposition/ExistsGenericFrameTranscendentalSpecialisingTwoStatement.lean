import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGenericFrameTranscendentalSpecialisingTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFrame_transcendental_specialising_two : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ Z.X) (g g' : EigFrame Z χ x) (L : Type) [Field L] (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) → ∀ (xL : Sp L ⟶ Z.X), xL = spMap ι ≫ x → ∃ gL : EigFrame Z (ι.comp χ) xL, ∀ (V : Type) [CommRing V] [IsLocalRing V] (ν : V →+* L) (ιV : K →+* V) (r : V →+* K) (sV : V), ν.comp ιV = ι → r.comp ιV = RingHom.id K → RingHom.ker r = IsLocalRing.maximalIdeal V → ν sV = s → (r sV = 0 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g tk) ∧ (r sV = 1 → ∃ (gV : EigFrame Z (ιV.comp χ) (spMap ιV ≫ x)) (tL : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Lˣ) (tk : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Kˣ), gV.Tri ν gL tL ∧ gV.Tri r g' tk) := by
  first | exact @GlobalTheory.GenFrame.exists_generic_frame | exact GlobalTheory.GenFrame.exists_generic_frame | (intros; apply GlobalTheory.GenFrame.exists_generic_frame <;> assumption)
