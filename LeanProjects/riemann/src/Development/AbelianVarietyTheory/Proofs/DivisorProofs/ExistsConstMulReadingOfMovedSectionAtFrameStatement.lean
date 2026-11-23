import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulReadingOfMovedSectionAtFrame
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPinnedOfIsUnf
open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.GeoLevel GlobalTheory.LevelCusp GlobalTheory.FrameUnif
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_mul_reading_of_moved_section_at_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U U' : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → Formalism.L2.PjFree.IsUnf U' → ∀ (k : U.Comp) (k' : U'.Comp) (δ : GL (Fin r) E) (h : IsMatch (U.X k) (U'.X k') δ) (ρ : Xo.X ⟶ Xo.X) (ν : SABMap Xo.univ.t Xo.univ.t ρ), ρ ≫ Xo.s = Xo.s → MoveMatch U U' k k' h ρ ν → (∀ (x : (U.X k).dom) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), IsUnitFr (U.X k) x.1 → FrMove ρ ν (U.un k x) y' → FrBor t (U'.un k' ⟨_, h.mem_dom x.2⟩) y' → cabs (t none : CAt σ) = 1) → ∀ n : ℕ, ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ w, Dom w n → ∀ f ∈ sec Xo c w n, ∀ f' ∈ sec Xo c w n, (∀ y y' : FrPt Xo c (CAt σ), FrMove ρ ν y y' → evR Xo c f' y = evR Xo c f y') → ∀ x ∈ (U.X k).dom, Formalism.L2.PjFree.rdU U f' k x = ε * Formalism.L2.PjFree.rdU U' f k' (lact δ (castFr h.psi x)) := by
  first | exact @GlobalTheory.GeoLevel.exists_const_rdU_of_moveMatch | exact GlobalTheory.GeoLevel.exists_const_rdU_of_moveMatch | (intros; apply GlobalTheory.GeoLevel.exists_const_rdU_of_moveMatch <;> assumption)
