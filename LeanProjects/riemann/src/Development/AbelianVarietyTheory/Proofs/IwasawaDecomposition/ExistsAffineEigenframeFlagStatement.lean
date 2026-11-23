import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_eigenframe_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (y : C.Y.X) (V : C.Y.X.Opens), y ∈ V → ∃ (U : C.Y.X.Opens) (hU : IsAffineOpen U) (hy : y ∈ U) (φ : c.F →+* Γ(C.Y.X, U)) (fr : EigFrame Z φ (((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z)) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → C.Y.Fnˣ), U ≤ V ∧ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genStr Z = spMap φ ∧ fr.Tri (fnOf U (gen_mem hy)) C.f0 t ∧ ∀ y' ∈ U, ∀ τ i, (C.gr τ i).IsEqn y' (t τ i) := by
  first | exact @GlobalTheory.ShFam.Spread.exists_frame_nhds | exact GlobalTheory.ShFam.Spread.exists_frame_nhds | (intros; apply GlobalTheory.ShFam.Spread.exists_frame_nhds <;> assumption)
