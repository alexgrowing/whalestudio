import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinates
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_flag_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (y : Y.Y.X), ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1)) (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (A : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Γ(Y.Y.X, U)), y ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ (∀ p : Y.Y.pts σ, p ∈ ptsIn Y.Y.str σ U → Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) ∧ (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧ ∀ (p : Y.Y.pts σ) (hp : p ∈ ptsIn Y.Y.str σ U), ∃ (hv : Y.down p ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt p), Y.Adapted p t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = (A τ).map (evHom hp) := by
  first | exact @GlobalTheory.ShFam.FlagFrames.exists_frames_nhds | exact GlobalTheory.ShFam.FlagFrames.exists_frames_nhds | (intros; apply GlobalTheory.ShFam.FlagFrames.exists_frames_nhds <;> assumption)
