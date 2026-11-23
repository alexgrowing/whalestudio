import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeNearImage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_eigenframe_near_image : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → IsOpen (Set.range Y.j) ∧ ∀ (x : Y.X) (U : Y.X.Opens), x ∈ U → x ∈ Set.range Y.j → ∃ (V : Y.X.affineOpens) (α : c.F →+* Γ(Y.X, V.1)) (e : Vecs Dw Y.t Γ(Y.X, V.1)) (n : ℕ) (en : Fin n ≃ Let Dw.mult), x ∈ V.1 ∧ V.1 ≤ U ∧ (V.1 : Set Y.X) ⊆ Set.range Y.j ∧ V.2.fromSpec ≫ Y.s = spMap (α.comp (c.V W).subtype) ∧ (∀ (R : Type) [CommRing R] (φ : Γ(Y.X, V.1) →+* R), IsFrame Y.t (φ.comp α) (spMap φ ≫ V.2.fromSpec) (e.bc φ)) ∧ ∀ w, IsTanAtG Y.t V.2.fromSpec w → ∃! a : Fin n → Γ(Y.X, V.1), IsCombAtG Y.t V.2.fromSpec (fun i => e (en i).1 (en i).2) a w := by
  first | exact @GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame | exact GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame | (intros; apply GlobalTheory.FlagEmb.EigSpread.exists_stable_eigFrame <;> assumption)
