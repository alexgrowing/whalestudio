import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenAction
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tangent_combination_eigen_action : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X), (∀ (n : ℕ) (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R), (∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j) → IsCombAtG t x u cf w → w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w) ∧ ∀ (f : c.F →+* R) (e u : Vecs Dw t R) (w : Pm Dw.mult) (y : CellVar Dw.mult → R), IsFrame t f x e → (∀ τ j, IsCombAtG t x (fun i => e τ (w τ i)) (fun i => cell y τ i j) (u τ j)) → IsFrame t f x u := by
  first | exact @GlobalTheory.FlagEmb.eig_comb_and_frame_cell | exact GlobalTheory.FlagEmb.eig_comb_and_frame_cell | (intros; apply GlobalTheory.FlagEmb.eig_comb_and_frame_cell <;> assumption)
