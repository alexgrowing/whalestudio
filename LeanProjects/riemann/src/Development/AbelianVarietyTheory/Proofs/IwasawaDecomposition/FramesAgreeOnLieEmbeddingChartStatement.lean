import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FramesAgreeOnLieEmbeddingChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frames_agree_on_lie_embedding_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X) (L : FinLB X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd t L M), IsLieEmb t L aff crd → ∀ (i : Fin L.n) (R : Type) [CommRing R] (φ : Γ(X, L.U i) →+* R) (x : Sp R ⟶ X) (f f' : c.F →+* R) (u u' : Vecs Dw t R), spMap φ ≫ (aff i).fromSpec = x → IsFrame t f x u → IsFrame t f' x u' → (SameFlag (fun τ => Finset.range (Dw.mult τ + 1)) t x u u' ↔ ∃ d, Tri (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2)) d) ∧ (∀ τ, LinearIndependent R fun j => crd i R φ (u τ j)) ∧ (f = f' → InBlock (fun z : Let Dw.mult => crd i R φ (u z.1 z.2)) (fun z => crd i R φ (u' z.1 z.2))) := by
  first | exact @GlobalTheory.FlagEmb.sameFlag_iff_tri_crd | exact GlobalTheory.FlagEmb.sameFlag_iff_tri_crd | (intros; apply GlobalTheory.FlagEmb.sameFlag_iff_tri_crd <;> assumption)
