import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineRefinementLieEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_refinement_lie_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p : ℕ) (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (L : FinLB Y.X) (aff : ∀ i, IsAffineOpen (L.U i)) (M : ℕ) (crd : Crd Y.t L M), IsLieEmb Y.t L aff crd → ∃ (n : ℕ) (V : Fin n → Y.X.affineOpens) (ι : Fin n → Fin L.n) (ρ : ∀ b, Γ(Y.X, L.U (ι b)) →+* Γ(Y.X, (V b).1)) (α : ∀ b, c.F →+* Γ(Y.X, (V b).1)) (e : ∀ b, Vecs Dw Y.t Γ(Y.X, (V b).1)) (D : ∀ b, Let Dw.mult → Fin (M + 1) → Γ(Y.X, (V b).1)), IsFrameCover Y L aff crd V ι ρ α e D := by
  first | exact @GlobalTheory.FlagEmb.exists_isFrameCover | exact GlobalTheory.FlagEmb.exists_isFrameCover | (intros; apply GlobalTheory.FlagEmb.exists_isFrameCover <;> assumption)
