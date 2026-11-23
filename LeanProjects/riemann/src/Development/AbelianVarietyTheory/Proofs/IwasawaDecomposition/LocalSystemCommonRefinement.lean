import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LineModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingHomExtValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CorrespondenceDiagonalStatement

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

theorem GlobalTheory.ShFam.Pad.exists_dominating_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → (N2 Y ∧ ∀ i, (Y i).SplitFibres ∧ (Y i).N3 ∧ (Y i).N4) → ∀ (n : ℕ) (Z : Fin (n + 1) → Mdl Y i₀), (∀ a, (Z a).i = (Z 0).i ∧ (Z a).ty = (Z 0).ty) → ∃ Z' : Mdl Y i₀, Z'.i = (Z 0).i ∧ Z'.ty = (Z 0).ty ∧ ∀ a, ∃ f : Z'.X ⟶ (Z a).X, IsMap Z' (Z a) f :=
  fun E _ _ _ H Dw Xo p W Y i₀ hp hW hN n Z hZ =>
    GlobalTheory.LocM.MapComp.exists_dominating (fun Z₁ Z₂ h => ⟨_, GlobalTheory.T.correspondence_diagonal E H Dw Xo p W hp hW Y i₀ hN.1 Z₁ Z₂ h⟩) n Z hZ
