import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlowupEffectiveCartierCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriModOfBlockTriangular
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx GlobalTheory.ConstLat GlobalTheory.LatChain Filter Topology
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blowup_effective_cartier_cover : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p ≠ 0 → ∀ J : V.X.IdealSheafData, (∀ x ∈ J.support, x ∉ V.X.basicOpen (p : Γ(V.X, ⊤))) → ∃ (V' : Cover Y) (Z : Scheme.{0}) (b : Z ⟶ V.X) (ν : V'.X ⟶ Z), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) ∧ (ν ≫ b) ≫ V.p = V'.p ∧ Lies V' V (ν ≫ b) := by
  first | exact @GlobalTheory.LatChain.BlowDom.exists_cover_over_blowup | exact GlobalTheory.LatChain.BlowDom.exists_cover_over_blowup | (intros; apply GlobalTheory.LatChain.BlowDom.exists_cover_over_blowup <;> assumption)
