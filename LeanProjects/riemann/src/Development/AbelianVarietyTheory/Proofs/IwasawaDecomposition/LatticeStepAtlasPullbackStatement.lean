import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeStepAtlasPullback
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_step_atlas_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X) (D : LCrd (Y Z.i) Z.π), IsMap Z t.B g → IsLat t Z g D → ∀ (A : Atlas (Y Z.i) Z.π Z.ty) (X' : Scheme.{0}) (f : X' ⟶ Z.X) (q : X' ⟶ PSpace (Z.i.c.V W) (plN D.N t.k)) (ty' : (E →+* ℂ) → Finset ℕ) (A' : Atlas (Y Z.i) (f ≫ Z.π) ty'), (∀ (K : Type) [Field K] (w : Sp K ⟶ Z.X) (u : Vecs Dw (Y Z.i).t K), A.FlagAt w u ↔ Z.FlagAt w u) → GRel D A t.σ t.le f q A' → Planar D.Em f q → ∀ (Z₁ : Mdl Y i₀) (h : Z₁.X ⟶ X'), MapsTo Z₁ A' h → IsMap Z₁ Z (h ≫ f) → t.k ∈ Z₁.ty t.σ → t.Holds Z₁ := by
  first | exact @GlobalTheory.GrCl.RowCombination.holds_of_planar | exact GlobalTheory.GrCl.RowCombination.holds_of_planar | (intros; apply GlobalTheory.GrCl.RowCombination.holds_of_planar <;> assumption)
