import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AtlasLatticeCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_lattice_coordinates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A), (∀ a, ⊤ ≤ A.ch.χ a ⁻¹ᵁ D.C.B (α a)) → ∃ (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a), IsFrVec D A σ α cv ∧ (∀ a, LeftInv (Dv a) (cv a)) ∧ ∀ (K : Type) [Field K] (a a' : A.ch.ι) (φ : A.ch.R a →+* K) (φ' : A.ch.R a' →+* K), spMap φ ≫ A.ch.χ a = spMap φ' ≫ A.ch.χ a' → ∀ e : ℕ, e ∈ ty σ ∨ e = 0 ∨ e = Dw.mult σ → initSpan K (fun i => φ ∘ cv a i) e = initSpan K (fun i => φ' ∘ cv a' i) e := by
  first | exact @GlobalTheory.GrCl.exists_isFrVec | exact GlobalTheory.GrCl.exists_isFrVec | (intros; apply GlobalTheory.GrCl.exists_isFrVec <;> assumption)
