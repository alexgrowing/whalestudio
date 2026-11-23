import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellAtlasFromLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_atlas_from_lattice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (D : LCrd M π) (σ : E →+* ℂ) (α : A.ch.ι → D.C.A) (cv Dv : ∀ a, Fin (Dw.mult σ) → Fin (D.N + 1) → A.ch.R a) (a k b : ℕ) (hk : k ≤ Dw.mult σ) (X' : Scheme.{0}) (f : X' ⟶ X) (q : X' ⟶ PSpace V (plN D.N k)) (κ : ∀ j : A.ch.ι, GPm (Dw.mult σ) a b → (Sp (MvPolynomial (GVar (Dw.mult σ) a k b) (A.ch.R j)) ⟶ X')) (ty' : (E →+* ℂ) → Finset ℕ), a ≤ k → k ≤ b → (a ∈ ty σ ∨ a = 0) → (b ∈ ty σ ∨ b = Dw.mult σ) → (∀ e ∈ ty σ, e ≤ a ∨ b ≤ e) → (∀ j, ⊤ ≤ A.ch.χ j ⁻¹ᵁ D.C.B (α j)) → IsFrVec D A σ α cv → (∀ j, LeftInv (Dv j) (cv j)) → CellCl (π ≫ M.s) A.ch (fun j => (A.alg j).comp V.subtype) (fun j => gxi a b hk (cv j)) f q κ → ty' σ = insert k (ty σ) → (∀ σ', σ' ≠ σ → ty' σ' = ty σ') → ∃ A' : Atlas M (f ≫ π) ty', GRel D A σ hk f q A' := by
  first | exact @GlobalTheory.GrCl.CellAtlas.exists_cellAtlas | exact GlobalTheory.GrCl.CellAtlas.exists_cellAtlas | (intros; apply GlobalTheory.GrCl.CellAtlas.exists_cellAtlas <;> assumption)
