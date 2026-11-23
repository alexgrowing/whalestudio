import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellsOfChartsPolynomial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cells_of_charts_polynomial : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] (Z : Scheme.{0}) (s : Z ⟶ Sp O), IsProjOver s → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → Flat s → ∀ (ch : Charts Z) (g : ∀ a, O →+* ch.R a) (V J : Type) [Finite V] [Finite J] (N : ℕ) (ξ : ∀ a, J → Fin (N + 1) → MvPolynomial V (ch.R a)) (ℓ : ∀ a, J → Fin (N + 1) → ch.R a), (∀ a, ch.χ a ≫ s = spMap (g a)) → (∀ a, Cells (MvPolynomial.C : ch.R a →+* MvPolynomial V (ch.R a)) (ξ a) (ℓ a)) → (∀ (K : Type) [Field K] (a a' : ch.ι) (φ : ch.R a →+* K) (j' : J) (ψ' : MvPolynomial V (ch.R a') →+* K), spMap φ ≫ ch.χ a = spMap (ψ'.comp MvPolynomial.C) ≫ ch.χ a' → ∃ (j : J) (ψ : MvPolynomial V (ch.R a) →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ ξ a' j' = (u : K) • (ψ ∘ ξ a j)) → ∃ (Z' : Scheme.{0}) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O N) (κ : ∀ a, J → (Sp (MvPolynomial V (ch.R a)) ⟶ Z')), CellCl s ch g ξ f q κ := by
  first | exact @GlobalTheory.GrCl.exists_cellCl | exact GlobalTheory.GrCl.exists_cellCl | (intros; apply GlobalTheory.GrCl.exists_cellCl <;> assumption)
