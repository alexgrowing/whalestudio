import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellCoordinatesBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cell_coordinates_base_change : ∀ (K R R' : Type) [Field K] [CommRing R] [CommRing R'] (m a k b N : ℕ) (hk : k ≤ m) (D c : Fin m → Fin (N + 1) → R) (D' c' : Fin m → Fin (N + 1) → R') (φ : R →+* K) (ψ' : MvPolynomial (GVar m a k b) R' →+* K) (w' : GPm m a b), a ≤ k → k ≤ b → LeftInv D c → LeftInv D' c' → (∀ e : ℕ, e = a ∨ e = b → initSpan K (fun l => φ ∘ c l) e = initSpan K (fun l => (ψ'.comp MvPolynomial.C) ∘ c' l) e) → (∃ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0) ∧ ∀ w : GPm m a b, ∑ q, φ (gell a b hk D w q) * ψ' (gxi a b hk c' w' q) ≠ 0 → ∃ (ψ : MvPolynomial (GVar m a k b) R →+* K) (u : Kˣ), ψ.comp MvPolynomial.C = φ ∧ ψ' ∘ gxi a b hk c' w' = (u : K) • (ψ ∘ gxi a b hk c w) := by
  first | exact @GlobalTheory.GrCl.CellGlue.mem_cell_of_initSpan_eq | exact GlobalTheory.GrCl.CellGlue.mem_cell_of_initSpan_eq | (intros; apply GlobalTheory.GrCl.CellGlue.mem_cell_of_initSpan_eq <;> assumption)
