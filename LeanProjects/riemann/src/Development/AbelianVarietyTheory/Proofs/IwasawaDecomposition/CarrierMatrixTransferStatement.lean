import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CarrierMatrixTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carrier_matrix_transfer : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (s : Z ⟶ Sp O) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)), q ≫ PSpace.str O _ = f ≫ s → ∀ (R K : Type) [CommRing R] [Field K] [Algebra R K] (z : Sp R ⟶ Z) (α : C.A) (_ : ⊤ ≤ z ⁻¹ᵁ C.B α) (n' : ℕ) (a : Matrix (Fin n') (Fin (C.n α)) R) (a' : Matrix (Fin (C.n α)) (Fin n') R) (y : Sp K ⟶ Z') (hy : ⊤ ≤ (y ≫ f) ⁻¹ᵁ C.B α) (ξ : Fin k → Fin (C.n α) → K), a * a' = 1 → a' * a = 1 → y ≫ f = spMap (algebraMap R K) ≫ z → Car Em f q y α hy ξ → (∀ (l : Fin k) (j : Fin n'), k ≤ (j : ℕ) → ∑ i, algebraMap R K (a j i) * ξ l i = 0) → ∃ y₀ : Sp R ⟶ PSpace O (plN N k), y₀ ≫ PSpace.str O _ = z ≫ s ∧ y ≫ q = spMap (algebraMap R K) ≫ y₀ := by
  first | exact @GlobalTheory.GrCl.IntPt.main | exact GlobalTheory.GrCl.IntPt.main | (intros; apply GlobalTheory.GrCl.IntPt.main <;> assumption)
