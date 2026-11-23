import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightBoundTorusPoints
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCochFrame
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory MonObj Matrix Topology
open Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj ComplexOrder
open GlobalTheory GlobalTheory.CubeFib GlobalTheory.LieMet GlobalTheory.LieHt GlobalTheory.LocM.Frm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh GlobalTheory.Toroidal GlobalTheory.HeightParts GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.BdFib
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_bound_torus_points : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (W : Scheme.{0}) (π : W ⟶ gen s.T.Z) (r : ℕ) (u : splitTorus W (Fin r → ℤ) ⟶ (Over.pullback (π ≫ genι s.T.Z)).obj s.T.Z.t.G), IsFinite π → IsMonHom u → (∀ (k : Type) [Field k] (w : Sp k ⟶ W), IsClosedImmersion ((Over.pullback w).map u).left) → ∃ C : ℝ, ∀ (K : Type) [Field K] (w : Sp K ⟶ W) (yK : Sp K ⟶ gen s.T.Z), w ≫ π = yK → ∃ ε : Fin r → TanM (yK ≫ genι s.T.Z) s.T.Z.t.G, IsCochFrame s.T.Z.t (yK ≫ genι s.T.Z) ε ∧ ∀ (σ : K →+* ℂ) (σ' : κ.c.F →+* ℂ) (z : CxPts (genStr s.T.Z) σ') (hz : spMap σ ≫ yK ≫ genι s.T.Z = z.1 ≫ genι s.T.Z), ((C : ℂ) • gramOf (x.met σ' z) (fun i => bcTan σ hz (ε i)) - 1).PosSemidef := by
  first | exact @GlobalTheory.CochGram.gram_lower_bound | exact GlobalTheory.CochGram.gram_lower_bound | (intros; apply GlobalTheory.CochGram.gram_lower_bound <;> assumption)
