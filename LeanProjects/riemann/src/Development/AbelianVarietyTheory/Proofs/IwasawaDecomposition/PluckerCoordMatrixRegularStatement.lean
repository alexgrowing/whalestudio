import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerCoordMatrixRegular
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_coord_matrix_regular : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ (hne : genericPoint (Φ.C k).Y.X ∈ (Φ.C k).π ⁻¹ᵁ V) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), g.Coord (GlobalTheory.FlagAmple.PlkLoc.baseFn (Φ.C k) V hne) (Φ.C k).f0 B → ∀ y : (Φ.C k).Y.X, y ∈ (Φ.C k).π ⁻¹ᵁ V → ∃ (t : ∀ τ : D.host.E →+* ℂ, Fin (S.Dw.mult τ) → (Φ.C k).Y.Fnˣ) (T : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn) (By : GlobalTheory.FlagBundle.Mat S.Dw.mult ((Φ.C k).Y.X.presheaf.stalk y)), (∀ τ a, ((Φ.C k).gr τ a).IsEqn y (t τ a)) ∧ (∀ τ a, T τ a a = t τ a) ∧ (∀ τ (a b : Fin (S.Dw.mult τ)), a < b → T τ a b = 0) ∧ (∀ τ, IsUnit (By τ)) ∧ ∀ τ, B τ = T τ * (By τ).map (algebraMap ((Φ.C k).Y.X.presheaf.stalk y) (Φ.C k).Y.Fn) := by
  first | exact @GlobalTheory.FlagAmple.PlkLoc.exists_tri_mul_unit_of_coord | exact GlobalTheory.FlagAmple.PlkLoc.exists_tri_mul_unit_of_coord | (intros; apply GlobalTheory.FlagAmple.PlkLoc.exists_tri_mul_unit_of_coord <;> assumption)
