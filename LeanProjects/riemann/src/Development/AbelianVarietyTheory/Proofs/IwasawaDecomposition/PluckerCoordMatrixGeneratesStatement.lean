import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerCoordMatrixGenerates
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.plucker_coord_matrix_generates : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (Φ : s.Flag) (k : s.Comp) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)), hV.fromSpec ≫ genStr s.T.Z = spMap φ → g.Stable → ∀ (hne : genericPoint (Φ.C k).Y.X ∈ (Φ.C k).π ⁻¹ᵁ V) (B : GlobalTheory.FlagBundle.Mat S.Dw.mult (Φ.C k).Y.Fn), g.Coord (GlobalTheory.FlagAmple.PlkLoc.baseFn (Φ.C k) V hne) (Φ.C k).f0 B → (∀ (x : GlobalTheory.FlagAmple.Step S.Dw) (q : Fin (GlobalTheory.FlagAmple.PlkLoc.plkM x + 1)) (y : (Φ.C k).Y.X), y ∈ (Φ.C k).π ⁻¹ᵁ V → (-GlobalTheory.FlagAmple.detDiv (Φ.C k) x.1 (x.2.1 : ℕ)).RegularAt y (GlobalTheory.FlagAmple.PlkLoc.plkFn B x q)) → ∀ (ht : ∀ x : GlobalTheory.FlagAmple.Step S.Dw, ⨆ q, nonzeroLocus (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x q) = ⊤) (K : Type) [Field K] [IsAlgClosed K] (a a' : Sp K ⟶ ((Φ.C k).π ⁻¹ᵁ V).toScheme), a ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) = a' ≫ (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) → (∀ x, a ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x) (ht x) = a' ≫ GlobalTheory.ProjSpace.toProj (((Φ.C k).π ∣_ V) ≫ hV.isoSpec.hom) (GlobalTheory.FlagAmple.PlkLoc.plkSec (Φ.C k) ((Φ.C k).π ⁻¹ᵁ V) B x) (ht x)) → a = a' := by
  first | exact @GlobalTheory.FlagAmple.PlkLoc.eq_of_toProj_plkSec_eq | exact GlobalTheory.FlagAmple.PlkLoc.eq_of_toProj_plkSec_eq | (intros; apply GlobalTheory.FlagAmple.PlkLoc.eq_of_toProj_plkSec_eq <;> assumption)
