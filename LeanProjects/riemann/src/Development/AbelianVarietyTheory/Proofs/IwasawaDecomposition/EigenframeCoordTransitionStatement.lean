import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EigenframeCoordTransition
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemNonzeroLocusSecOfRat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PluckerNonzeroIffIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCoordNeZero
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenframe_coord_transition : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (V : (gen s.T.Z).Opens) (hV : IsAffineOpen V) (φ : κ.c.F →+* Γ(gen s.T.Z, V)) (g : EigFrame s.T.Z φ (hV.fromSpec ≫ genι s.T.Z)) (K : Type) [Field K] (c : Γ(gen s.T.Z, V) →+* K) (h h' : EigFrame s.T.Z (c.comp φ) ((spMap c ≫ hV.fromSpec) ≫ genι s.T.Z)) (M M' : GlobalTheory.FlagBundle.Mat S.Dw.mult K), g.Coord c h M → g.Coord c h' M' → (∀ τ, IsUnit (M τ).det) → (∀ τ, IsUnit (M' τ).det) → (∀ τ, ∃ L : Matrix (Fin (S.Dw.mult τ)) (Fin (S.Dw.mult τ)) K, M τ = L * M' τ ∧ ∀ i l, i < l → L i l = 0) → ∃ d, h'.Tri (RingHom.id K) h d := by
  first | exact @GlobalTheory.ShFam.EigFrame.tri_of_coord_lowerTriangular | exact GlobalTheory.ShFam.EigFrame.tri_of_coord_lowerTriangular | (intros; apply GlobalTheory.ShFam.EigFrame.tri_of_coord_lowerTriangular <;> assumption)
