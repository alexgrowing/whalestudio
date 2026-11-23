import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemClosureIffMapMemMatrixHomLatticeCompletion
import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesLaw
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceRepresentativesTrivial
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemHomLat
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Matrix GlobalTheory.VolAt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_iff_map_mem_matrixHomLattice_completion : ∀ {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) {W Qq : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq] [Algebra W Qq] [IsFractionRing W Qq] (p : ℕ) (hp : Irreducible (p : W)) (ρ : E →+* Qq) (h2 : ∀ (y : W) (n : ℕ), ∃ (x : 𝓞 E) (z : W), ρ x = algebraMap W Qq (y + (p : W) ^ n * z)) (φ : P.adicCompletion E ≃+* Qq) (hφ : ∀ x : E, φ (algebraMap E (P.adicCompletion E) x) = ρ x) (hop : ∀ n : ℕ, IsOpen {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)}) (hnb : ∀ U ∈ nhds (0 : P.adicCompletion E), ∃ n : ℕ, {z : P.adicCompletion E | ∃ w : W, φ z = algebraMap W Qq ((p : W) ^ n * w)} ⊆ U) {k k' : ℕ} (Y : Submodule (𝓞 E) (Matrix (Fin k') (Fin k) E)) (a : Matrix (Fin k) (Fin k) Qq) (b : Matrix (Fin k') (Fin k') Qq) (ha : IsUnit a.det) (hb : IsUnit b.det) (hY : ∀ A ∈ Y, A.map ρ ∈ homLat W (colSpan W a) (colSpan W b)) (hT : homLat W (colSpan W a) (colSpan W b) ≤ Submodule.span W ((fun A : Matrix (Fin k') (Fin k) E => A.map ρ) '' (Y : Set (Matrix (Fin k') (Fin k) E)))) (y : Matrix (Fin k') (Fin k) (P.adicCompletion E)), y ∈ (Y.toAddSubgroup.map ((algebraMap E (P.adicCompletion E)).toAddMonoidHom.mapMatrix)).topologicalClosure ↔ y.map φ ∈ homLat W (colSpan W a) (colSpan W b) := by
  first | exact @GlobalTheory.VolAt.mem_closure_iff_map_mem_homLat | exact GlobalTheory.VolAt.mem_closure_iff_map_mem_homLat | (intros; apply GlobalTheory.VolAt.mem_closure_iff_map_mem_homLat <;> assumption)
