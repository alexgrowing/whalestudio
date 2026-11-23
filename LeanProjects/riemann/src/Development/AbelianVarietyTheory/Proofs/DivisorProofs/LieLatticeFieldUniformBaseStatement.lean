import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeFieldUniformBase
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermFamGramPosSemidef
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCoordLat
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open AlgebraicGeometry CategoryTheory NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.LieHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.HeightParts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_lattice_field_uniform_base : Hypotheses2 → HypothesesH → GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps.TorusSaturated → OnObj fun D O _ _ H _ => ∀ (x : ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → ∃ C₀ : ℝ, ∀ y : Pt O.s, y ∉ H.int → ∃ (K₀ : Type) (_ : Field K₀) (_ : NumberField K₀) (io₀ : K₀ →+* Qb), ∀ (K : Type) [Field K] [NumberField K] (io : K →+* Qb) (j : K₀ →+* K), io.comp j = io₀ → ∀ (L : Submodule (𝓞 K) (Fin (D.R.f * O.N) → K)) (h : HermFam K (Fin (D.R.f * O.N) → K)), IsLieAtWith O x P y K io L h → ∃ (F : SemiFib K) (h' : HermFam K (Fin F.P₀.g → K)) (r : ℕ) (ε : Fin r → Fin (D.R.f * O.N) → K) (q : (Fin (D.R.f * O.N) → K) →ₗ[K] (Fin F.P₀.g → K)), F.IsHerm h' ∧ TorusExt h L ε q h' F.lieLat C₀ := by
  first | exact @GlobalTheory.BdFib.torusExt_structure | exact GlobalTheory.BdFib.torusExt_structure | (intros; apply GlobalTheory.BdFib.torusExt_structure <;> assumption)
