import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLatticeBasisOfEigenvectors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatSectionFrameInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeExistsUniqueOfSamePoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsCombAtGMulVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValueStatementHolds

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel GlobalTheory.Toroidal
open GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.VertForm
open GlobalTheory.DetHT
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.ShFam.Descent

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_lattice_basis_of_eigenvectors : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (p : ℕ) [Fact p.Prime]
    (l : Level H) (c : Coeff l) [Algebra c.F ℂ_[p]],
    letI := H.starRing; ∀ (Q : PtP E p) (τ : Psi H) (n : ℕ) (xx : Fin n → LieG Q.Gt) (g : Matrix (Fin n) (Fin n) ℂ_[p]),
      (∀ j, AvDefs.IsEig Q.Gt Q.oGt (embInt c Q.integers (conjEmb τ.1)) (xx j)) →
      IsLatBasis ℂ_[p] (htLat c Q (conjEmb τ.1)) (fun i => ∑ j, g i j • Q.bLie (xx j)) → ∀ a : Fin n → ℂ_[p],
        (∑ i, a i • ∑ j, g i j • Q.bLie (xx j) ∈ Q.latT ↔ ∀ i, ‖(1 : ℂ_[p]) * a i‖ ≤ 1) := by
  first | exact @GlobalTheory.eigconj_sum_mem_latT_iff | exact GlobalTheory.eigconj_sum_mem_latT_iff | (intros; apply GlobalTheory.eigconj_sum_mem_latT_iff <;> assumption)
