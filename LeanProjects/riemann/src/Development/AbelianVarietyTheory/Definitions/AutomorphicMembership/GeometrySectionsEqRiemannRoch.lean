import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdlCutProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteNonemptyOffCharts

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar Formalism.BasicNotions

namespace GlobalTheory.TrueGeo

def geoTrue (F : Type) [Field F] [NumberField F] [StarRing F] : DV.Geo F := geoOf (cxSt F) (cutSt _) (resSt _)

variable {F : Type} [Field F] [NumberField F] [StarRing F]

section Cut

variable (Y : Var F) (E : Type) [Field E] [NumberField E] [Algebra F E] {n : ℕ} (w : Fin n → Y.Fn)
  (c : Fin Y.dim → Fin n → 𝓞 E)

end Cut

example (n : ℕ) (d : Fin n → ℤ) : (geoTrue F).inter (proj F n) (fun i => d i • projHyp F n) = ∏ i, d i :=
  inter_zsmul_projHyp F n d

example (m : ℤ) : ((geoTrue F).nef (proj F 1) (m • projHyp F 1) ↔ 0 ≤ m) ∧
    ((geoTrue F).big (proj F 1) (m • projHyp F 1) ↔ 0 < m) :=
  ⟨nef_zsmul_projHyp_line F m, big_zsmul_projHyp F 1 le_rfl m⟩

example (Y : (geoTrue F).Var) (σ : F →+* ℂ) (n : ℕ) : Nonempty ((geoTrue F).pts Y σ) ∧
    (geoTrue F).mSmooth (proj F n) σ (projHyp F n) (projMet F σ n) :=
  ⟨Var.nonempty_pts, mSmooth_projMet F σ n⟩

end GlobalTheory.TrueGeo
