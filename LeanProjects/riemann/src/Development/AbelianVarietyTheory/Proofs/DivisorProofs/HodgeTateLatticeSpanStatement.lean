import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeSpan
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdicCompleteDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.Frames GlobalTheory.AllWt GlobalTheory.CompHt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_lattice_span : ∀ {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), HTChar p v P.Gt → ∀ (τ : Λ →+* O) {w : P.V}, w ∈ P.latT → w ∈ Submodule.span C (P.wRec τ : Set P.V) → ∀ {c : O}, v (algebraMap O C c) ^ (p - 1) ≤ v (p : C) → algebraMap O C c • w ∈ P.wRec τ := by
  first | exact @GlobalTheory.CompHt.DualHT.smul_mem_wRec_of_mem_span | exact GlobalTheory.CompHt.DualHT.smul_mem_wRec_of_mem_span | (intros; apply GlobalTheory.CompHt.DualHT.smul_mem_wRec_of_mem_span <;> assumption)
