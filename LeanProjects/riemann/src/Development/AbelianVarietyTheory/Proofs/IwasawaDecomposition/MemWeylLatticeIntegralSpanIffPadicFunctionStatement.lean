import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemWeylLatticeIntegralSpanIffPadicFunction
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DominantWeightPolynomialFunctionalMinorsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.Columns.TiedValLatG
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_weylLatticeIntegralSpan_iff_padic_function : ∀ {K ι : Type} [Field K] [NumberField K] [Fintype ι] (σ : K →+* ℂ) (Pl : Rows.Places K) (w : Pl.Pl) {p : ℕ} [Fact p.Prime] (φ : K →+* ℂ_[p]), (∀ x, x ∈ intW Pl w ↔ ‖φ x‖ ≤ 1) → ∀ {n : ℕ} (lam : ι → DomWeight n) (G : MvPolynomial (ι × Fin n × Fin n) K), G ∈ Formalism.L2.DIV.VV K lam → (MvPolynomial.map σ G ∈ vlIntSpan σ Pl w lam ↔ (fun y : ι → Matrix (Fin n) (Fin n) ℂ_[p] => MvPolynomial.eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (MvPolynomial.map φ G)) ∈ WeylLatticeDuality.DelW p ι n (fun τ => (lam τ).natW)) := by
  first | exact @GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW | exact GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW | (intros; apply GlobalTheory.Mem.IntSpanDelW.map_mem_vlIntSpan_iff_delW <;> assumption)
