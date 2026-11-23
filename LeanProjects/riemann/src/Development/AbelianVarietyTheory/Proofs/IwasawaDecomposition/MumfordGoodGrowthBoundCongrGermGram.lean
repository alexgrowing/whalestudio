import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLieBase
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgePeriodGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.GoodMetric

theorem goodBound_congr_nhds (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (c : ℝ) (N : ℕ)
    (G G' : ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n) :
    G =ᶠ[nhds v] G' → GlobalTheory.GoodMetric.GoodBound S c N G v → GlobalTheory.GoodMetric.GoodBound S c N G' v := by
  intro h hb
  have hv : G v = G' v := h.eq_of_nhds
  have hc : ∀ ξ, (fun u => GlobalTheory.HermFrame.conn G u ξ) =ᶠ[nhds v] (fun u => GlobalTheory.HermFrame.conn G' u ξ) :=
    fun ξ => h.eventuallyEq_nhds.mono fun x hx => GlobalTheory.HermFrame.conn_congr hx ξ
  refine ⟨fun i j => ?_, ?_, fun a i j => ?_, fun a b i j => ?_, fun a b i j => ?_⟩
  · rw [← hv]; exact hb.entry i j
  · rw [← hv]; exact hb.det
  · rw [← GlobalTheory.HermFrame.conn_congr h]; exact hb.form a i j
  · rw [← GlobalTheory.HermFrame.curv_congr h]; exact hb.dbar a b i j
  · rw [← GlobalTheory.HermFrame.mdel_congr (hc _), ← GlobalTheory.HermFrame.mdel_congr (hc _)]; exact hb.del a b i j

end GlobalTheory.GoodMetric
