import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricGramHolomorphicFrameForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DivisorDecompositionFlagSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalFlagCoordinates

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

namespace GlobalTheory.HodgeLocGeo

theorem exists_frames_analytic_chart : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β) (F : Type) [Field F] [NumberField F] (e : F ≃+* c.F) (Y : FlagCpt Z e) (σ : F →+* ℂ) (d : ℕ) (c' : AlgChart Y.Y.str σ d) (p0 : Y.Y.pts σ), p0 ∈ c'.finChart.source →
    ∃ (U : Y.Y.X.Opens) (t : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Y.Y.Fnˣ) (V : (gen Z).affineOpens) (φ : c.F →+* Γ(gen Z, V.1))
      (Fr : EigFrame Z φ (LogKS.chart V ≫ genι Z)) (Am : ∀ τ : E →+* ℂ, (Fin d → ℂ) → Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ),
      under p0 ∈ U ∧ LogKS.chart V ≫ genStr Z = spMap φ ∧ Y.down p0 ∈ ptsIn (genStr Z) (embOf e σ) V.1 ∧
      (∀ y' ∈ U, ∀ τ i, (Y.gr τ i).IsEqn y' (t τ i)) ∧
      ∀ᶠ v in 𝓝 (c'.finChart p0), (∀ τ a b, AnalyticAt ℂ (fun w => Am τ w a b) v) ∧
        ∃ (hv : Y.down (c'.finChart.symm v) ∈ ptsIn (genStr Z) (embOf e σ) V.1) (g f : Y.FrameAt (c'.finChart.symm v)),
          Y.Adapted _ t g 1 ∧ Fr.IsMap (evHom hv) f ∧ ∀ τ, f.co g τ = Am τ v := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ _ e Y σ d c' p0 hp0
  obtain ⟨U, t, V, φ, Fr, A, hy, hφ, hUV, ht, hfr⟩ := GlobalTheory.ShFam.FlagFrames.exists_frames_nhds E H Dw l Xo c O β Z F e Y σ (under p0)
  have hp0U : p0 ∈ ptsIn Y.Y.str σ U := mem_ptsIn.2 hy
  refine ⟨U, t, V, φ, Fr, fun τ w => Matrix.of fun a b => ev Y.Y.str σ U (A τ a b) (c'.finChart.symm w),
    hy, hφ, hUV p0 hp0U, ht, ?_⟩
  have hS : IsOpen (c'.finChart.target ∩ c'.finChart.symm ⁻¹' ptsIn Y.Y.str σ U) :=
    c'.finChart.isOpen_inter_preimage_symm (isOpen_ptsIn U)
  have hm : c'.finChart p0 ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' ptsIn Y.Y.str σ U :=
    ⟨c'.finChart.map_source hp0, by rw [Set.mem_preimage, c'.finChart.left_inv hp0]; exact hp0U⟩
  filter_upwards [hS.mem_nhds hm] with v hv
  refine ⟨fun τ a b => (c'.analyticOnNhd_finChart_iff (isOpen_ptsIn U) _).2 (c'.holo U (A τ a b)) v hv, ?_⟩
  obtain ⟨hV, g, f, had, hmap, hco⟩ := hfr _ hv.2
  refine ⟨hV, g, f, had, hmap, fun τ => ?_⟩
  rw [hco τ]
  ext a b
  exact (ev_eq hv.2 _).symm

end GlobalTheory.HodgeLocGeo
