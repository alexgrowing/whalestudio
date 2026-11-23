import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Mean4O GlobalTheory.Mean4 ReciprocityTheory.AnForm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory GlobalTheory.CxPts

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HodgeLocCoord

theorem pn_eq_normSq_mul_near : ∀ {F : Type} [Field F] [NumberField F] (Y : Var F) (σ : F →+* ℂ) {e : ℕ} (c' : AlgChart Y.str σ e)
    (p0 : Y.pts σ), p0 ∈ c'.finChart.source → ∀ (Δ : Y.Dv) (a : Y.Fnˣ) (U : Y.X.Opens), under p0 ∈ U →
    (∀ y' ∈ U, Δ.IsEqn y' a) → ∀ f : Y.Fn, Δ.GeneratesAt (under p0) f →
    ∃ g : (Fin e → ℂ) → ℂ, g (c'.finChart p0) ≠ 0 ∧ ∀ᶠ v in 𝓝 (c'.finChart p0), AnalyticAt ℂ g v ∧
      c'.finChart.symm v ∈ Var.eqnSet σ Δ a ∧ ∀ m : (cxSt F).Met Y σ Δ,
        (cxSt F).pn Y σ Δ m ((cxSt F).cx Y σ f) (c'.finChart.symm v) = ‖g v‖ ^ 2 * m.h a (c'.finChart.symm v) := by
  intro F _ _ Y σ e c' p0 hp0 Δ a U hU hE f hf
  have hu : UnitAt (under p0) (f * (a : Y.Fn)) := ((hE _ hU).generatesAt_iff).1 hf
  obtain ⟨W, hW, s, hs⟩ := hu.regAt.exists_fnOf
  have hWo : IsOpen (ptsIn Y.str σ W) := isOpen_ptsIn W
  have hUo : IsOpen (ptsIn Y.str σ U) := isOpen_ptsIn U
  have hA : AnalyticOnNhd ℂ (ev Y.str σ W s ∘ c'.finChart.symm)
      (c'.finChart.target ∩ c'.finChart.symm ⁻¹' ptsIn Y.str σ W) :=
    (c'.analyticOnNhd_finChart_iff hWo _).2 (c'.holo W s)
  have hl : c'.finChart.symm (c'.finChart p0) = p0 := c'.finChart.left_inv hp0
  have hp0W : p0 ∈ ptsIn Y.str σ W := mem_ptsIn.2 hW
  have hp0U : p0 ∈ ptsIn Y.str σ U := mem_ptsIn.2 hU
  refine ⟨ev Y.str σ W s ∘ c'.finChart.symm, ?_, ?_⟩
  · show ev Y.str σ W s (c'.finChart.symm (c'.finChart p0)) ≠ 0
    rw [hl, ← ratVal_fnOf hp0W (gen_mem hW), hs]
    exact ratVal_ne_zero hu
  · have hN : IsOpen (c'.finChart.target ∩ c'.finChart.symm ⁻¹' (ptsIn Y.str σ W ∩ ptsIn Y.str σ U)) :=
      c'.finChart.isOpen_inter_preimage_symm (hWo.inter hUo)
    have hm : c'.finChart p0 ∈ c'.finChart.target ∩ c'.finChart.symm ⁻¹' (ptsIn Y.str σ W ∩ ptsIn Y.str σ U) :=
      ⟨c'.finChart.map_source hp0, by rw [Set.mem_preimage, hl]; exact ⟨hp0W, hp0U⟩⟩
    filter_upwards [hN.mem_nhds hm] with v hv
    have hvW : c'.finChart.symm v ∈ ptsIn Y.str σ W := hv.2.1
    have hvE : c'.finChart.symm v ∈ Var.eqnSet σ Δ a := hE _ (mem_ptsIn.1 hv.2.2)
    refine ⟨hA v ⟨hv.1, hvW⟩, hvE, fun m => ?_⟩
    show Var.pn Y σ Δ m (Var.cx Y σ f) (c'.finChart.symm v) = _
    rw [Var.pn_eq (m := (m : Var.Met Y σ Δ)) hvE, Var.fval_cx, ← hs, ratVal_fnOf hvW (gen_mem hW)]
    rfl

end GlobalTheory.HodgeLocCoord
