import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFramedChartExponentialToroidalModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGramHodgeFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockGramDeterminantBoundsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisorGeneratesLocalPeriodMatrixStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.AnForm.M GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.ShFam
open Filter Topology
open Matrix
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

open Filter Topology Matrix
open scoped ComplexOrder

open GlobalTheory.HodgeLocGeo in

theorem GlobalTheory.HodgeLocGeo.hodge_potential_local : Hypotheses2 → HypothesesH → OnObj fun D O _ T _ h => ∀ (c : O.Y.Comp) (a : Fin ((T.M c).n + 1)) (j : Fin ((T.M c).A a).n),
  ∀ y ∈ (((T.M c).A a).chart j).target, (((T.M c).A a).chart j).symm y ∉ (T.M c).Z a →
  ∀ f : DV.Rt D.what₂.Tau O.N → (O.var c).Fn,
    (∀ x, (GlobalTheory.ShFam.Pad.divOf (O.Φ.C c) (O.ex x)).GeneratesAt (under ((h.man c).pt a ((((T.M c).A a).chart j).symm y))) (f x)) →
  ∃ (p q : D.what₂.Tau → ℕ) (hpq : ∀ τ, p τ + q τ = O.N) (ι : Type) (_ : Fintype ι) (U : Set (ι → ℂ))
    (ψ : ∀ τ, (ι → ℂ) → Matrix (Fin (q τ) ⊕ Fin (p τ)) (Fin (q τ) ⊕ Fin (p τ)) ℂ) (a' b' : D.what₂.Tau → ℝ)
    (Y' : Set (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ)) (π : (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → ι → ℂ)
    (AW : ∀ τ, (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (p τ)) (Fin (p τ)) ℂ)
    (Aω : ∀ τ, (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → Matrix (Fin (q τ)) (Fin (q τ)) ℂ)
    (g : DV.Rt D.what₂.Tau O.N → (Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y) → ℂ) → ℂ),
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsHodgeFrame U (ψ τ)) ∧ (∀ τ, 0 < a' τ) ∧ (∀ τ, 0 < b' τ) ∧
    (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y' U π (AW τ)) ∧ (∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.IsFlagFamily Y' U π (Aω τ)) ∧
    y ∈ Y' ∧ (∀ x, AnalyticAt ℂ (g x) y) ∧ (∀ x, g x y ≠ 0) ∧
    ∀ u : D.what₂.Tau → Fin O.N → ℝ,
      (fun v => ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 *
        GlobalTheory.Mean4O.lnN (O.met.hm c none ((h.man c).ε a) (O.ex x)) (f x) ((h.man c).pt a ((((T.M c).A a).chart j).symm v))) =ᶠ[𝓝 y]
      fun v => -Real.log (GlobalTheory.IndefiniteRowSideFullHecke.HodgeFrameGram.pairWeightNormSq (fun τ x => (a' τ : ℂ) • GlobalTheory.HermFrame.quotGram (ψ τ x))
          (fun τ x => (b' τ : ℂ) • -GlobalTheory.HermFrame.subGram (ψ τ x)) π AW Aω (fun τ k => u τ (Fin.cast (hpq τ) k)) v) / 2 +
        ∑ x : DV.Rt D.what₂.Tau O.N, u x.1 x.2 * Real.log ‖g x v‖ := by
  intro p2 ph D O hc hR A T H h c a j y hy hZ f hf
  obtain ⟨Zm, GW, GΩ, cW, cΩ, g, hcW, hcΩ, hg0, hev⟩ := GlobalTheory.T.divisor_generates_local_period_matrix p2 ph D O hc hR A T H h c a j y hy hZ f hf
  obtain ⟨U, hUsub, hUo, hyU⟩ := eventually_nhds_iff.1 hev
  have hpq : O.j + (O.N - O.j) = O.N := by have := O.indef; omega
  refine ⟨fun _ => O.j, fun _ => O.N - O.j, fun _ => hpq, Fin (Formalism.MainNotions.WeightThresholdDefs.dimY O.Y), inferInstance, U,
    fun τ v => modelHodgeGram (Zm τ v), cW, fun τ => (cΩ τ)⁻¹, U, id, fun τ v => (GW τ v)ᵀ,
    fun τ v => ((GΩ τ v).submatrix Fin.rev id)⁻¹, g, fun τ => ?_, hcW, fun τ => inv_pos.2 (hcΩ τ), fun τ => ?_,
    fun τ => ?_, hyU, fun x => (hUsub y hyU).2.2.2.1 x, hg0, fun u => ?_⟩
  · exact GlobalTheory.T.model_hodge_gram_hodge_frame U (Zm τ) hUo (fun a b v hv => ((hUsub v hv).1 τ a b).differentiableAt.differentiableWithinAt)
      fun v hv => (hUsub v hv).2.2.2.2.1 τ
  · refine ⟨hUo, contDiffOn_id, fun v hv => hv, fun a b v hv => ?_, fun v hv => ?_⟩
    · exact ((hUsub v hv).2.1 τ b a).contDiffAt.contDiffWithinAt
    · rw [Matrix.det_transpose]; exact (hUsub v hv).2.2.2.2.2.1 τ
  · have hR : ∀ v ∈ U, IsUnit ((GΩ τ v).submatrix Fin.rev id).det := fun v hv => by
      rw [← Matrix.isUnit_iff_isUnit_det,
        show ((GΩ τ v).submatrix Fin.rev id) = (GΩ τ v).submatrix Fin.revPerm (Equiv.refl _) from rfl,
        Matrix.isUnit_submatrix_equiv, Matrix.isUnit_iff_isUnit_det]
      exact (hUsub v hv).2.2.2.2.2.2.1 τ
    refine ⟨hUo, contDiffOn_id, fun v hv => hv, fun a b v hv => ?_, fun v hv => ?_⟩
    · exact (GlobalTheory.ShFam.Hor.LogCh.analyticAt_inv_apply (fun a' b' => (hUsub v hv).2.2.1 τ (Fin.rev a') b')
        (hR v hv).ne_zero a b).contDiffAt.contDiffWithinAt
    · exact Matrix.isUnit_nonsing_inv_det _ (hR v hv)
  · filter_upwards [hUo.mem_nhds hyU] with v hv
    obtain ⟨-, -, -, -, hpos, hu1, hu2, hln⟩ := hUsub v hv
    simp only [hln, mul_add, Finset.sum_add_distrib]
    rw [GlobalTheory.T.weighted_sum_log_rootNorm_eq_neg_log_pairWeightNormSq hpq Zm GW GΩ cW cΩ v hcW hcΩ hpos hu1 hu2 u, add_comm]
