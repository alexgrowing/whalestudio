import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLast
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBiThetaIffJoin
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSourceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumPreservesThetaFundamentalDomainPairing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqZeroOfOrthogonalAllThetaFunctions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsJointlySmoothBiThetaWeilRepSecondVariableStatement
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EqZeroOfLintegralEqZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSawComm

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem integrableOn_mul_star {X : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {μ : Measure X} {𝓕 : Set X} (h𝓕 : μ 𝓕 ≠ ⊤) {f g : X → ℂ} (hf : Continuous f) (hg : Continuous g)
    {M N : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hN : ∀ x, ‖g x‖ ≤ N) : IntegrableOn (fun x => f x * star (g x)) 𝓕 μ := by
  refine Measure.integrableOn_of_bounded (M := M * N) h𝓕
    ((hf.mul hg.star).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_star]
  exact mul_le_mul (hM x) (hN x) (norm_nonneg _) ((norm_nonneg _).trans (hM x))

theorem isBiTheta_left {A S A' : HSp D} {χA χS : (AE D)ˣ →* Circle} {oma : Om A S}
    (hA : IsWeilDatumO ψ A S χA χS oma) {C : WO A S → WO S A' → ℂ} (hC : IsBiTheta ψ A S A' C) (p : GA D A × GA D S) :
    IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := by
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  have hF := GlobalTheory.BiTransfer.isThetaFunO_join d hC
  have h := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A (GlobalTheory.ChiGrid.negSp A') S d χA χS oma hA _ hF Unit (0 : Measure Unit)
    (fun _ => 0) (fun _ => 0) measurable_const (integrable_zero _ _ _) p).1
  simp only [GlobalTheory.BiTransfer.join_symm] at h
  exact GlobalTheory.BiTransfer.isBiTheta_of_join (C := fun u v => oma p (fun u' => C u' v) u) d h

theorem slice_right {A S A' : HSp D} {K : WO A S → WO S A' → ℂ} (hK : IsBiTheta ψ A S A' K) (u : WO A S) :
    IsThetaFunO ψ S A' (K u) := by
  refine ⟨fun γ w => hK.quasiR γ u w, ?_, hK.cont.comp (continuous_const.prodMk continuous_id), fun k L hL hLf w => ?_⟩
  · obtain ⟨U, hU, h⟩ := hK.levR
    exact ⟨U, hU, fun a ha ha' => h a ha ha' u⟩
  · have := hK.smooth k 0 L continuous_zero hL (fun _ => by simp) hLf u w
    simpa using this

theorem comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle)
    (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb →
    ∀ C, IsBiTheta ψ A S A' C → ∀ p q u v,
      omb q (fun v' => oma p (fun u' => C u' v') u) v = oma p (fun u' => omb q (C u') v) u := by
  intro D ψ A S A' χA χS χS' χA' oma omb hA hB C hC p q u v
  have hψ : IsStdChar D ψ (-1) := hA.std
  let d := GlobalTheory.BiTransfer.sumDec A (GlobalTheory.ChiGrid.negSp A')
  obtain ⟨μ, 𝓕, hcov⟩ := GlobalTheory.MixModel.exists_isCovolOne D A'.rank S.rank
  have h𝓕 : μ 𝓕 ≠ ⊤ := by rw [hcov.2.2]; exact ENNReal.one_ne_top
  let v0 : VolM D A'.rank S.rank := ⟨μ, 𝓕, hcov⟩
  have : BorelSpace (WO S A') := ⟨rfl⟩
  have : BorelSpace (WO A' S) := ⟨rfl⟩

  have hC1 : IsBiTheta ψ A S A' fun u v => oma p (fun u' => C u' v) u := isBiTheta_left hA hC p
  have hC2 : IsBiTheta ψ A S A' fun u v => omb q (C u) v := GlobalTheory.T.isBiTheta_weilRep_second_variable D ψ A S A' χS' χA' omb hB C hC q
  have hC3 : IsBiTheta ψ A S A' fun u v => oma p (fun u' => omb q (C u') v) u := isBiTheta_left hA hC2 p
  have hL := hB.om_pres q _ (slice_right hC1 u)
  have hR := slice_right hC3 u

  have hint : ∀ f g : WO S A' → ℂ, IsThetaFunO ψ S A' f → IsThetaFunO ψ S A' g →
      IntegrableOn (fun w => f w * star (g w)) 𝓕 μ := by
    intro f g hf hg
    obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
    obtain ⟨N, hN⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hg
    exact integrableOn_mul_star h𝓕 hf.cont hg.cont hM hN
  have hintS : ∀ f : WO S A' → ℂ, IsThetaFunO ψ S A' f → Integrable (fun w => star (f w)) (μ.restrict 𝓕) := by
    intro f hf
    obtain ⟨M, hM⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hf
    refine Measure.integrableOn_of_bounded (M := M) h𝓕 hf.cont.star.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_star]; exact hM x
  have hk : Measurable (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A') := (GlobalTheory.BiTransfer.continuous_dagger S A').measurable

  set Q : WO S A' → ℂ := fun w => omb q (fun v' => oma p (fun u' => C u' v') u) w -
    oma p (fun u' => omb q (C u') w) u with hQ
  suffices hQ0 : Q = 0 by
    have := congrFun hQ0 v
    simp only [hQ, Pi.zero_apply] at this
    exact sub_eq_zero.1 this
  refine GlobalTheory.ThetaOrthTotal.eq_zero_of_orthogonal_theta D ψ hψ S A' μ 𝓕 hcov.1 hcov.2.1 Q (hL.cont.sub hR.cont) (fun γ w => ?_) (fun f hf => ?_)
  · simp only [hQ]
    rw [mul_sub, ← hL.quasi γ w, ← hR.quasi γ w]
  ·
    set g := omb q⁻¹ f with hg
    have hgt : IsThetaFunO ψ S A' g := hB.om_pres _ _ hf
    have hfg : omb q g = f := by
      rw [hg, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

    have e1 : ∫ w in 𝓕, omb q (fun v' => oma p (fun u' => C u' v') u) w * star (f w) ∂μ =
        ∫ w in 𝓕, oma p (fun u' => C u' w) u * star (g w) ∂μ := by
      have := GlobalTheory.WeilPairing.thPair_om_eq D ψ S A' χS' χA' omb hB v0 q _ g (slice_right hC1 u) hgt
      rw [hfg] at this
      exact this

    have e2 : ∫ w in 𝓕, oma p (fun u' => omb q (C u') w) u * star (f w) ∂μ =
        ∫ w in 𝓕, oma p (fun u' => C u' w) u * star (g w) ∂μ := by
      have c2 := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A (GlobalTheory.ChiGrid.negSp A') S d χA χS oma hA _ (GlobalTheory.BiTransfer.isThetaFunO_join d hC2)
        (WO S A') (μ.restrict 𝓕) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A') (fun w => star (f w)) hk (hintS f hf) p).2 u
      have c1 := (GlobalTheory.T.weil_operator_commutes_superposition_slices_source D ψ _ A (GlobalTheory.ChiGrid.negSp A') S d χA χS oma hA _ (GlobalTheory.BiTransfer.isThetaFunO_join d hC)
        (WO S A') (μ.restrict 𝓕) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S A') (fun w => star (g w)) hk (hintS g hgt) p).2 u
      simp only [GlobalTheory.BiTransfer.join_symm, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger_dagger] at c1 c2
      have inner : (fun u' => ∫ w, star (f w) * omb q (C u') w ∂(μ.restrict 𝓕)) =
          fun u' => ∫ w, star (g w) * C u' w ∂(μ.restrict 𝓕) := by
        funext u'
        have := GlobalTheory.WeilPairing.thPair_om_eq D ψ S A' χS' χA' omb hB v0 q _ g (slice_right hC u') hgt
        rw [hfg] at this
        simp only [thPair, v0] at this
        simp only [mul_comm (star _)]
        exact this
      simp only [mul_comm _ (star _)]
      rw [← c2, inner, c1]
    simp only [hQ, sub_mul]
    rw [integral_sub (hint _ _ hL hf) (hint _ _ hR hf), e1, e2, sub_self]

end GlobalTheory.SeeSawComm

end
