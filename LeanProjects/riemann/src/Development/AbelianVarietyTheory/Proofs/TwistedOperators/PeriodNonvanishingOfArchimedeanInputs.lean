import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesCoefficientsCuspidalIffOneSided
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCuspFormPeriodNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralEqZeroOfOrthogonalRealTranslatesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodEqZeroOfVanishingOnKFiniteValuesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridDepthPaysEveryLossStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsArchimedeanSignatureFrames
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealVectorsAllPlacesOfLocalDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultTApplyRapidDec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SurjectiveTopMap
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaLiftLastStepsCouplingCosetOrbitInvari
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteVolumeAdelicUnitaryQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryEmbeddingContinuousMulRational
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsRealFnNeZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PeriodNePf

section General

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

open Classical in

theorem real_translate (hθ : IsInfFam θ) {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ} :
    ∀ a ∈ GinfC V, ∀ v : SmT M, ∃ v' : SmT M, ∀ T ∈ MultT θ M J χ, ∀ h, T v' h = T v (h * a) := by
  refine GlobalTheory.Core.Rk.TopOnto.real_induction hθ _ (fun v => ⟨v, fun T _ h => by rw [mul_one]⟩) (fun a b ha hb v => ?_)
    fun τ g hg v => ?_
  · obtain ⟨v₁, f1⟩ := hb v
    obtain ⟨v₂, f2⟩ := ha v₁
    exact ⟨v₂, fun T hT h => by rw [f2 T hT, f1 T hT, mul_assoc]⟩
  · induction v using PiTensorProduct.induction_on with
    | smul_tprod r v =>
      let w : M.sm τ := ⟨M.rep τ g (v τ), GlobalTheory.Core.Rk.TopOnto.rep_mem_sm M τ hg _ (v τ).2⟩
      refine ⟨r • PiTensorProduct.tprod ℂ (Function.update v τ w), fun T hT h => ?_⟩
      rw [map_smul, map_smul, Pi.smul_apply, Pi.smul_apply,
        GlobalTheory.Core.Rk.TopOnto.multT_rel v (Function.update v τ w) (h * atTau θ V τ g) h 1 (fun m hm => by
          rw [one_mul]; exact congrFun (hm.equiv τ g hg v w rfl) h) hT, one_mul]
    | add a b ha hb =>
      obtain ⟨a', f1⟩ := ha
      obtain ⟨b', f2⟩ := hb
      exact ⟨a' + b', fun T hT h => by rw [T.map_add, T.map_add, Pi.add_apply, Pi.add_apply, f1 T hT, f2 T hT]⟩

end General

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

variable {D : D7}

theorem exists_kf {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G) (hM : M.IsRow)
    (hCR : GlobalTheory.Published.CuspRapidDecay) (hHC : GlobalTheory.Published.HarishChandraModules)
    (M₀ : DSModel (Yc D 0) (parB (Ptw D) 0)) (MP : DSModel (G.V (.core 0)) (Node.par D sc.cGap (.core 0)))
    {t : SmT M₀ →ₗ[ℂ] (GA D (Yc D 0) → ℂ)} (ht : t ∈ Rows L W.θ M₀)
    {y : SmT MP →ₗ[ℂ] (GA D (G.V (.core 0)) → ℂ)} (hy : y ∈ CoreForms G W.θ 0 MP) (v : SmT MP) (w' : SmT M₀)
    (h0 : per0 G M (y v) (t w') ≠ 0) (w : SmT M₀) (hw : w ≠ 0) :
    ∃ a ∈ KF MP, per0 G M (y a) (t w) ≠ 0 := by
  have hθ := W.θ_is
  obtain ⟨hμ, hfd⟩ := (hM.row 0 (Nat.zero_le _)).haar_fund
  let vY : GlobalTheory.Unf.Vol (Yc D 0) := ⟨M.ν (.grid 0 0), M.fd (.grid 0 0), hμ, hfd⟩
  have hyv : ∀ a, RapidDec (G.V (.core 0)) (y a) := fun a =>
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ MP W.θ hθ _ _ y hy a).2.2
  have htw : RapidDec (Yc D 0) (t w) :=
    (GlobalTheory.ChainOnto.MultRapid.multT_apply_rapidDec hCR D _ _ M₀ W.θ hθ _ _ t ht w).2.2
  have hF : GlobalTheory.Unf.IsContAut (Yc D 0) (fun g => y v (stabilizerEmbedding G.sp.dec0 g)) :=
    ⟨fun γ hγ g => by
      simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      exact (hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ) _,
      (hyv v).2.1.comp (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _)⟩
  have hB : ∃ C, ∀ g, ‖y v (stabilizerEmbedding G.sp.dec0 g)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hyv v).2.2 0
    exact ⟨C, fun g => by simpa using hC (stabilizerEmbedding G.sp.dec0 g)⟩
  obtain ⟨h, hh, hne⟩ : ∃ h ∈ GinfC (Yc D 0),
      ∫ g in vY.𝓕, y v (stabilizerEmbedding G.sp.dec0 g) * t w (g * h) ∂vY.μ ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact h0 (GlobalTheory.T.integral_eq_zero_of_orthogonal_real_translates hCR GlobalTheory.Mem.VolFin.finVol D W.θ hθ (Yc D 0) _ M₀ _ _ t ht vY _ hF hB w hw hn w')
  have e1 := GlobalTheory.QPl.LastOrb.setIntegral_mul_right vY
    (fun g => y v (stabilizerEmbedding G.sp.dec0 (g * h⁻¹)) * t w g) (fun γ hγ g => by
      simp only [mul_assoc, GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul]
      rw [(hyv v).1 _ (GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_rational _ γ hγ), htw.1 γ hγ g]) h
  simp only [mul_inv_cancel_right] at e1
  have hinf : stabilizerEmbedding G.sp.dec0 h⁻¹ ∈ GinfC (G.V (.core 0)) := GlobalTheory.RealType.Emb_mem_inf G.sp.dec0 (inv_mem hh)
  obtain ⟨v', hv'⟩ := real_translate hθ (M := MP) (J := (lev G (.core 0) : Set _)) (χ := 1) _ hinf v
  have hp : per0 G M (y v') (t w) ≠ 0 := by
    unfold per0
    simp only [hv' y hy]
    rw [e1] at hne
    simp only [GlobalTheory.UnitaryEmbeddingProperties.unitaryEmbedding_mul] at hne
    exact hne
  by_contra hn
  push_neg at hn
  have key := GlobalTheory.T.period_eq_zero_of_vanishing_on_kFinite_values hCR hHC D W.θ hθ (G.V (.core 0)) _ MP _ _ y hy (GA D (Yc D 0)) (vY.μ.restrict vY.𝓕)
    (stabilizerEmbedding G.sp.dec0) (t w) (GlobalTheory.UnitaryEmbeddingProperties.continuous_unitaryEmbedding _).measurable
    (htw.integrableOn_fundamentalDomain hμ hfd) (fun a ha => hn a ha) v'
  exact hp key

end GlobalTheory.PeriodNePf

namespace GlobalTheory.PeriodNePf

end GlobalTheory.PeriodNePf

end
