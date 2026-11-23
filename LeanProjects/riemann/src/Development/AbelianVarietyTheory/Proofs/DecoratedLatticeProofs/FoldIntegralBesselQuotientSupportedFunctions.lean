import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompactStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroupStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupUnfoldFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBesselRationalCutoffFundamentalDomainStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Fold

theorem fold_quot : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (𝓢 : Set (besGrp B.d B.o)), IsFundamentalDomain ((GQ (D.sp.Y 0)).subgroupOf (besGrp B.d B.o)) 𝓢 B.lev.μR → ∀ Fs : Set X.B.I.GA, IsFundamentalDomain (Srat X u) Fs (X.B.I.muA X.B.μf) → ∃ c : ℝ, 0 < c ∧ ∀ F : X.B.I.GA → ENNReal, Measurable F → (∀ γ ∈ Srat X u, ∀ x, F (γ * x) = F x) → (∀ k ∈ X.K2, ∀ x, F (x * (1, k)) = F x) → (∀ x, F x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B 𝓢 h𝓢 Fs hFs
  obtain ⟨c₁, hc₁, hL1⟩ := GlobalTheory.T.haarMeasure_disintegration_besselGroup D X h u ψ A B
  obtain ⟨β, hβm, hβ1, hβF⟩ := GlobalTheory.T.exists_besselRational_cutoff_fundamentalDomain D X u Fs hFs
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hK0 : X.B.μf X.K2 ≠ 0 := hK.2.2.1.ne'
  have hKT : X.B.μf X.K2 ≠ ⊤ := hK.2.2.2.ne
  refine ⟨c₁ * (X.B.μf X.K2).toReal, mul_pos hc₁ (ENNReal.toReal_pos hK0 hKT), ?_⟩
  intro F hFm hFl hFr hFsupp
  have hR := Formalism.L2.SG.Pf.foldReady_holds X.B.I
  haveI : BorelSpace X.B.I.GA := hR.2.2.2.1
  haveI : SecondCountableTopology X.B.I.GA := hR.2.1
  haveI : LocallyCompactSpace X.B.I.GA := hR.1
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI : SecondCountableTopology (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.secondCountableTopology
  haveI : LocallyCompactSpace (GA D (D.sp.Y 0)) := (iotaX X h).toHomeomorph.isClosedEmbedding.locallyCompactSpace
  have hcl : IsClosed (besGrp B.d B.o : Set (GA D (D.sp.Y 0))) := GlobalTheory.BesClosed.besGrp_isClosed _ _ _ _ _ _ B.d B.o
  haveI : LocallyCompactSpace (besGrp B.d B.o) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : B.lev.μR.IsHaarMeasure := (GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact D D.R.rS B.lev).1
  haveI : SigmaFinite B.lev.μR := inferInstance
  have hK2m : MeasurableSet X.K2 := (Formalism.L2.SG.Pf.DstarIdxPf.isOpen_levelSubgroup' X).measurableSet
  have hι : Continuous (fun s : besGrp B.d B.o => iotaX X h s.1) :=
    (iotaX X h).continuous.comp continuous_subtype_val

  have key : ∀ y : X.B.I.Ginf,
      ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) * F (iotaX X h s.1 * (y, X.xu u) * (1, k))
          ∂X.B.μf ∂B.lev.μR =
        X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR := by
    intro y
    set g : X.B.I.GA := (y, X.xu u) with hg
    have e1 : ∀ s : besGrp B.d B.o,
        ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g * (1, k)) ∂X.B.μf =
          ∫⁻ k in X.K2, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂X.B.μf := by
      intro s
      refine setLIntegral_congr_fun hK2m (fun k hk => ?_)
      rw [hFr k hk]
    simp_rw [e1]
    have hmeas : Measurable (Function.uncurry fun (s : besGrp B.d B.o) (k : X.B.I.Gf) =>
        β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g)) := by
      have c1 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g * (1, p.2)) :=
        ((hι.comp continuous_fst).mul continuous_const).mul (continuous_const.prodMk continuous_snd)
      have c2 : Continuous (fun p : besGrp B.d B.o × X.B.I.Gf => iotaX X h p.1.1 * g) :=
        (hι.comp continuous_fst).mul continuous_const
      exact (hβm.comp c1.measurable).mul (hFm.comp c2.measurable)
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    have e2 : ∀ k ∈ X.K2, ∫⁻ s, β (iotaX X h s.1 * g * (1, k)) * F (iotaX X h s.1 * g) ∂B.lev.μR =
        ∫⁻ s in 𝓢, F (iotaX X h s.1 * g) ∂B.lev.μR := by
      intro k hk
      have hf : Measurable (fun x : X.B.I.GA => β (x * g * (1, k)) * F (x * g)) :=
        (hβm.comp ((continuous_id.mul continuous_const).mul continuous_const).measurable).mul
          (hFm.comp (continuous_id.mul continuous_const).measurable)
      rw [GlobalTheory.T.lintegral_besselGroup_unfold_fundamental_domain D X h u ψ A B 𝓢 h𝓢 _ hf]
      refine lintegral_congr fun s => ?_
      have e3 : ∀ σ : Srat X u, β ((σ : X.B.I.GA) * iotaX X h s.1 * g * (1, k)) * F ((σ : X.B.I.GA) * iotaX X h s.1 * g) =
          β ((σ : X.B.I.GA) * (iotaX X h s.1 * g * (1, k))) * F (iotaX X h s.1 * g) := by
        intro σ
        rw [mul_assoc (σ : X.B.I.GA) (iotaX X h s.1) g, hFl _ σ.2, mul_assoc (σ : X.B.I.GA) (iotaX X h s.1 * g)]
      simp only [e3]
      rw [ENNReal.tsum_mul_right, hβ1, one_mul]
    rw [setLIntegral_congr_fun hK2m (fun k hk => e2 k hk), setLIntegral_const, mul_comm]
  calc ∫⁻ x in Fs, F x ∂(X.B.I.muA X.B.μf) = ∫⁻ x, β x * F x ∂(X.B.I.muA X.B.μf) := hβF F hFm hFl
    _ = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, β (iotaX X h s.1 * (y, X.xu u) * (1, k)) *
          F (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
        refine hL1 (fun x => β x * F x) (hβm.mul hFm) (fun x hx => hFsupp x ?_)
        intro h0; exact hx (by rw [h0, mul_zero])
    _ = ENNReal.ofReal c₁ * ∫⁻ y, X.B.μf X.K2 * ∫⁻ s in 𝓢, F (iotaX X h s.1 * (y, X.xu u)) ∂B.lev.μR ∂(X.nuQ u) := by
        congr 1; exact lintegral_congr key
    _ = _ := by
        rw [lintegral_const_mul' _ _ hKT, ← mul_assoc, ENNReal.ofReal_mul hc₁.le, ENNReal.ofReal_toReal hKT]

end GlobalTheory.Core.Mi.Fold
