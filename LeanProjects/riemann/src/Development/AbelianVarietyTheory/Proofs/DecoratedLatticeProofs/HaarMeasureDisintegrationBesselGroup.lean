import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarFiniteAdeleDisintegrationStabilizerCompactStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealStabilizerProductMeasureIsHaarOnSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LintegralBesselGroupHaarEqConstMulProdStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi.Disint

theorem disint : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  intro D X h u ψ A B
  obtain ⟨μSf, hHaar, hσ, c₁, hc₁, hfin⟩ := GlobalTheory.T.haar_finite_adele_disintegration_stabilizer_compact D X u
  obtain ⟨c₃, hc₃, hR⟩ := GlobalTheory.T.lintegral_besselGroup_haar_eq_const_mul_prod D X h u ψ A B μSf hHaar hσ (GlobalTheory.T.real_stabilizer_product_measure_isHaarOnSet D X u)
  refine ⟨c₁ / c₃, div_pos hc₁ hc₃, ?_⟩
  intro G hGm hsupp
  haveI : SecondCountableTopology X.B.I.Gf := Formalism.L2.SG.Pf.gf_secondCountable X.B.I
  haveI := hσ
  set μS := ((X.muN u).prod (X.muH u)).map (fun p : X.B.I.Ginf × X.B.I.Ginf => p.1 * p.2) with hμS

  set g : X.B.I.Ginf → ENNReal := fun x => ∫⁻ t, ∫⁻ k in X.K2, G (x, t.1 * X.xu u * k) ∂X.B.μf ∂μSf with hgdef
  have hg : Measurable g := by
    have hΨ : Measurable (fun p : (X.B.I.Ginf × Formalism.L2.SG.Pf.SfinSub X.B.I X.eR (X.zR u)) × X.B.I.Gf =>
        G (p.1.1, p.1.2.1 * X.xu u * p.2)) :=
      hGm.comp (measurable_fst.fst.prodMk
        (((measurable_subtype_coe.comp measurable_fst.snd).mul_const _).mul measurable_snd))
    exact (hΨ.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)).lintegral_prod_right' (ν := μSf)
  have hL : ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := by
    have e0 : X.B.I.muA X.B.μf = (Formalism.L2.SG.ProjRows.muInf X.B.I).prod X.B.μf := rfl
    rw [e0, lintegral_prod _ hGm.aemeasurable]
    have e1 : ∀ x, ∫⁻ z, G (x, z) ∂X.B.μf = ENNReal.ofReal c₁ * g x := fun x =>
      hfin (fun z => G (x, z)) (hGm.comp measurable_prodMk_left) (fun z hz => hsupp (x, z) hz)
    simp_rw [e1]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, X.nuQ_weil u g hg]
  have hRy : ∀ y : X.B.I.Ginf, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR =
      ENNReal.ofReal c₃ * ∫⁻ a, g (a * y) ∂μS := by
    intro y
    set Φ : X.B.I.GA → ENNReal := fun p => ∫⁻ k in X.K2, G (p.1 * y, p.2 * X.xu u * k) ∂X.B.μf with hΦ
    have hΦm : Measurable Φ := by
      have : Measurable (fun q : X.B.I.GA × X.B.I.Gf => G (q.1.1 * y, q.1.2 * X.xu u * q.2)) :=
        hGm.comp ((measurable_fst.fst.mul_const y).prodMk ((measurable_fst.snd.mul_const _).mul measurable_snd))
      exact this.lintegral_prod_right' (ν := X.B.μf.restrict X.K2)
    have e : ∀ s : besGrp B.d B.o, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf = Φ (iotaX X h s.1) := by
      intro s
      refine lintegral_congr fun k => ?_
      congr 1
      ext <;> simp
    simp_rw [e]
    rw [hR Φ hΦm]
  calc ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c₁ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u) := hL
    _ = ENNReal.ofReal (c₁ / c₃) * (ENNReal.ofReal c₃ * ∫⁻ y, ∫⁻ a, g (a * y) ∂μS ∂(X.nuQ u)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (div_pos hc₁ hc₃).le, div_mul_cancel₀ _ hc₃.ne']
    _ = _ := by
        congr 1
        rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact (lintegral_congr fun y => hRy y).symm

end GlobalTheory.Core.Mi.Disint
