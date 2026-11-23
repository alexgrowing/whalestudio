import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ThetaIdentityOfMapsAll
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.KerJoinS
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOnto
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PiCongrLeftUpdate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGaps
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureFirst
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneMemKg
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ConsequencesOfDsClass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsScaleNormalisedLocalReading
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CuspidalSubspaceClosedRightTranslationStable
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTIota
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralTranslateOfSets
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ConjRowMultCusp

theorem mem_NI_iff_iota : ∀ (D : D7) {r : ℕ} (C : Matrix (Fin (D.sp.Y 0).rank) (Fin r) D.host.E), IsIsoFrame (D.sp.Y 0) C → ∀ g : GA D (D.sp.Y 0), g ∈ NI (D.sp.Y 0) C ↔ Formalism.IndefR.RationalEmbedding.iota D g ∈ (Formalism.IndefR.RationalEmbedding.inst D).NA (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range (C : Matrix (Fin (Formalism.IndefR.RationalEmbedding.inst D).n) (Fin r) (Formalism.IndefR.RationalEmbedding.inst D).E).col)) := by
  intro D r C hC g
  let I := Formalism.IndefR.RationalEmbedding.inst D
  let T := (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv
  obtain ⟨L, R, hL, hR⟩ :=
    GlobalTheory.CuspCompare.exists_inverses (starRingEnd D.host.E) (J := (D.sp.Y 0).gram) I.J_det hC.2.1
  have key : ∀ h : GA D (D.sp.Y 0),
      T h ∈ I.NA (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) ↔
      GlobalTheory.CuspCompare.UnipEq (incA D) C R (Formalism.UG.cT (starRingEnd D.host.E) C * (D.sp.Y 0).gram) L
        ((matHom (D.sp.Y 0) h).1 - 1) := fun h => by
    have hs : (Formalism.IndefR.RationalEmbedding.iota D).symm (T h) = h := (Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply h
    refine GlobalTheory.CuspCompare.mem_NA_iff I (fun v => Formalism.IndefR.Eqv.thetaC D ((Formalism.L2.Host.tauPl D).symm v))
      (fun v => Formalism.IndefR.Eqv.isInfFam_thetaC D ((Formalism.L2.Host.tauPl D).symm v)) h (T h) ?_ (fun v => ?_) hL hR
    · have hb := (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D (T h)).2
      have h2 := hb.trans (congrArg (Formalism.L2.SG.AdBridge.ofHAFin I) hs)
      unfold Formalism.L2.SG.AdBridge.ofHAFin at h2
      rw [Formalism.L2.SG.EvalTIota.tauF_eq_i] at h2
      exact h2
    · obtain ⟨ρ, rfl⟩ := (Formalism.L2.Host.tauPl D).surjective v
      have hb := Formalism.L2.SG.EvalTIota.infMat_brg_i (T h) ρ
      rw [hs] at hb
      simp only [Equiv.symm_apply_apply]
      exact hb.symm
  have hW : I.IsIsot (Submodule.span I.E (Set.range (C : Matrix (Fin I.n) (Fin r) I.E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff I _).2 ⟨r, C, hC, rfl⟩
  refine GlobalTheory.CuspCompare.mem_closure_iff_of_equiv T (GlobalTheory.T.strong_approximation_unitaryUnipotentRadical I _ hW).1 (fun g => ?_) g
  rw [key]
  exact and_congr Iff.rfl (and_congr Iff.rfl (GlobalTheory.CuspCompare.perp_cond (incA D) hL hR _).2)

theorem isCuspFun_of_isCuspFn_iota : ∀ (D : D7) (I : Formalism.MainNotions.S.AutInst) (hI : I = Formalism.L2.SG.InstExistsPf.instOf D)
    (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf] (f : I.GA → ℂ), Continuous f →
    (∀ γ ∈ I.GFset, ∀ y, f (γ * y) = f y) → I.IsCuspFn (I.muA μf) f →
    IsCuspFun (D.sp.Y 0) (fun y => f (((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA hI.symm)) y)) := by
  intro D I hI μf _ _ f hf hi hcusp
  subst hI
  have : BorelSpace (GA D (D.sp.Y 0)) := ⟨rfl⟩
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hW : (Formalism.IndefR.RationalEmbedding.inst D).IsIsot (Submodule.span (Formalism.IndefR.RationalEmbedding.inst D).E (Set.range (C : Matrix (Fin (Formalism.IndefR.RationalEmbedding.inst D).n) (Fin r) (Formalism.IndefR.RationalEmbedding.inst D).E).col)) :=
    (GlobalTheory.CuspCompare.isIsot_iff _ _).2 ⟨r, C, hC, rfl⟩
  have key := (GlobalTheory.CuspCompare.constTerm_iff_inst (Formalism.IndefR.RationalEmbedding.inst D) μf
    (Formalism.IndefR.RationalEmbedding.iota D).toMulEquiv ⟨(Formalism.IndefR.RationalEmbedding.iota D).continuous,
      (Formalism.IndefR.RationalEmbedding.iota D).symm.continuous⟩ (GQ (D.sp.Y 0)) (NI (D.sp.Y 0) C)
    (fun g => Formalism.IndefR.RationalEmbedding.iota_rat D g) _ hW (mem_NI_iff_iota D C hC) f hf hi).2
    (fun ν hν => hcusp _ hW ν hν)
  exact key μ 𝓕 hμ h𝓕 g

theorem isCuspFn_of_contRep {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {F : L2X X} {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X F ψ) (hF : X.B.I.IsCuspFn (X.B.I.muA X.B.μf) (X.B.I.ext F)) :
    X.B.I.IsCuspFn (X.B.I.muA X.B.μf) ψ := by
  obtain ⟨hc, hi, he⟩ := hψ
  have hfund := X.B.fund_spec
  obtain ⟨hT, hL, hS, -⟩ := GlobalTheory.CongTop.adelic_topology X.B.I
  obtain ⟨Γ, hΓ, hcΓ, -⟩ := GlobalTheory.T.rationalUnitaryPoints_discrete_fundamentalDomain X.B.I
  obtain ⟨hl, -, -, -, hop⟩ := GlobalTheory.T.adelicUnitaryHaar_bi_invariant X.B.I X.B.μf
  have : BorelSpace X.B.I.GA := inferInstance
  have : (X.B.I.muA X.B.μf).IsMulLeftInvariant := ⟨hl⟩
  have : SFinite (X.B.I.muA X.B.μf) := by unfold Formalism.MainNotions.S.AutInst.muA; infer_instance
  have hr : ∀ y, ∃ γ : Γ, X.B.I.rep X.B.fund y = (γ : X.B.I.GA) * y ∧ X.B.I.rep X.B.fund y ∈ X.B.fund := by
    intro y
    have h := hfund.2.1 y
    have e : X.B.I.rep X.B.fund y = h.choose * y := by
      unfold Formalism.MainNotions.S.AutInst.rep; exact dif_pos h
    have hm : h.choose ∈ (Γ : Set X.B.I.GA) := by
      have k := h.choose_spec.1
      generalize h.choose = z at k ⊢
      rw [hΓ]; exact k
    exact ⟨⟨h.choose, hm⟩, e, e ▸ h.choose_spec.2⟩
  have hext : X.B.I.ext F =ᵐ[X.B.I.muA X.B.μf] ψ := by
    filter_upwards [GlobalTheory.RightRegFund.ae_rep hfund.1 hr he] with y hy
    obtain ⟨γ, h1, -⟩ := hr y
    unfold Formalism.MainNotions.S.AutInst.ext
    rw [hy, h1, hi _ (hΓ ▸ γ.2)]
  intro W hW ν hν
  have := hν.1
  filter_upwards [hF W hW ν hν, GlobalTheory.CuspSubspace.constTerm_congr ν hext] with x a b
  rw [← b, a]

theorem conjMap_isCuspFun : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ u : M.Vec, IsCuspFun (D.sp.Y 0) (GlobalTheory.ConjRowMult.conjMap X M c Φ h t u) := by
  intro hDSC D X h θ S M J χ t c hS hθ hgap hE hM hrep Φ hΦ hcont u
  obtain ⟨ψ, hψ⟩ := hcont u
  obtain ⟨hd, hl, hH, hb, -⟩ := GlobalTheory.Core.Mi.seeData_of_gap D X hgap
  have hSL : GlobalTheory.DSId.StrictLow := GlobalTheory.ClassificationConsequences.strictLow_of_dsClass
    (GlobalTheory.Published.discreteSeriesClassification_iff.1 hDSC)
  have hL2 := ((GlobalTheory.Dec.CuspAll.cusp_all hSL X.B X.dv _ hd (GlobalTheory.PinScale.one_le_g X) hb hl hH Φ hΦ).2
    (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))).1
  have hψc := isCuspFn_of_contRep X hψ hL2
  have hY := isCuspFun_of_isCuspFn_iota D X.B.I h X.B.μf ψ hψ.1 hψ.2.1 hψc
  have e : GlobalTheory.ConjRowMult.conjMap X M c Φ h t u = fun y => star (ψ (iotaX X h (y * t⁻¹))) := by
    funext y
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  rw [e]
  intro r C hC μ 𝓕 hμ h𝓕 g
  have hz : ∫ n in 𝓕, ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * (g * t⁻¹))) ∂μ = 0 := hY r C hC μ 𝓕 hμ h𝓕 (g * t⁻¹)
  show ∫ n in 𝓕, star (ψ (iotaX X h ((n : GA D (D.sp.Y 0)) * g * t⁻¹))) ∂μ = 0
  simp only [mul_assoc]
  have := congrArg (starRingEnd ℂ) hz
  rw [← integral_conj, map_zero] at this
  exact this

end GlobalTheory.ConjRowMultCusp

end
