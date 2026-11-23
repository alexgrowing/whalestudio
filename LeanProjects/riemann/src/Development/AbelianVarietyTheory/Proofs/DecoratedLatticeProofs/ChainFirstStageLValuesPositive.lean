import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageConjugateValuesHeckeOperatorsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageLatticeStabilizerParamsOffSetStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainHeckeParamsTrivialBoundRapidDecayStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainLevelPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EulerProductConjugationStableParametersPosStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoundedAutomorphicParametersStarStableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevelStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem isPar_flat_of_le {D : D7} {c : Com D} {w : Twist D} {j : ℕ} {s : PiLocalization₂ D} (hr : D.R.r ≤ s.V.rank)
    (hle : s.CC c ≤ (flat c w j s hr).CC c) (u : s.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB : IsPar u B) :
    IsPar (⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) B := by
  refine ⟨fun h => ?_, fun v hv => ?_⟩
  · have h2 : ((⟨u.1, hle u.2⟩ : (flat c w j s hr).CC c) : SmT (flat c w j s hr).M →ₗ[ℂ] (GA D (flat c w j s hr).V → ℂ)) = 0 :=
      (Submodule.coe_eq_zero).2 h
    exact hB.1 ((Submodule.coe_eq_zero).1 h2)
  · have h3 := hB.2 v hv
    unfold ParFun at h3 ⊢
    exact h3

theorem bounded_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r (((D.R.r : ℝ) - 1) / 2) := by
  have hrank : s'.V.rank = D.R.r := by
    rw [hflat.rank]; simp [Formalism.BasicNotions.Ranks.rankY]
  have hbd0 := GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay hCRD D (GlobalTheory.T.thetaChain_level_properties D) c hc 0 hj s' hflat u' B hB'
  rw [hrank] at hbd0
  exact hbd0

theorem conjStable_first_member (hCRD : GlobalTheory.Published.CuspRapidDecay) {D : D7} {c : Com D} (hc : c.Is) (hj : 0 ≤ D.R.m) {s' : PiLocalization₂ D}
    (hflat : s'.Is c 0) (u' : s'.CC c) (B : GlobalTheory.LFun.Fam D.host.E) (hB' : IsPar u' B) :
    ∀ w ∉ GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))),
      (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) → w ≠ w' → B w' = (B w).map star) ∧
      (¬ Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) (w.under (𝓞 D.host.F)) → (B w).map star = B w) := by
  have hex : ∃ v, PiLocalization₂.val u' v ≠ 0 := by
    by_contra h
    push_neg at h
    apply hB'.1
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    exact h v
  obtain ⟨v, hv⟩ := hex
  set f : GA D s'.V → ℂ := fun g => conj (PiLocalization₂.val u' v g) with hfdef
  have hPF : ParFun c s' (PiLocalization₂.val u' v) B := hB'.2 v hv
  have h3 : GlobalTheory.LFun.IsParamFunV s'.V c.S f B := ((GlobalTheory.T.thetaChainStage_lattice_stabilizer_params_off_set D c hc 0 hj s' hflat).2 f B).1 hPF
  obtain ⟨h4a, _, _⟩ := GlobalTheory.T.thetaChainStage_conjugate_values_hecke_operators hCRD D c hc 0 hj s' hflat
  obtain ⟨hcont, ⟨C, hC⟩, hinv, _⟩ := h4a u' v
  have hfmem : f ∈ GlobalTheory.FinZeta.bddAut s'.V := by
    refine ⟨(Complex.continuous_conj).comp hcont, fun γ hγ g => ?_, C, fun g => ?_⟩
    · simp only [hfdef, hinv γ hγ g]
    · simpa [hfdef] using hC g
  exact GlobalTheory.T.boundedAutomorphic_parameters_star_stable D s'.V c.S f hfmem B h3

end GlobalTheory.ChainTw

namespace GlobalTheory.ChainTw

theorem lPos_of_rapidDecay : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, LPos D := by
  intro hCRD D c w hw j hj s hs hj0 u B hB
  subst hj0
  have hc := hw.com
  obtain ⟨hr, hL, hflat⟩ := hs
  have hle := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw 0 hj s ⟨hr, hL, hflat⟩ hr
  have hB' := isPar_flat_of_le hr hle u B hB
  have hbd : GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (c.S : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r ((D.R.r : ℝ) / 2) :=
    GlobalTheory.LiftPole.Bounded.mono (bounded_first_member hCRD hc hj hflat _ B hB') (by linarith)
  refine ⟨hbd, fun k hk => ?_⟩
  have hst := conjStable_first_member hCRD hc hj hflat _ B hB'
  have hch := hc.chars.2.2.2.2 (k + 1) (Finset.mem_Icc.2 ⟨by omega, by omega⟩)
  have hrt : ((D.R.r : ℝ) / 2) + 1 < (1 + (D.R.t : ℝ)) / 2 := by
    have h5 : D.R.r + 5 ≤ D.R.t := by simpa [Formalism.BasicNotions.Ranks.r] using D.R.rank_add_five_le
    have h5' : (D.R.r : ℝ) + 5 ≤ D.R.t := by exact_mod_cast h5
    linarith
  obtain ⟨l, hl, he⟩ := GlobalTheory.T.euler_product_conjugation_stable_parameters_pos D c.S B (c.μ (k + 1)) D.R.r ((D.R.r : ℝ) / 2) ((1 + (D.R.t : ℝ)) / 2) hch.1 hch.2
    (hc.unr ⟨k, hk⟩) hbd hrt hst
  refine ⟨l, hl, ?_⟩
  rw [← he]
  congr 1
  push_cast
  ring

end GlobalTheory.ChainTw
