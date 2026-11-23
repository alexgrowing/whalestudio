import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitDecayStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousThetaLiftTransfer
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.TopoAF

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.ThKCont

theorem continuous_I_so : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁),
    Continuous (G.M'.I om' Φ) := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM Φ hΦ
  have hT := hM.triple
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hS : Φ ∈ schA F (Fin a' × Fin (a + a')) := GlobalTheory.ThK.SqIntCont.polData_le_schA hT.geo.hM' hΦ.1
  have hcont := (((GlobalTheory.T.theta_basic_properties hKP.base) F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ hP).1 Φ hS).1
  obtain ⟨C, k, hC⟩ := (GlobalTheory.T.schwartz_orbit_decay hKP) F E σ B a' (a + a') G.V' G.W G.M' _ _ om' _ _ _ _ hP Φ hΦ.2 0
  have hfin : G.M'.μ G.M'.dom < ⊤ :=
    GlobalTheory.UnitaryVol.measure_dom_lt_top F E σ B a a' G X om om' hKP.siegelSetUnitary hT
  haveI : BorelSpace (UA σ G.V'.J) := ⟨rfl⟩
  haveI : Fact (G.M'.μ G.M'.dom < ⊤) := ⟨hfin⟩
  have hbd : ∀ g h, ‖theta om' Φ g h‖ ≤ C * (ht h : ℝ) ^ k := fun g h => by simpa using hC g h
  have hC0 : 0 ≤ C := by
    have h1 : (1 : ℝ) ≤ ht (1 : UA σ G.W.J) := by exact_mod_cast GlobalTheory.AdelicU.one_le_heightGL (F := F) (1 : UA σ G.W.J).1
    have h2 := (norm_nonneg _).trans (hbd 1 1)
    exact nonneg_of_mul_nonneg_left h2 (pow_pos (lt_of_lt_of_le one_pos h1) k)
  have hht : Continuous fun h : UA σ G.W.J => (ht h : ℝ) :=
    NNReal.continuous_coe.comp ((GlobalTheory.Grow.continuous_heightGL F).comp continuous_subtype_val)
  haveI : FirstCountableTopology (UA σ G.W.J) := by
    have : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) :=
      inferInstanceAs (SecondCountableTopology (Fin (a + a') → Fin (a + a') → AE F E))
    have : SecondCountableTopology (Matrix (Fin (a + a')) (Fin (a + a')) (AE F E))ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
    have : SecondCountableTopology (GL (Fin (a + a')) (AE F E)) :=
      Units.isEmbedding_embedProduct.secondCountableTopology
    have : SecondCountableTopology (UA σ G.W.J) := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    exact @TopologicalSpace.SecondCountableTopology.to_firstCountableTopology _ _ this
  rw [continuous_iff_continuousAt]
  intro h0
  have hev : ∀ᶠ h in 𝓝 h0, (ht h : ℝ) < ht h0 + 1 :=
    hht.continuousAt.eventually (gt_mem_nhds (lt_add_one _))
  unfold Model.I
  refine continuousAt_of_dominated (bound := fun _ => C * ((ht h0 : ℝ) + 1) ^ k) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun h =>
      (hcont.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
  · filter_upwards [hev] with h hh
    refine ae_of_all _ fun g => (hbd g h).trans ?_
    gcongr
  · exact integrable_const _
  · exact ae_of_all _ fun g => (hcont.comp (continuous_const.prodMk continuous_id)).continuousAt

end GlobalTheory.ThKCont
