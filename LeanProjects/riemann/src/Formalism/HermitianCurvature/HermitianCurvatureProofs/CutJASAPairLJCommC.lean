import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASAPairLQOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableGerm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJALocToolsTheta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAFFStableAdjComm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SA

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.JA

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem thrW_sa (k r o : ℕ) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r (6 * (r : ℝ) * (o : ℝ) + (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) + 1) o := by
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have h1 : 0 ≤ (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ)) * (6 * (r : ℝ) + 1) := by positivity
  have h2 : 0 ≤ (r : ℝ) * (6 * (r : ℝ) + 1) := by positivity
  refine ⟨by linarith, ?_⟩
  nlinarith

theorem sAJCommC_of_thetaJ (hT : LT.ThetaJ) : SAJCommC := by
  refine ⟨0, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ hΘ F hFs hFc _hFO U X hU hX hagree y hy hyU
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl

  have hAg := QO.agree_qOf (T v).base X F U hX
    (fun q hq hqU => hagree q ⟨hq.1, by rw [hTT]; exact hq.2⟩ hqU)
  set V : Set (B.Mat S.G.k S.G.r) := Q.OmPlus S.G.k S.G.r (T v).base.z (T v).base.z' ∩
    QO.qOf (T v).base.z (T v).base.z' ⁻¹' U with hVdef
  have hVo : IsOpen V := QO.isOpen_qOf _ _ hU
  have hJV : ∀ g ∈ V, g ∈ B.GV S.G.k S.G.r → X g = B.JF (T v).base F g := fun g hg hgG =>
    hAg g ⟨hgG, hg.1⟩ hg.2
  have hq : y ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hy.1, by rw [← hTT]; exact hy.2⟩
  have hg0 := Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq
  have hg0V : B.gq (T v).base y ∈ V := ⟨hg0.2, by
    show QO.qOf (T v).base.z (T v).base.z' (B.gq (T v).base y) ∈ U
    rw [QO.qOf_gq (T v).base hq]; exact hyU⟩

  have hJck : B.CkOn ⊤ (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') X :=
    Formalism.FourierDecayAlt.P.CutMP.jdc_ckOn_om _ _ hX.1
  set UU : Set (B.Mat S.G.k S.G.r) := JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' ∩ V with hUUdef
  have hUU : UU ⊆ JF.Om S.G.k S.G.r (T v).base.z (T v).base.z' := Set.inter_subset_left
  have hCkF : B.CkOn (B.opOrder Θ : ℕ∞) UU (B.JF (T v).base F) := by
    intro g₀ hg₀
    obtain ⟨U₁, f', hU₁, hgU₁, hc, he⟩ := hJck g₀ hg₀.1
    refine ⟨U₁ ∩ V, f', hU₁.inter hVo, ⟨hgU₁, hg₀.2⟩, (hc.mono Set.inter_subset_left).of_le ?_, ?_⟩
    · exact_mod_cast le_top
    · intro g hg hgG
      rw [← hJV g hg.2 hgG]
      exact he g hg.1 hgG
  have hg0UU : B.gq (T v).base y ∈ UU := ⟨hg0, hg0V⟩

  have hIn := Formalism.FourierDecayAlt.P.JFxG.cptInCC_G hFs hFc
    (fun g _ hg => image_eq_zero_of_notMem_tsupport hg)
    (6 * (S.G.r : ℝ) * (B.opOrder Θ : ℝ) +
      (S.G.r : ℝ) * (4 * (S.G.r : ℝ) + 2 * (S.G.k : ℝ)) * (6 * (S.G.r : ℝ) + 1) + 1) (B.opOrder Θ)
  obtain ⟨hT1, hT2⟩ := hT S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) (T v).base Θ _ F UU
    (thrW_sa S.G.k S.G.r (B.opOrder Θ)) hΘ.1 hΘ.2 hFs hIn hUU hCkF
  have hg0G : B.gq (T v).base y ∈ B.GV S.G.k S.G.r := hg0.1
  refine ⟨?_, ?_⟩
  · rw [← hT1 _ hg0]
    unfold B.opApply
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word Tm.word_lie hVo hJV _ hg0V hg0G]
  · rw [← hT2 _ hg0UU]
    unfold B.opAdj
    congr 1
    apply List.map_congr_left
    intro Tm _
    rw [Formalism.FourierDecayAlt.P.CutMP.JA.FFS.rw_local Tm.word.reverse
      (fun X hX => Tm.word_lie X (List.mem_reverse.1 hX)) hVo
      (f := fun g => Tm.coefAdj g (X g)) (f' := fun g => Tm.coefAdj g (B.JF (T v).base F g))
      (fun g hg hgG => by simp only [hJV g hg hgG]) _ hg0V hg0G]

theorem sAJCommC_of_adjComm (hAC : Formalism.FourierDecayAlt.P.CutMP.JA.FFS.AdjComm) : SAJCommC :=
  sAJCommC_of_thetaJ (LT.thetaJ_of_adjComm hAC)

theorem self_adjoint_commutation_compact : SAJCommC :=
  sAJCommC_of_adjComm Formalism.FourierDecayAlt.P.CutMP.JA.FFS.adjoint_commutation_holds

end Formalism.FourierDecayAlt.P.CutMP.JA.SA

end
