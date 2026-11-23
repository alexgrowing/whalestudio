import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientModelConjDiscreteSeriesOfGapStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TranslatedEvaluationSquareIntegrableNormAllRowsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjTranslatedLevelRowEvaluationMemAllRowsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRowLevelTranslatedEvaluationOfConjRowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.SRe

set_option maxHeartbeats 1000000 in

theorem evalOn_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) ∧ ∃ c : ℝ, 0 < c ∧ EvalOn R X h t v₀ c (MultR R F) (conjRows X) := by
  intro hDS hCusp hU hFin D G' _ _ Pl0 T A Ks _ _ _ R F X h t hE hGap hl hi hν hsee
  obtain ⟨cc, hcc, hsm⟩ := GlobalTheory.T.contragredientModel_conjDiscreteSeries_of_gap hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  let v₀ : (MP R).Vec := fun τ => ⟨(cc τ).symm (X.B.w (X.pl.symm τ)), hsm τ⟩
  have hv₀ : ∀ τ, cc τ (v₀ τ : (MP R).H τ) = X.B.w (X.pl.symm τ) := fun τ => by simp [v₀]
  have hnorm : ∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1 := fun τ => by
    show ‖(cc τ).symm (X.B.w (X.pl.symm τ))‖ = 1
    rw [LinearIsometryEquiv.norm_map]
    exact (X.low _).1
  obtain ⟨c0, hc0, hN⟩ := GlobalTheory.T.translatedEvaluation_squareIntegrable_norm_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee
  have hI := GlobalTheory.T.conj_translated_level_row_evaluation_mem_all_rows hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  have hO := GlobalTheory.T.exists_rowLevel_translatedEvaluation_of_conj_row hDS hCusp hU hFin D G' Pl0 T A Ks R F X h t hE hGap hl hi hν hsee cc v₀ hcc hv₀
  refine ⟨v₀, hnorm, c0, hc0, ?_⟩
  classical
  have hmem : ∀ S : MultR R F, MemLp (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) 2 (muX X) :=
    fun S => (hN v₀ hnorm S S.2).1
  let Φ : MultR R F → conjRows X := fun S =>
    ⟨(hmem S).toLp _, hI S S.2 _ (hmem S).coeFn_toLp⟩
  have hΦ : ∀ S, ((Φ S : conjRows X) : L2X X) =ᵐ[muX X]
      (fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) := fun S => (hmem S).coeFn_toLp
  have key : ∀ (S : MultR R F) (Fx : conjRows X), ((Fx : L2X X) =ᵐ[muX X]
      fun x => ev (MP R) v₀ (S : MMap (MP R)) ((iotaX X h).symm x * t)) → Φ S = Fx := by
    intro S Fx hF
    apply Subtype.ext
    apply Lp.ext
    exact (hΦ S).trans hF.symm
  let L : MultR R F →ₗ[ℂ] conjRows X :=
    { toFun := Φ
      map_add' := fun S S' => by
        apply key
        have h1 := hΦ S
        have h2 := hΦ S'
        have h3 := Lp.coeFn_add ((Φ S : conjRows X) : L2X X) ((Φ S' : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.add h2))).trans ?_
        · simp only [Submodule.coe_add]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply]
      map_smul' := fun a S => by
        rw [RingHom.id_apply]
        apply key
        have h1 := hΦ S
        have h3 := Lp.coeFn_smul a ((Φ S : conjRows X) : L2X X)
        refine (Filter.EventuallyEq.trans ?_ (h3.trans (h1.const_smul a))).trans ?_
        · simp only [Submodule.coe_smul]; rfl
        · refine Filter.Eventually.of_forall fun x => ?_
          simp [ev_apply] }
  have hLn : ∀ S : MultR R F, ‖((L S : conjRows X) : L2X X)‖ ^ 2 =
      c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re := by
    intro S
    show ‖((hmem S).toLp _ : L2X X)‖ ^ 2 = _
    rw [Formalism.IndefR.AutomorphicEvaluation.norm_sq_toLp (hmem S)]
    exact (hN v₀ hnorm S S.2).2.1
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro S hS
    have h1 := hLn S
    rw [hS] at h1
    simp only [ZeroMemClass.coe_zero, norm_zero] at h1
    have h2 : (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re = 0 := by
      rcases mul_eq_zero.mp (by rw [← h1]; ring : c0 * (ipM (MP R) R.ν0 R.fd0 (S : MMap (MP R)) (S : MMap (MP R))).re = 0) with h' | h'
      · exact absurd h' hc0.ne'
      · exact h'
    exact Subtype.ext ((hN v₀ hnorm S S.2).2.2 h2)
  have hsurj : Function.Surjective L := by
    intro Fx
    obtain ⟨S, hS, hF⟩ := hO (Fx : L2X X) Fx.2
    exact ⟨⟨S, hS⟩, key ⟨S, hS⟩ Fx hF⟩
  refine ⟨LinearEquiv.ofBijective L ⟨hinj, hsurj⟩, fun S => ⟨hΦ S, hLn S⟩⟩

end GlobalTheory.Mem.SRe
