import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransfer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TranslatedRowEvaluationSquareIntegrableNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Formalism.LocalToGlobal.IndefiniteReal.SquareIntegrableTransferOfFundamentalDomains
import Formalism.LocalToGlobal.IndefiniteReal.PeterssonHilbertSpace
import Formalism.LocalToGlobal.IndefiniteReal.MeasurableMulGA
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.EvalAllRows

theorem eq_zero_of_units {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T : MMap M)
    (h : ∀ v : M.Vec, (∀ τ, ‖(v τ : M.H τ)‖ = 1) → T v = 0) : T = 0 := by
  classical
  refine MultilinearMap.ext fun v => ?_
  by_cases hz : ∃ τ, v τ = 0
  · obtain ⟨τ, hτ⟩ := hz
    exact T.map_coord_zero τ hτ
  · push_neg at hz
    have hn : ∀ τ, ‖(v τ : M.H τ)‖ ≠ 0 := fun τ e => hz τ (Subtype.ext (norm_eq_zero.1 e))
    let u : M.Vec := fun τ => ((‖(v τ : M.H τ)‖⁻¹ : ℝ) : ℂ) • v τ
    have hu : ∀ τ, ‖(u τ : M.H τ)‖ = 1 := fun τ => by
      simp only [u, Submodule.coe_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hn τ)
    have hv : v = fun τ => ((‖(v τ : M.H τ)‖ : ℝ) : ℂ) • u τ := by
      funext τ
      simp only [u, smul_smul]
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (hn τ), Complex.ofReal_one, one_smul]
    rw [hv, T.map_smul_univ, h u hu, smul_zero]
    rfl

end GlobalTheory.EvalAllRows

theorem GlobalTheory.EvalAllRows.evalTranslate_norm_all : GlobalTheory.Dec.DSInfChar → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.DiscreteSeriesUpqUnique → Formalism.L2.SG.RowsDef.RowsFinDim → ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (D.sp.Y 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → GapHyp D → R.toLevCh.Is A.μ0 → R.models_inf → R.models_ν0 → SeeAt R F X h t → ∃ c : ℝ, 0 < c ∧ ∀ v₀ : (MP R).Vec, (∀ τ, ‖(v₀ τ : (MP R).H τ)‖ = 1) → ∀ S ∈ MultR R F, MemLp (fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t)) 2 (muX X) ∧ ∫ x, ‖ev (MP R) v₀ S ((iotaX X h).symm x * t)‖ ^ 2 ∂(muX X) = c * (ipM (MP R) R.ν0 R.fd0 S S).re ∧ ((ipM (MP R) R.ν0 R.fd0 S S).re = 0 → S = 0) := by
  intro _ hCusp _ _ D G' _ _ Pl0 T A Ks _ _ _ R F X h t hHE hGap hL hinf hν0 hsee
  haveI hνH : R.ν0.IsHaarMeasure := hν0.1.1
  obtain ⟨c, hc, hmap⟩ := @GlobalTheory.EvalNormTransfer.exists_map_eq_smul D X h R.ν0 hνH
  obtain ⟨hι, hιs⟩ := measurable_of_borel X (iotaX X h) (GlobalTheory.EvalNormTransfer.borel_inst X)
  have hTr : SquareIntegrableTransfer R.ν0 R.fd0 X (iotaX X h).toMulEquiv t c :=
    squareIntegrableTransfer_of_rational_points R.ν0 R.fd0 X _ t c hι hιs hc hmap hνH hν0.2 (GlobalTheory.EvalNormTransfer.iotaX_rat X h)
  refine ⟨c, hc, fun v₀ hv S hS => ?_⟩
  have hSch : ∀ S' ∈ MultR R F, ∃ c', IsMultIP (MP R) R.ν0 R.fd0 S' S' c' := fun S' hS' =>
    GlobalTheory.MultFinite.schurMult hCusp R.ν0 R.fd0 hinf hνH hν0.2 S' hS' S' hS'
  have hcont : ∀ S' ∈ MultR R F, ∀ v, Continuous (S' v) ∧ ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S' v (γ * g) = S' v g :=
    fun S' hS' v => Formalism.IndefR.PeterssonHilbertSpace.mult_cont_left (M := R.MY 0) (θ := R.θ) (J := JR R F) (χ := chiR R F) hS' v
  haveI : BorelSpace (GA D (D.sp.Y 0)) := Formalism.IndefR.PeterssonHilbertSpace.borel_GA (Yc D 0)
  have hL2 : ∀ S' ∈ MultR R F, ∀ v, MemLp (S' v) 2 (R.ν0.restrict R.fd0) := by
    intro S' hS' v
    obtain ⟨c', hip⟩ := hSch S' hS'
    refine (memLp_two_iff_integrable_sq_norm (hcont S' hS' v).1.measurable.aestronglyMeasurable).2
      (((hip v v).1).norm.congr (.of_forall fun x => ?_))
    simp only [norm_mul, norm_star, sq]
  obtain ⟨hm, hn⟩ := hTr (S v₀) (hcont S hS v₀).1 (hcont S hS v₀).2 (hL2 S hS v₀)
  refine ⟨hm, hn.trans (congrArg (c * ·) (re_ipM_eq (hSch S hS) hv).symm), ?_⟩
  intro h0
  refine GlobalTheory.EvalAllRows.eq_zero_of_units (MP R) S fun v hv' => ?_
  by_contra hne
  have hre := re_ipM_eq (hSch S hS) hv'
  have hint : IntegrableOn (fun x => ‖S v x‖ ^ 2) R.fd0 R.ν0 :=
    (memLp_two_iff_integrable_sq_norm (hL2 S hS v).1).1 (hL2 S hS v)
  have hp := Formalism.IndefR.PeterssonHilbertSpace.petPos (D.sp.Y 0) R.ν0 R.fd0 hνH hν0.2 (S v) (hcont S hS v).1 (hcont S hS v).2 hne hint
  rw [← hre, h0] at hp
  exact lt_irrefl _ hp
