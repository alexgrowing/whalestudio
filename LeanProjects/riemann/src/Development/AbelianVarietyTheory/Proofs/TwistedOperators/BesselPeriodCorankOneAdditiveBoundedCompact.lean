import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankConvergesColumn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslateSobolevSepContinuous

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)

noncomputable section

namespace GlobalTheory.BplusLaws

private theorem norm_besChar_eq_one {D : D7} {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V}
    {ψ : AddChar (AF D.host.F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1) (d : BesDat A B ι) (n : GA D B) :
    ‖besChar ψ d n‖ = 1 := by
  unfold besChar
  split_ifs with h
  · obtain ⟨a, b, -, -, hv⟩ := h.choose_spec
    rw [hv]
    exact hψ _
  · simp

private theorem coCpt_gridData_V_zero {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) :
    GlobalTheory.Unf.CoCpt (G.V (.top 0)) := by
  have hV := GlobalTheory.FunObj.isV_Xp G
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact (G.V (.top 0)) fun τ =>
    GlobalTheory.DefiniteQuotient.posDef_of_signature (by
      have h1 := hV.sigOK (tauE D τ)
      rw [hV.sig (tauE D τ)] at h1
      exact h1)
  refine ⟨C, hC, fun g => ?_⟩
  obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
  exact ⟨γ⁻¹, inv_mem hγ, by rwa [← mul_assoc, inv_mul_cancel, one_mul]⟩

private theorem integrableOn_besInt_of_bounded {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil)
    (M : Vol G) (hM : M.IsRow) {φ : GA D (G.V (.top 0)) → ℂ} (hφc : Continuous φ) {Cφ : ℝ}
    (hCφ : ∀ g, ‖φ g‖ ≤ Cφ) (hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤)
    {F : GA D (G.V (.grid D.R.m 0)) → ℂ} (hFc : Continuous F) {K : ℝ}
    (hK : ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K) :
    (∀ h, IntegrableOn (besInt W φ F h) M.fdN M.νN) ∧
      IntegrableOn (fun h => ∫ n in M.fdN, besInt W φ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
  have hψ : ∀ x, ‖W.ψ x‖ = 1 := W.ψ_std.1.2.1
  obtain ⟨-, -, hBor, -⟩ := GlobalTheory.Per.Inhab.flag_topology _ G.besTop.e_iso
  haveI := GlobalTheory.Unf.EvalCont.firstCountable_GA (G.V (.top 0))
  have hemb : Continuous (embTop G) :=
    GlobalTheory.Per.Inhab.emb_continuous (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
      (fun h => (GlobalTheory.FunObj.embRel_iff _ h _).2 rfl)
  have hχ : Continuous fun n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e => besChar W.ψ G.besTop (n : GA D _) :=
    GlobalTheory.BesselChar.besChar_continuous _ W.ψ_std.1 _
  have hjoint : Continuous fun q : GA D (G.V (.top 0)) × NFlag (G.V (.grid D.R.m 0)) G.besTop.e =>
      besInt W φ F q.1 q.2 := by
    unfold besInt
    refine ((hφc.comp continuous_fst).mul (hFc.comp ?_)).mul ((hχ.comp continuous_snd).star)
    exact (continuous_subtype_val.comp continuous_snd).mul (hemb.comp continuous_fst)
  have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
    intro h n
    unfold besInt
    rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one hψ, mul_one]
    exact mul_le_mul (hCφ h) (hK h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
  have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
  refine ⟨fun h => Measure.integrableOn_of_bounded hNlt.ne ?_ (ae_of_all _ (hbd h)), ?_⟩
  · exact (hjoint.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · have hT : GlobalTheory.Unf.EvalCont.Tame fun h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e) => besInt W φ F h n :=
      GlobalTheory.Unf.EvalCont.tame_of_bounded hjoint hbd
    have hcont := GlobalTheory.Unf.EvalCont.Tame.continuous_integral M.νN M.fdN hNlt hT
    exact Measure.integrableOn_of_bounded hvol.ne hcont.aestronglyMeasurable
      (ae_of_all _ fun h => norm_setIntegral_le_of_norm_le_const hNlt fun n _ => hbd h n)

theorem bplus_add_bound : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  intro D T L sc G W M hM Ω hΩc hΩ φ hφ
  have hcpt := coCpt_gridData_V_zero G
  obtain ⟨haar, fund⟩ := GlobalTheory.FunObj.Vol.IsAt.haar_fund hM.top
  have hvol : M.ν (.top 0) (M.fd (.top 0)) < ⊤ := GlobalTheory.Unf.EvalCont.vol_lt_top hcpt ⟨_, _, haar, fund⟩
  have hOrb : ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) →
      ∀ h (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e), ‖F ((n : GA D _) * embTop G h)‖ ≤ K := by
    intro F hF K hK h n
    obtain ⟨γ, hγ, hmem⟩ := hΩ h n
    rw [← hF.2 γ hγ]
    exact hK _ hmem
  have hconv : ∀ ψ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)),
      (∀ h, IntegrableOn (besInt W ψ F h) M.fdN M.νN) ∧
        IntegrableOn (fun h => ∫ n in M.fdN, besInt W ψ F h n ∂M.νN) (M.fd (.top 0)) (M.ν (.top 0)) := by
    intro ψ hψ F hF
    obtain ⟨Cψ, hCψ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hψ.2, hψ.1⟩
    obtain ⟨K, hK⟩ := hΩc.exists_bound_of_continuousOn hF.1.continuousOn
    exact integrableOn_besInt_of_bounded W M hM hψ.1 hCψ hvol hF.1 (hOrb F hF K hK)
  obtain ⟨Cφ, hCφ⟩ := GlobalTheory.Unf.EvalCont.bounded_of_contAut hcpt ⟨hφ.2, hφ.1⟩
  refine ⟨Cφ * (M.ν (.top 0)).real (M.fd (.top 0)), ?_, ?_, ?_⟩
  · intro F hF F' hF'
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ hφ F' hF') fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro φ' hφ' F hF
    unfold Bplus
    refine GlobalTheory.Per.Inhab.iterated_add (hconv φ hφ F hF) (hconv φ' hφ' F hF) fun h n => ?_
    unfold besInt
    simp only [Pi.add_apply]
    ring
  · intro F hF K hK
    have hK' := hOrb F hF K hK
    have hNlt : M.νN M.fdN < ⊤ := by rw [hM.unip.2.2]; exact ENNReal.one_lt_top
    have hNr : M.νN.real M.fdN = 1 := by simp [Measure.real, hM.unip.2.2]
    have hbd : ∀ h n, ‖besInt W φ F h n‖ ≤ Cφ * K := by
      intro h n
      unfold besInt
      rw [norm_mul, norm_mul, norm_star, norm_besChar_eq_one W.ψ_std.1.2.1, mul_one]
      exact mul_le_mul (hCφ h) (hK' h n) (norm_nonneg _) (le_trans (norm_nonneg _) (hCφ h))
    unfold Bplus
    calc ‖∫ h in M.fd (.top 0), ∫ n in M.fdN, besInt W φ F h n ∂M.νN ∂M.ν (.top 0)‖
        ≤ (Cφ * K) * (M.ν (.top 0)).real (M.fd (.top 0)) := by
          refine norm_setIntegral_le_of_norm_le_const hvol fun h _ => ?_
          have := norm_setIntegral_le_of_norm_le_const hNlt fun n (_ : n ∈ M.fdN) => hbd h n
          rwa [hNr, mul_one] at this
      _ = Cφ * (M.ν (.top 0)).real (M.fd (.top 0)) * K := by ring

end GlobalTheory.BplusLaws

end
