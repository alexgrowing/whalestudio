import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsQuasiFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaAbsoluteSum
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.WeilDatumExistence
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergTranslateThetaContinuousDifferentiableStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasFDerivAtOfContinuousCoordinatePartialsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtSobolevThetaFormHeisenbergAlongRealLinStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

namespace GlobalTheory.Unf.MatCoef

theorem contDiff_of_partials {k : ℕ} (P : ((Fin k → ℝ) → ℂ) → Prop) (hc : ∀ F, P F → Continuous F)
    (hd : ∀ F, P F → ∀ i : Fin k, ∃ (m : ℕ) (a H : Fin m → (Fin k → ℝ) → ℂ), (∀ j, ContDiff ℝ ∞ (a j)) ∧
      (∀ j, P (H j)) ∧ ∀ t, HasDerivAt (fun s : ℝ => F (t + s • Pi.single i 1)) (∑ j, a j t * H j t) 0) :
    ∀ F, P F → ContDiff ℝ ∞ F := by
  have key : ∀ n : ℕ, ∀ F, P F → ContDiff ℝ n F := by
    intro n
    induction n with
    | zero => intro F hF; exact contDiff_zero.2 (hc F hF)
    | succ n ih =>
      intro F hF
      choose m a H ha hH hD using hd F hF
      have hGc : ∀ i, Continuous fun t => ∑ j, a i j t * H i j t := fun i =>
        continuous_finset_sum _ fun j _ => ((ha i j).continuous).mul (hc _ (hH i j))
      have hfd := GlobalTheory.T.hasFDerivAt_of_continuous_coordinate_partials k F (fun i t => ∑ j, a i j t * H i j t) hGc hD
      have hfe : fderiv ℝ F = fun t => ∑ i, (∑ j, a i j t * H i j t) •
          (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ).smulRight (1 : ℂ) := by
        funext t
        rw [(hfd t).fderiv]
        refine Finset.sum_congr rfl fun i _ => ?_
        ext x
        simp [mul_comm]
      rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_fderiv]
      refine ⟨fun t => (hfd t).differentiableAt, by simp, ?_⟩
      rw [hfe]
      refine ContDiff.sum fun i _ => ?_
      have hs : ContDiff ℝ n fun t => ∑ j, a i j t * H i j t :=
        ContDiff.sum fun j _ => ((ha i j).of_le (mod_cast le_top)).mul (ih _ (hH i j))
      exact hs.smul contDiff_const
  intro F hF
  exact contDiff_infty.2 fun n => key n F hF

end GlobalTheory.Unf.MatCoef

namespace GlobalTheory.Unf.MatCoef

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {S T : HSp D}

theorem form_sub {ℓ : (WO S T → ℂ) → ℂ} (hℓ : IsSobForm ψ θ S T ℓ) {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hg : IsThetaFunO ψ S T g) : ℓ (f - g) = ℓ f - ℓ g := by
  have e : f - g = f + (-1 : ℂ) • g := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, hℓ.add f _ hf (theta_smul (-1) hg), hℓ.smul (-1) g hg]
  ring

theorem symplOH_zero_left (u : WO S T) : symplOH S T 0 u = 0 := by
  have := symplOH_add_left (S := S) (T := T) 0 0 u
  rw [add_zero] at this
  linear_combination -this

theorem decomp (h : Chart θ σ) (a : WO S T) : (iotaW σ T S (piW θ T S a)).map (finPart D) = 0 ∧
    (a - iotaW σ T S (piW θ T S a)).map (infPart D) = 0 := by
  refine ⟨h.real_iota T S _, ?_⟩
  have hp : piW θ T S (a - iotaW σ T S (piW θ T S a)) = 0 := by rw [AddMonoidHom.map_sub, h.pi_iota, sub_self]
  ext i j
  exact ThetaCont.infPart_eq_zero h _ fun τ => congrFun (congrFun (congrFun hp τ) i) j

theorem theta_heisO_any (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (u : WO S T) : IsThetaFunO ψ S T (heisO ψ S T u f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨hr, hn⟩ := decomp h u
  have e : heisO ψ S T u f = heisO ψ S T (iotaW σ T S (piW θ T S u)) (heisO ψ S T (u - iotaW σ T S (piW θ T S u)) f) := by
    rw [heisO_heisO, (symplOH_fin_real hn hr).2, AddChar.map_zero_eq_one, one_smul, add_sub_cancel]
  rw [e]
  exact theta_heisO_real hθ hψ hr (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf hn)

theorem continuous_form (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {ℓ : (WO S T → ℂ) → ℂ}
    (hℓ : IsSobForm ψ θ S T ℓ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    Continuous fun u => ℓ (heisO ψ S T u f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  haveI : IsTopologicalAddGroup (Formalism.L2.Theta.AE D) := IsTopologicalRing.to_topologicalAddGroup
  haveI : IsTopologicalAddGroup (WO S T) := Pi.topologicalAddGroup
  haveI : ContinuousSub (WO S T) := IsTopologicalAddGroup.to_continuousSub
  haveI : ContinuousAdd (WO S T) := inferInstance
  refine continuous_iff_continuousAt.2 fun u₀ => ?_
  have hg : IsThetaFunO ψ S T (heisO ψ S T u₀ f) := theta_heisO_any hψ hθ hf u₀
  obtain ⟨U, hU, hl⟩ := hg.level
  obtain ⟨d, C, hC⟩ := hℓ.bound U hU
  have hgU : heisO ψ S T u₀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hg, hl⟩
  let r : WO S T → WO S T := fun a => iotaW σ T S (piW θ T S a)
  have hrc : Continuous r := (h.continuous_iota T S).comp (continuous_pi' hθ T S)
  have hr0 : r 0 = 0 := by simp [r]
  have hnc : Continuous fun a => a - r a := continuous_id.sub hrc
  have hev : ∀ᶠ a in 𝓝 (0 : WO S T), a - r a ∈ U :=
    hnc.continuousAt.preimage_mem_nhds (hU.mem_nhds (by simp [hr0]))
  have hform : ∀ a, a - r a ∈ U → ℓ (heisO ψ S T (u₀ + a) f) =
      ψ (-(symplOH S T a u₀)) * ℓ (heisO ψ S T (r a) (heisO ψ S T u₀ f)) := by
    intro a ha
    obtain ⟨hr, hn⟩ := decomp h a
    have e1 : heisO ψ S T (r a) (heisO ψ S T u₀ f) = heisO ψ S T a (heisO ψ S T u₀ f) := by
      have e2 : heisO ψ S T (a - r a) (heisO ψ S T (r a) (heisO ψ S T u₀ f)) = heisO ψ S T (r a) (heisO ψ S T u₀ f) :=
        heisO_comm_fin_real hn hr (hl _ ha hn)
      rw [← e2, heisO_heisO, (symplOH_fin_real hn hr).1, AddChar.map_zero_eq_one, one_smul, sub_add_cancel]
    have e3 : heisO ψ S T a (heisO ψ S T u₀ f) = ψ (symplOH S T a u₀) • heisO ψ S T (u₀ + a) f := by
      rw [heisO_heisO, add_comm]
    rw [e1, e3, hℓ.smul _ _ (theta_heisO_any hψ hθ hf _), ← mul_assoc, ← AddChar.map_add_eq_mul, neg_add_cancel,
      AddChar.map_zero_eq_one, one_mul]
  have hphase : Filter.Tendsto (fun a => ψ (-(symplOH S T a u₀))) (𝓝 0) (𝓝 1) := by
    have hc : Continuous fun a : WO S T => ψ (-(symplOH S T a u₀)) :=
      hψ.1.1.comp (continuous_symplOH continuous_id continuous_const).neg
    simpa only [symplOH_zero_left, neg_zero, AddChar.map_zero_eq_one] using hc.tendsto 0
  have hmain : Filter.Tendsto (fun a => ℓ (heisO ψ S T (r a) (heisO ψ S T u₀ f))) (𝓝 0)
      (𝓝 (ℓ (heisO ψ S T u₀ f))) := by
    have ht := ((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T d _ hg).1).comp (hrc.tendsto' 0 0 hr0)
    have ht2 : Filter.Tendsto (fun a => (C : ℝ≥0∞) * supSob ψ θ d (heisO ψ S T (r a) (heisO ψ S T u₀ f) - heisO ψ S T u₀ f))
        (𝓝 0) (𝓝 0) := by
      simpa only [mul_zero, Function.comp_def] using ENNReal.Tendsto.const_mul ht (Or.inr ENNReal.coe_ne_top)
    rw [tendsto_iff_edist_tendsto_0]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht2 (fun _ => zero_le) fun a => ?_
    have hm : heisO ψ S T (r a) (heisO ψ S T u₀ f) ∈ GlobalTheory.Size.thetaLevel ψ S T U :=
      ⟨theta_heisO_real hθ hψ (h.real_iota T S _) hg, fun u hu h0 => heisO_comm_fin_real h0 (h.real_iota T S _) (hl u hu h0)⟩
    show edist _ _ ≤ _
    rw [edist_eq_enorm_sub, ← form_sub hℓ hm.1 hg]
    exact hC _ (sub_mem hm hgU)
  have hlim : Filter.Tendsto (fun a => ℓ (heisO ψ S T (u₀ + a) f)) (𝓝 0) (𝓝 (ℓ (heisO ψ S T u₀ f))) := by
    have := hphase.mul hmain
    rw [one_mul] at this
    exact this.congr' (hev.mono fun a ha => (hform a ha).symm)
  have hc2 : Filter.Tendsto (fun u => u - u₀) (𝓝 u₀) (𝓝 0) := tendsto_sub_nhds_zero_iff.2 Filter.tendsto_id
  exact (hlim.comp hc2).congr fun u => by simp only [Function.comp_apply, add_sub_cancel]

theorem deriv_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {M : ℝ →+ WO S T} (hM : Continuous M)
    (hMf : ∀ s, (M s).map (finPart D) = 0) (w : WO S T) :
    deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 =
      -(Real.pi * Complex.I) * (omO S T (piW θ T S w) (piW θ T S (M 1)) : ℂ) := by
  have hlin : ∀ s : ℝ, piW θ T S (M s) = s • piW θ T S (M 1) := fun s => by
    have := map_real_smul ((piW θ T S).comp M) ((continuous_pi' h.inf T S).comp hM) s 1
    simpa using this
  have e : (fun s : ℝ => ψ (symplOH S T w (M s))) = fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) := by
    funext s
    rw [← h.iota_pi (hMf s), psi_symplOH h hψ, hlin, LinearMap.map_smul, smul_eq_mul]
  rw [e]
  have hd : HasDerivAt (fun s : ℝ =>
      Complex.exp (-(Real.pi * Complex.I) * ((s * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)))
      (Complex.exp (-(Real.pi * Complex.I) * (((0 : ℝ) * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ)) *
        (-(Real.pi * Complex.I) * ((1 * omO S T (piW θ T S w) (piW θ T S (M 1)) : ℝ) : ℂ))) 0 :=
    ((((hasDerivAt_id (0 : ℝ)).mul_const (omO S T (piW θ T S w) (piW θ T S (M 1)))).ofReal_comp).const_mul
      (-(Real.pi * Complex.I))).cexp
  rw [hd.deriv]
  simp

theorem contDiff_phase (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {k : ℕ} {L : (Fin k → ℝ) →+ WO S T}
    (hL : Continuous L) {M : ℝ →+ WO S T} (hM : Continuous M) (hMf : ∀ s, (M s).map (finPart D) = 0) (u : WO S T) :
    ContDiff ℝ ∞ fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0 := by
  let A : (Fin k → ℝ) →L[ℝ] RW T S := AddMonoidHom.toRealLinearMap ((piW θ T S).comp L) ((continuous_pi' h.inf T S).comp hL)
  let B : RW T S →L[ℝ] ℝ := LinearMap.toContinuousLinearMap ((omO S T).flip (piW θ T S (M 1)))
  have hB : ∀ t, B (A t) = omO S T (piW θ T S (L t)) (piW θ T S (M 1)) := fun t => rfl
  have e : (fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0) = fun t =>
      (Real.pi * Complex.I) * Complex.ofRealCLM (omO S T (piW θ T S u) (piW θ T S (M 1)) + B (A t)) := by
    funext t
    rw [deriv_phase h hψ hM hMf, hB, AddMonoidHom.map_add, LinearMap.map_add₂, Complex.ofRealCLM_apply]
    ring
  rw [e]
  have hc : ContDiff ℝ ∞ fun t => omO S T (piW θ T S u) (piW θ T S (M 1)) + B (A t) :=
    contDiff_const.add (B.contDiff.comp A.contDiff)
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hc)

end GlobalTheory.Unf.MatCoef

namespace GlobalTheory.Unf.MatCoef

open GlobalTheory.OrientedHeis GlobalTheory.FockCompare

theorem matCoef_smooth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ →
    ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f →
    Continuous (fun u => ℓ (heisO ψ S T u f)) ∧ ∀ (k : ℕ) (L : (Fin k → ℝ) →+ WO S T), Continuous L →
      (∀ t, (L t).map (finPart D) = 0) → ∀ u, ContDiff ℝ ∞ fun t => ℓ (heisO ψ S T (u + L t) f) := by
  intro D ψ hψ θ hθ S T ℓ hℓ f hf
  refine ⟨continuous_form hψ hθ hℓ hf, fun k L hL hLf u => ?_⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  let P : ((Fin k → ℝ) → ℂ) → Prop := fun F =>
    ∃ (u : WO S T) (f : WO S T → ℂ), IsThetaFunO ψ S T f ∧ F = fun t => ℓ (heisO ψ S T (u + L t) f)
  refine contDiff_of_partials P ?_ ?_ _ ⟨u, f, hf, rfl⟩
  · rintro _ ⟨u, f, hf, rfl⟩
    exact (continuous_form hψ hθ hℓ hf).comp (continuous_const.add hL)
  · rintro _ ⟨u, f, hf, rfl⟩ i
    let E : ℝ →ₗ[ℝ] (Fin k → ℝ) := LinearMap.toSpanSingleton ℝ (Fin k → ℝ) (Pi.single i 1)
    let M : ℝ →+ WO S T := L.comp E.toAddMonoidHom
    have hM : Continuous M := hL.comp E.continuous_of_finiteDimensional
    have hMf : ∀ s, (M s).map (finPart D) = 0 := fun s => hLf _
    have hf' : IsThetaFunO ψ S T (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0) :=
      ((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T 0 f hf).2 M hM hMf).1
    refine ⟨2, ![fun _ => 1, fun t => -deriv (fun s : ℝ => ψ (symplOH S T (u + L t) (M s))) 0],
      ![fun t => ℓ (heisO ψ S T (u + L t) (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)),
        fun t => ℓ (heisO ψ S T (u + L t) f)], fun j => ?_, fun j => ?_, fun t => ?_⟩
    · fin_cases j
      · exact contDiff_const
      · exact contDiff_phase h hψ hL hM hMf u
    · fin_cases j
      · exact ⟨u, _, hf', rfl⟩
      · exact ⟨u, f, hf, rfl⟩
    · have e : (fun s : ℝ => ℓ (heisO ψ S T (u + L (t + s • Pi.single i 1)) f)) =
          fun s => ℓ (heisO ψ S T ((u + L t) + M s) f) := by
        funext s
        have : E s = s • Pi.single i 1 := rfl
        rw [map_add, add_assoc, ← this]
        rfl
      rw [e]
      convert GlobalTheory.T.hasDerivAt_sobolevThetaForm_heisenberg_along_real_line D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf (u + L t) using 1
      simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_mul]
      ring

end GlobalTheory.Unf.MatCoef
