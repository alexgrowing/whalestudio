import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDIdentSpec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSERDResRad
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJASASecFinal
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Gauge

variable {k r : ℕ}

def secGauge (k r : ℕ) (c : Fin r → ℂ) : ℂ := ∏ a : Fin r, ((‖c a‖ ^ (Mdim k r a - 1) : ℝ) : ℂ)

theorem secGauge_smooth : ContDiffOn ℝ ∞ (secGauge k r) (OmX r) := by
  unfold secGauge
  apply contDiffOn_prod
  intro a _ x hx
  apply ContDiffAt.contDiffWithinAt
  have h1 : ContDiffAt ℝ ∞ (fun c : Fin r → ℂ => ‖c a‖) x :=
    (contDiffAt_norm ℝ (hx a)).comp x (contDiff_apply ℝ ℂ a).contDiffAt
  exact (Complex.ofRealCLM.contDiff.contDiffAt).comp x (h1.pow _)

theorem secGauge_ne {c : Fin r → ℂ} (hc : c ∈ OmX r) : secGauge k r c ≠ 0 := by
  unfold secGauge
  refine Finset.prod_ne_zero_iff.mpr (fun a _ => ?_)
  exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr (hc a)))

theorem secGauge_inv_smooth : ContDiffOn ℝ ∞ (fun c => (secGauge k r c)⁻¹) (OmX r) := secGauge_smooth.inv (fun c hc => secGauge_ne hc)

theorem resG_last_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (J : Mx k r → E) (c : Fin r → ℂ)
    (g : Mx k r) : resG k r (Fin.last r) J c g = secGauge k r c • J (wCell k r (Fin.last r) c * g) := by
  unfold resG secGauge
  congr 1
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  rw [if_pos (show (a : ℕ) < (Fin.last r : ℕ) from a.isLt)]

end Gauge

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem spectral_section_identity : RDSSection := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' X μ L st l0 D hD _ _ _ _ _ _ _ Ψ _
  classical
  have hz : inWb P.k P.r z := hD.1.2.1
  have hz' : inWb P.k P.r z' := hD.1.2.2.1
  obtain ⟨h0, hs, he⟩ := Ψ.2

  let Φf : Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g => (secGauge P.k P.r c)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) c g
  have hmem : Φf ∈ RadSp P.k P.r z z' π π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = 0
      rw [h0 x hx, smul_zero]
    · obtain ⟨U, F, hU, hxU, hF, hΨ⟩ := hs x₀ hx₀
      have hV : IsOpen {x : (Fin P.r → ℂ) × Mx P.k P.r | x.1 ∈ OmX P.r} :=
        (Formalism.FourierDecayAlt.P.Qx3.isOpen_OmX P.r).preimage continuous_fst
      refine ⟨U ∩ {x | x.1 ∈ OmX P.r}, fun x => (secGauge P.k P.r x.1)⁻¹ • F x, hU.inter hV, ⟨hxU, hx₀.1⟩, ?_,
        fun x hx hxG => ?_⟩
      · have hg : ContDiffOn ℝ ∞ (fun x : (Fin P.r → ℂ) × Mx P.k P.r => (secGauge P.k P.r x.1)⁻¹)
            (U ∩ {x | x.1 ∈ OmX P.r}) :=
          secGauge_inv_smooth.comp contDiff_fst.contDiffOn fun x hx => hx.2
        exact hg.smul (hF.mono Set.inter_subset_left)
      · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2 = _
        rw [hΨ x hx.1 hxG]
    · show (secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (h * x.2 * h') =
        (π h).comp (((secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2).comp (π' h'))
      rw [he x hx h hh h' hh', ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  obtain ⟨D₀, hD₀, K, hK, hKv⟩ :=
    Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_descent_holds Wp Wq P.k P.r z z' π π' hz hz' Φf hmem
  have hsub : ∀ g ∈ Q.Glev P.k P.r 0 ∩ Q.OmPlus P.k P.r z z', g ∈ D₀ := by
    intro g hg
    obtain ⟨n, hn, n', hn', c, hc, g₁, hg₁, hGG, hgeq⟩ :=
      Formalism.FourierDecayAlt.P.CutMP.JA.SA.self_adjoint_cover_holds P.k P.r z z' hz hz' g hg
    have hw := (hKv c hc g₁ hg₁ hGG).1
    have hwG : Q.wCell P.k P.r (Fin.last P.r) c * g₁ ∈ Q.Glev P.k P.r 0 :=
      Formalism.FourierDecayAlt.P.Qx3.glev_mul (Formalism.FourierDecayAlt.P.Qx3.wlist_glev hc _)
        (Formalism.FourierDecayAlt.P.Qx3.glev_mono (Fin.zero_le _) hg₁)
    rw [hgeq]
    exact hD₀.2 _ ⟨hwG, hw⟩ n ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n, hn, (Matrix.one_mul n).symm⟩ n'
      ⟨1, Formalism.FourierDecayAlt.P.Qx8.uw_one _, n', hn', (Matrix.one_mul n').symm⟩
  have hKO : K ∈ Q.FFl P.k P.r z z' π π' 0 (Q.OmPlus P.k P.r z z') := by
    obtain ⟨hs', hL, hRt, hW⟩ := hK
    exact ⟨fun g₀ hg₀ => hs' g₀ ⟨hg₀.1, hsub g₀ hg₀⟩, fun g hg n hn => hL g ⟨hg.1, hsub g hg⟩ n hn,
      fun g hg n hn => hRt g ⟨hg.1, hsub g hg⟩ n hn, fun g hg h hh h' hh' => hW g ⟨hg.1, hsub g hg⟩ h hh h' hh'⟩
  refine ⟨K, ?_, fun x hx => ?_⟩
  · rw [rdb_ffl_om_eq]; exact hKO
  · rw [resG_last_eq, (hKv x.1 hx.1 x.2 hx.2.1 hx.2.2).2]
    show _ = secGauge P.k P.r x.1 • ((secGauge P.k P.r x.1)⁻¹ • (Ψ : Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 x.2)
    rw [smul_smul, mul_inv_cancel₀ (secGauge_ne hx.1), one_smul]

end Formalism.FourierDecayAlt.P.CutSE
