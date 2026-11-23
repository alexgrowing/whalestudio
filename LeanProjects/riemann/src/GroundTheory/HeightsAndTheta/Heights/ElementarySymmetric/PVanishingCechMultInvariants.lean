import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.VanishingCechMultInvariants
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.TorsionAverageBasics
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem VanishingCechMultInvariants.proof (hPB : PullbackMulMem.Statement)
    (hTA : TorsAvgDescends.Statement) : VanishingCechMultInvariants.Statement := by
  intro P a _ r x hx m hm n q hvan φ hφ
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have hmw : ∀ w : Fin P.g → ℂ, (m : ℂ) • ((m : ℂ)⁻¹ • w) = w := fun w => by
    rw [smul_smul, mul_inv_cancel₀ hm0, one_smul]

  have hprod : ∀ (J : Finset (Fin (r + 1))) u v w,
      ∏ i ∈ J, x i (w + P.latVec u v) = P.autL (a * J.card) u v w * ∏ i ∈ J, x i w := by
    intro J u v w
    rw [Finset.prod_congr rfl (fun i _ => P.thetaSec_add_latVec (P.S_le a _ (hx.1 i)) u v w),
      Finset.prod_mul_distrib, Finset.prod_const, P.autL_mul]
  have hprod0 : ∀ (J : Finset (Fin (r + 1))) w, w ∈ P.chartSet x J → ∏ i ∈ J, x i w ≠ 0 :=
    fun J w hw => Finset.prod_ne_zero_iff.mpr hw
  have hchart : ∀ (J : Finset (Fin (r + 1))) u v w, w ∈ P.chartSet x J →
      w + P.latVec u v ∈ P.chartSet x J := by
    intro J u v w hw i hi
    rw [P.thetaSec_add_latVec (P.S_le a _ (hx.1 i))]
    exact mul_ne_zero (P.autL_ne_zero _ _ _ _) (hw i hi)

  have hφt : ∀ J : Finset (Fin (r + 1)), J.card = q + 2 → ∀ w ∈ P.chartSet x J, ∀ u v,
      φ J (w + P.latVec u v) = P.autL n u v w * φ J w := by
    intro J hJ w hw u v
    obtain ⟨k, f, hf, hfe⟩ := hφ.1 J hJ
    rw [hfe _ (hchart J u v w hw), hfe _ hw, hprod, P.thetaSec_add_latVec (P.S_le _ _ hf),
      P.autL_add, P.autL_mul (a * J.card) k]
    have h1 := P.autL_ne_zero (a * J.card) u v w
    have h2 := hprod0 J w hw
    field_simp
    ring

  have hφ' : P.IsCocycle (a * m ^ 2) (n * m ^ 2) (q + 1) (fun j z => x j ((m : ℂ) • z))
      (fun J z => φ J ((m : ℂ) • z)) := by
    refine ⟨fun J hJ => ?_, fun J hJ z hz => hφ.2 J hJ _ hz⟩
    obtain ⟨k, f, hf, hfe⟩ := hφ.1 J hJ
    refine ⟨k, fun z => f ((m : ℂ) • z), ?_, fun z hz => hfe _ hz⟩
    rw [show n * m ^ 2 + a * m ^ 2 * J.card * k = (n + a * J.card * k) * m ^ 2 by ring]
    exact hPB P m _ f hf
  obtain ⟨ψ', hψ'c, hψ'd⟩ := hvan _ hφ'
  have hpt : ∀ (J : Finset (Fin (r + 1))) (w : Fin P.g → ℂ), w ∈ P.chartSet x J →
      ∀ u v : Fin P.g → Fin m, (m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v) ∈
        P.chartSet (fun j z => x j ((m : ℂ) • z)) J := by
    intro J w hw u v
    show ∀ i ∈ J, x i ((m : ℂ) • ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v))) ≠ 0
    rw [← smul_add, hmw]
    exact hchart J _ _ w hw

  refine ⟨fun J w => P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w), fun J hJ => ?_, fun J hJ w hw => ?_⟩
  · obtain ⟨k, F, hF, hFe⟩ := hψ'c J hJ
    have hF' : F ∈ P.S ((n + a * J.card * k) * m ^ 2) := by
      rw [show (n + a * J.card * k) * m ^ 2 = n * m ^ 2 + a * m ^ 2 * J.card * k by ring]; exact hF
    obtain ⟨f, hf, hfe⟩ := hTA P m hm _ F hF'
    refine ⟨k, f, hf, fun w hw => ?_⟩
    have hY : ∀ u v : Fin P.g → Fin m,
        (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
          P.autL (a * J.card) (torsIdx u) (torsIdx v) ((m : ℂ) • ((m : ℂ)⁻¹ • w)) *
            (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) := by
      intro u v
      simp only [← smul_add, hmw]
      exact hprod J _ _ w
    have hY0 : (fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) ≠ 0 := by
      simp only [hmw]; exact hprod0 J w hw
    have hG : ∀ u v : Fin P.g → Fin m,
        ψ' J ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) =
          F ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) /
            (fun z => ∏ i ∈ J, x i ((m : ℂ) • z))
              ((m : ℂ)⁻¹ • w + (m : ℂ)⁻¹ • P.latVec (torsIdx u) (torsIdx v)) ^ k := by
      intro u v
      exact hFe _ (hpt J w hw u v)
    have key := P.torsAvg_div (n := n) (d := a * J.card) (k := k) (m := m) (F := F) (G := ψ' J)
      (Y := fun z => ∏ i ∈ J, x i ((m : ℂ) • z)) (z := (m : ℂ)⁻¹ • w) hY hY0 hG
    show P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w) = f w / (∏ i ∈ J, x i w) ^ k
    rw [key, hfe]
    simp only [hmw]
  · have h1 : cechD (fun J w => P.torsAvg n m (ψ' J) ((m : ℂ)⁻¹ • w)) J w =
        cechD (fun I => P.torsAvg n m (ψ' I)) J ((m : ℂ)⁻¹ • w) := by
      simp only [cechD]
    have h2 : P.torsAvg n m (cechD ψ' J) ((m : ℂ)⁻¹ • w) =
        P.torsAvg n m (fun z => φ J ((m : ℂ) • z)) ((m : ℂ)⁻¹ • w) :=
      P.torsAvg_congr (fun u v => hψ'd J hJ _ (hpt J w hw u v))
    rw [h1, P.torsAvg_cechD, h2]
    exact P.torsAvg_pullback hm (fun u v => hφt J hJ w hw _ _)

end

end GroundTheory.Heights₂.Heights.KeyFormula
