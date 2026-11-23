import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LeExpOfLogLe
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RamifiedPrimePowersSizeBounds

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem span_image_smul_top {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (c : K) (hc : c ≠ 0)
    (S : Set V) (hS : Submodule.span K S = ⊤) : Submodule.span K ((fun g => c • g) '' S) = ⊤ := by
  refine eq_top_iff.mpr fun v _ => ?_
  have key : ∀ x ∈ Submodule.span K S, c • x ∈ Submodule.span K ((fun g => c • g) '' S) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
    | smul e x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ e hx
  have hv : c⁻¹ • v ∈ Submodule.span K S := hS ▸ Submodule.mem_top
  simpa [smul_smul, hc] using key _ hv

theorem shortG_scaled : ∀ (D : D7) (B : WeightFamilies.Prov D) (P : ModuliIntegralCharts.Prov D) (j : ℕ) (X : PJ D B P j) (w : WeightFamilies.Wt D j) (s : 𝓞 B.KO) (Sh : Finset (B.Cusp j w)) (a b : ℝ), s ≠ 0 → 0 ≤ a → 0 ≤ b → (∀ σ : B.KO →+* ℂ, Real.log ‖σ (s : B.KO)‖ ≤ a) → (∀ g ∈ Sh, g ∈ X.shortTh w ∧ ∀ σ, Real.log (B.supN j w σ g) ≤ b) → Submodule.span B.KO (Sh : Set (B.Cusp j w)) = ⊤ → ShortG X w (X.Thc s w) (a + b + lamStar D * w.size) := by
  intro D B P j X w s Sh a b hs ha hb hsa hSh hspan
  classical

  let N : ℕ := D.host.g 0 * D.host.g 1
  let k : ℕ := D.R.f * D.R.r * w.n
  let t : 𝓞 B.KO := s * (N : 𝓞 B.KO) ^ k
  have hN1 : (1 : ℝ) ≤ N := by
    have h0 := (D.host.g_prime 0).one_lt
    have h1 := (D.host.g_prime 1).one_lt
    have : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    exact_mod_cast this
  have htK : ((t : 𝓞 B.KO) : B.KO) = (s : B.KO) * ((N : ℕ) : B.KO) ^ k := by
    simp [t]
  have hsK : (s : B.KO) ≠ 0 := fun h => hs (by exact_mod_cast h)
  have hNK : ((N : ℕ) : B.KO) ≠ 0 := by
    have : N ≠ 0 := by
      intro h; rw [h] at hN1; norm_num at hN1
    exact_mod_cast this
  have ht0 : ((t : 𝓞 B.KO) : B.KO) ≠ 0 := by
    rw [htK]; exact mul_ne_zero hsK (pow_ne_zero _ hNK)
  have hsm : ∀ g : B.Cusp j w, t • g = ((t : 𝓞 B.KO) : B.KO) • g := fun g =>
    (algebraMap_smul B.KO t g).symm
  have hlam : 0 ≤ Real.log N ∧ Real.log N ≤ lamStar D := by
    have h2 := (pPow_size D j w).2.2.1
    refine ⟨Real.log_nonneg hN1, ?_⟩
    unfold Formalism.MainNotions.WeightAlgebra.lamStar
    have : ((N : ℕ) : ℝ) = (D.host.g 0 : ℝ) * D.host.g 1 := by simp [N]
    rw [← this]; linarith
  have hk : (k : ℝ) ≤ w.size := by
    unfold WeightFamilies.Wt.size
    have hm : (1 : ℝ) ≤ ((max (D.R.sigW j).2 1 : ℕ) : ℝ) := by exact_mod_cast le_max_right _ _
    have hsum : 0 ≤ ∑ τ, ((∑ i, (w.aP τ i : ℝ)) + ∑ i, (w.aM τ i : ℝ)) := by positivity
    have : (k : ℝ) ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (w.n : ℝ) := by
      calc (k : ℝ) = (D.R.f : ℝ) * 1 * (D.R.r : ℝ) * (w.n : ℝ) := by simp [k]
        _ ≤ _ := by gcongr
    linarith
  refine ⟨Sh.image fun g => t • g, ?_, ?_, ?_⟩
  · intro x hx
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    simp only [PJ.Thc, PJ.scaled]
    refine Submodule.mem_map.mpr ⟨((N : 𝓞 B.KO) ^ k) • g, Submodule.mem_map.mpr ⟨g, (hSh g hg).1, by simp [N, k]⟩, ?_⟩
    simp only [t, mul_smul, LinearMap.smul_apply, LinearMap.id_apply]
  · have : ((Sh.image fun g => t • g : Finset (B.Cusp j w)) : Set (B.Cusp j w)) =
        (fun g => ((t : 𝓞 B.KO) : B.KO) • g) '' (Sh : Set (B.Cusp j w)) := by
      rw [Finset.coe_image]
      exact congrArg (· '' (Sh : Set (B.Cusp j w))) (funext hsm)
    rw [this]
    exact span_image_smul_top _ ht0 _ hspan
  · intro x hx
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hx
    apply WeightFamilies.meanLogSup_le
    intro σ
    rw [hsm, B.supN_smul, htK]
    have hσs : 0 < ‖σ (s : B.KO)‖ := norm_pos_iff.mpr ((map_ne_zero σ).mpr hsK)
    have hnorm : ‖σ ((s : B.KO) * ((N : ℕ) : B.KO) ^ k)‖ = ‖σ (s : B.KO)‖ * (N : ℝ) ^ k := by
      simp
    rw [hnorm]
    have hlog_s := hsa σ
    have hG := (hSh g hg).2 σ
    have hkN : (k : ℝ) * Real.log N ≤ lamStar D * w.size := by
      calc (k : ℝ) * Real.log N ≤ w.size * Real.log N := mul_le_mul_of_nonneg_right hk hlam.1
        _ ≤ w.size * lamStar D :=
            mul_le_mul_of_nonneg_left hlam.2 (by linarith [WeightFamilies.Wt.one_le_size w])
        _ = lamStar D * w.size := mul_comm _ _
    by_cases hg0 : B.supN j w σ g = 0
    · rw [hg0, mul_zero, Real.log_zero]
      have : 0 ≤ lamStar D * w.size :=
        mul_nonneg (hlam.1.trans hlam.2) (by linarith [WeightFamilies.Wt.one_le_size w])
      linarith
    · have hNk : (0 : ℝ) < (N : ℝ) ^ k := pow_pos (by linarith) _
      rw [Real.log_mul (mul_pos hσs hNk).ne' hg0, Real.log_mul hσs.ne' hNk.ne', Real.log_pow]
      linarith

end GlobalTheory.RunIn
