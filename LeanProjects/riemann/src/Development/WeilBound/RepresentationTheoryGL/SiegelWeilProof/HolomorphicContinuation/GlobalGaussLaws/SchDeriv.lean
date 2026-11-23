import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.NormIterFstComp
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DerivationOfQuadraticForm

noncomputable section

open Filter Topology Set
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.Glob

open SchDH

theorem schDeriv : SchDeriv := by
  intro m n c hc X P
  obtain ⟨φ0, hφ0⟩ := exists_fP (m := m) (n := n) c hc P
  obtain ⟨φ1, hφ1⟩ := exists_fP (m := m) (n := n) c hc (vfX c X P)
  set A : ℝ → (Fin m → Fin n → ℂ) →L[ℝ] (Fin m → Fin n → ℂ) :=
    fun t => matL (NormedSpace.exp ((t : ℂ) • X)) with hAdef
  have hA : ContDiff ℝ ∞ A := contDiff_A X
  have hinv : ∀ t y, A (-t) (A t y) = y := by
    intro t y
    simp only [hAdef]
    rw [← matL_mul, ← Matrix.exp_add_of_commute _ _ (((Commute.refl X).smul_left _).smul_right _)]
    rw [← add_smul, Complex.ofReal_neg, neg_add_cancel, zero_smul, NormedSpace.exp_zero, matL_one]
  let Aeq : ℝ → (Fin m → Fin n → ℂ) ≃L[ℝ] (Fin m → Fin n → ℂ) := fun t =>
    ContinuousLinearEquiv.equivOfInverse (A t) (A (-t)) (fun y => hinv t y)
      (fun y => by have h := hinv (-t) y; rwa [neg_neg] at h)
  have hAeq : ∀ t y, Aeq t y = A t y := fun t y => rfl
  let S : ℝ → SchwartzMap (Fin m → Fin n → ℂ) ℂ := fun t => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (Aeq t) φ0
  have hS : ∀ t y, S t y = φ0 (A t y) := fun t y => by
    simp only [S, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hAeq]
  refine ⟨S, φ1, fun t y => ?_, fun y => hφ1 y, ?_⟩
  · rw [hS, hφ0]
    congr 1
  · set F : ℝ × (Fin m → Fin n → ℂ) → ℂ := fun q => φ0 (A q.1 q.2) with hFdef
    have hF : ContDiff ℝ ∞ F := (φ0.smooth ⊤).comp ((hA.comp contDiff_fst).clm_apply contDiff_snd)
    have hR : ∀ p, ⇑(S p) = fun x => F (p, x) := fun p => by funext x; rw [hS]
    have hder : ∀ x, HasDerivAt (fun t : ℝ => F (t, x)) (φ1 x) 0 := fun x => by
      have h := hasDerivAt_curve c X P x
      rw [hφ1]
      have e : (fun t : ℝ => F (t, x)) = fun t : ℝ => fP c P (matL (NormedSpace.exp ((t : ℂ) • X)) x) := by
        funext t; simp only [hFdef, hAdef, hφ0]
      rw [e]; exact h
    have hD : ∀ v : ℝ, ⇑(v • φ1) = fun x => fderiv ℝ F ((0 : ℝ), x) (v, 0) := by
      intro v
      funext x
      have hFd : HasFDerivAt F (fderiv ℝ F ((0 : ℝ), x)) ((0 : ℝ), x) :=
        ((hF.differentiable (by simp)) _).hasFDerivAt
      have hc : HasDerivAt (fun t : ℝ => ((t, x) : ℝ × (Fin m → Fin n → ℂ))) ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) 0 :=
        (hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x)
      have h1 := hFd.comp_hasDerivAt (0 : ℝ) hc
      have h2 := (hder x).unique h1
      have e : ((v, 0) : ℝ × (Fin m → Fin n → ℂ)) = v • ((1 : ℝ), (0 : Fin m → Fin n → ℂ)) := by
        ext <;> simp
      rw [SchwartzMap.smul_apply, e, map_smul]
      change v • φ1 x = v • (fderiv ℝ F ((0 : ℝ), x)) ((1 : ℝ), (0 : Fin m → Fin n → ℂ))
      rw [h2]
    have hb : ∀ k N : ℕ, ∃ C, ∀ p : ℝ, ‖p - 0‖ ≤ 1 → ∀ x : Fin m → Fin n → ℂ,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ N F (p, x)‖ ≤ C := fun k N => bound_comp φ0 A hA hinv k N
    rw [(schwartz_withSeminorms ℂ (Fin m → Fin n → ℂ) ℂ).tendsto_nhds]
    rintro ⟨k, N⟩ ε hε
    obtain ⟨C, hC⟩ := GlobalTheory.CompanionTheory.OM.SchDiff.seminorm_remainder hF (0 : ℝ) hb S (fun v => v • φ1) hR hD k N
    set C' := max C 1 with hC'
    have hC'0 : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < min 1 (ε / C') := by
      have h := (continuous_abs.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))
      rw [abs_zero] at h
      exact h (Iio_mem_nhds (lt_min one_pos (div_pos hε hC'0)))
    filter_upwards [hev, self_mem_nhdsWithin] with t ht htne
    have htne' : t ≠ 0 := htne
    have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs]; exact (lt_of_lt_of_le ht (min_le_left _ _)).le
    have key : t⁻¹ • (S t - S 0) - φ1 = ((t⁻¹ : ℝ) : ℂ) • (S (0 + t) - S 0 - t • φ1) := by
      rw [Complex.coe_smul, zero_add]
      simp only [smul_sub, smul_smul, inv_mul_cancel₀ htne', one_smul]
    change SchwartzMap.seminorm ℂ k N (t⁻¹ • (S t - S 0) - φ1) < ε
    rw [key, map_smul_eq_mul, Complex.norm_real, norm_inv]
    have hCt := hC t ht1
    have hpos : 0 < ‖t‖ := norm_pos_iff.2 htne'
    calc ‖t‖⁻¹ * (SchwartzMap.seminorm ℂ k N) (S (0 + t) - S 0 - t • φ1)
        ≤ ‖t‖⁻¹ * (C * ‖t‖ ^ 2) := by gcongr
      _ = C * ‖t‖ := by field_simp
      _ ≤ C' * ‖t‖ := by gcongr; exact le_max_left _ _
      _ < C' * (ε / C') := by
          gcongr
          rw [Real.norm_eq_abs]; exact lt_of_lt_of_le ht (min_le_right _ _)
      _ = ε := by field_simp

end PositivityTheory.Rg.Sw.Glob
