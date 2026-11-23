import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.PosSemidefWeightedInnerNonneg

noncomputable section

open Finset MeasureTheory
open scoped ComplexOrder

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

theorem psi_coef_expand (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (ξ ζ : Fin n → T.V) (g : Matrix (Fin n) (Fin n) ℂ) :
    ob2PsiCoef dual Ψ ξ ζ g = ∑ c, ∑ d, oa1Phi dual g c d * inner ℂ (ξ c) (Ψ g (ζ d)) := by
  simp only [ob2PsiCoef, inner_sum, inner_smul_right, oa1Phi]

section Psi

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

theorem continuous_spherical_psi (hP : IsPsiFor ε lam T Ψ) :
    Continuous (fun g : Formalism.REAL.UJ ε => Ψ (Formalism.MainNotions.S.umat g)) :=
  (ffa_continuousOn hP.2.2.1).comp_continuous continuous_umat' (fun g => g.2)

theorem psi_twist_coef_memLp (dual : Bool) (hP : IsPsiFor ε lam T Ψ)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) :
    MemLp (fun g : Formalism.REAL.UJ ε => ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := by
  simp_rw [psi_coef_expand]
  refine memLp_finsetSum _ fun c _ => memLp_finsetSum _ fun d _ => ?_
  refine (hWT (ζ d) (ξ c)).of_le ?_ (Filter.Eventually.of_forall fun g => ?_)
  · exact ((continuous_tensor_phi dual c d).mul (continuous_const.inner
      ((continuous_spherical_psi hP).clm_apply continuous_const))).aestronglyMeasurable
  · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right (norm_tensor_phi_le_sqrt_hs g.2 dual c d) (norm_nonneg _)

theorem psi_term_integrable (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε)) (ξ ζ : Fin n → T.V) (u v : T'.V) :
    Integrable (fun g : Formalism.REAL.UJ ε => starRingEnd ℂ (ob2PsiCoef dual Ψ ξ ζ (Formalism.MainNotions.S.umat g)) *
      inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) (Formalism.REAL.muG ε) := by
  have h1 := (psi_twist_coef_memLp dual hP hWT ξ ζ).star
  have h2 : MemLp (fun g : Formalism.REAL.UJ ε => inner ℂ u (Ψ' (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε) :=
    memLp_muG_of_haar ε (fun x => inner ℂ u (Ψ' x v)) 2
      (fun μ hμ => (pdA_coef u v).comp_memLp' (hP'.2.2.2.2 μ hμ))
  exact h1.integrable_mul h2

end Psi

theorem psi_twist_at_one (dual : Bool) {ε : Fin n → Bool} {Λ : Fin n → ℝ} {T : S7.KType ε Λ}
    (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)) (hΨ : Ψ 1 = 1) (u : Fin n → T.V) :
    ob2B dual Ψ 1 u = u := by
  funext c
  have hφ : ∀ d, oa1Phi dual 1 c d = if c = d then 1 else 0 := by
    intro d
    cases dual
    · simp [oa1Phi, Matrix.one_apply]
    · simp [oa1Phi, Matrix.one_apply, eq_comm]
  simp [ob2B, hφ, hΨ, ite_smul]

section Main

variable {ε : Fin n → Bool} {lam lam' : Fin n → ℝ} {T : S7.KType ε (lowK ε lam)} {T' : S7.KType ε (lowK ε lam')}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)} {Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)}

def ob2Fij (dual : Bool) (Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V))
    (Ψ' : Matrix (Fin n) (Fin n) ℂ → (T'.V →L[ℂ] T'.V)) (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V))
    (i j : Fin (Module.finrank ℂ T'.V)) (g : Formalism.REAL.UJ ε) : ℂ :=
  starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
    (Formalism.MainNotions.S.umat g)) *
  inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))

theorem psi_pairing_at_one_re_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0) :
    0 < (∑ i, ∑ j, ob2Fij (ε := ε) dual Ψ Ψ' ι₀ i j 1).re := by
  set b := stdOrthonormalBasis ℂ T'.V
  have e : (∑ i, ∑ j, ob2Fij (ε := ε) dual Ψ Ψ' ι₀ i j 1) =
      ∑ j, ob2SI (ob2B dual Ψ 1 (ι₀ (b j))) (ι₀ (Ψ' 1 (b j))) :=
    psi_pairing_eq_inner dual Ψ Ψ' ι₀ (1 : Matrix (Fin n) (Fin n) ℂ)
  rw [e]
  simp only [psi_twist_at_one dual Ψ hP.2.1, hP'.2.1, ContinuousLinearMap.one_apply]
  obtain ⟨j, hj⟩ : ∃ j, ι₀ (b j) ≠ 0 := by
    by_contra h
    push Not at h
    exact hι₀ (b.toBasis.ext fun j => by simpa using h j)
  obtain ⟨c, hc⟩ := Function.ne_iff.mp hj
  have key : ∀ x : T.V, (inner ℂ x x).re = ‖x‖ ^ 2 := fun x => inner_self_eq_norm_sq (𝕜 := ℂ) x
  simp only [ob2SI, Complex.re_sum, key]
  have hc' : ι₀ (b j) c ≠ 0 := by simpa using hc
  exact Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun c _ => by positivity)
    ⟨j, Finset.mem_univ _, Finset.sum_pos' (fun c _ => by positivity)
      ⟨c, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hc') 2⟩⟩

theorem continuous_psi_pairing_sum (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) :
    Continuous (fun g : Formalism.REAL.UJ ε => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) := by
  have h1 := continuous_spherical_psi hP
  have h2 := continuous_spherical_psi hP'
  have h3 := continuous_tensor_phi (ε := ε) dual
  simp only [ob2Fij, psi_coef_expand]
  exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    (Complex.continuous_conj.comp (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun d _ =>
      (h3 c d).mul (continuous_const.inner (h1.clm_apply continuous_const)))).mul
      (continuous_const.inner (h2.clm_apply continuous_const))

theorem psi_pairing_trace_pos (dual : Bool) (hP : IsPsiFor ε lam T Ψ) (hP' : IsPsiFor ε lam' T' Ψ')
    (hpos : ∀ X, inP ε X → (Ψ (NormedSpace.exp X)).IsPositive)
    (hpos' : ∀ X, inP ε X → (Ψ' (NormedSpace.exp X)).IsPositive)
    (hWT : ∀ v w : T.V, MemLp (fun g : Formalism.REAL.UJ ε => ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) *
      inner ℂ w (Ψ (Formalism.MainNotions.S.umat g) v)) 2 (Formalism.REAL.muG ε))
    (ι₀ : T'.V →ₗ[ℂ] (Fin n → T.V)) (hι₀ : ι₀ ≠ 0)
    (hK : ∀ (k : S7.KG ε) (v : T'.V), ι₀ (T'.op k v) = ob2TauF dual T k (ι₀ v)) :
    0 < (∑ i, ∑ j, ∫ g : Formalism.REAL.UJ ε,
      starRingEnd ℂ (ob2PsiCoef dual Ψ (ι₀ (stdOrthonormalBasis ℂ T'.V i)) (ι₀ (stdOrthonormalBasis ℂ T'.V j))
        (Formalism.MainNotions.S.umat g)) *
      inner ℂ (stdOrthonormalBasis ℂ T'.V i) (Ψ' (Formalism.MainNotions.S.umat g) (stdOrthonormalBasis ℂ T'.V j))
        ∂(Formalism.REAL.muG ε)).re := by
  show 0 < (∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε)).re
  have hint : ∀ i j, Integrable (ob2Fij dual Ψ Ψ' ι₀ i j) (Formalism.REAL.muG ε) := fun i j =>
    psi_term_integrable dual hP hP' hWT _ _ _ _
  have hFi : Integrable (fun g => ∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) (Formalism.REAL.muG ε) :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j
  have hsum : ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε) =
      ∑ i, ∑ j, ∫ g, ob2Fij dual Ψ Ψ' ι₀ i j g ∂(Formalism.REAL.muG ε) := by
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
  rw [← hsum]
  have hre : (∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g) ∂(Formalism.REAL.muG ε)).re =
      ∫ g, (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re ∂(Formalism.REAL.muG ε) :=
    (integral_re hFi).symm
  rw [hre]
  have hG0 : 0 ≤ fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re := by
    intro g
    have h := psi_pairing_nonneg dual hP hP' hpos hpos' ι₀ hK (g := Formalism.MainNotions.S.umat g) g.2
    have h' := (Complex.le_def.mp h).1
    rw [Complex.zero_re] at h'
    exact h'
  have hGc : Continuous fun g : Formalism.REAL.UJ ε => (∑ i, ∑ j, ob2Fij dual Ψ Ψ' ι₀ i j g).re :=
    Complex.continuous_re.comp (continuous_psi_pairing_sum dual hP hP' ι₀)
  rw [integral_pos_iff_support_of_nonneg hG0 hFi.re]
  exact hGc.isOpen_support.measure_pos _ ⟨1, Function.mem_support.mpr (psi_pairing_at_one_re_pos dual hP hP' ι₀ hι₀).ne'⟩

end Main

end ReciprocityTheory.ChartRestriction.DS
