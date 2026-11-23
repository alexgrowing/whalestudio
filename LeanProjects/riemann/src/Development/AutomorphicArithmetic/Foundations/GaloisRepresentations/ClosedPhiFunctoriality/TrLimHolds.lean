import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ClosedPhiFunctoriality.IntBasisAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFrobeniusMatrixEqZeroOfDvd
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong GlobalTheory.WeilDeligne Matrix
open scoped Formalism.Per NNReal
open UpperTheory.Gal.ClosedPhiFromClosedTrace

theorem UpperTheory.Gal.ClosedPhiFromClosedTrace.trLim_holds :
    TrStep → TrLim := by
  intro hstep l _ P AI T K bk Γ _ _ L₀ a r Cl Cv s V V' p θ pv hs hV hV' hlink hθ
  by_contra hne
  have hpθ : p - θ ≠ 0 := sub_ne_zero.mpr hne
  have hl1 : (1 : ℝ) < (l : ℝ) := by exact_mod_cast (Fact.out : l.Prime).one_lt
  have hl0 : (0 : ℝ) < (l : ℝ) := by linarith
  have hlnorm : ‖(l : Om l)‖ = (l : ℝ)⁻¹ := by
    have h := PadicAlgCl.norm_extends l ((l : ℚ_[l]))
    rw [Padic.norm_p] at h
    simpa using h
  have hnp : ∀ (c : ℕ) (x : Om l), ‖(l : Om l) ^ c * x‖ = ((l : ℝ) ^ c)⁻¹ * ‖x‖ := by
    intro c x
    rw [norm_mul, norm_pow, hlnorm, inv_pow]
  obtain ⟨c₁, hc₁⟩ := pow_unbounded_of_one_lt (‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖) hl1
  have hsmall : ∀ x : Om l, ‖x‖ ≤ ‖p - θ‖ + ∑ i, ‖(Cv.b i).trace‖ → ‖(l : Om l) ^ c₁ * x‖ ≤ 1 := by
    intro x hx
    rw [hnp, inv_mul_le_iff₀ (pow_pos hl0 c₁), mul_one]
    exact hx.trans hc₁.le
  have hsum0 : 0 ≤ ∑ i, ‖(Cv.b i).trace‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have ht : ∀ i, ‖(l : Om l) ^ c₁ * (Cv.b i).trace‖ ≤ 1 := fun i =>
    hsmall _ (((Finset.single_le_sum (f := fun i => ‖(Cv.b i).trace‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ i))).trans
      (le_add_of_nonneg_left (norm_nonneg _)))
  have hd : ‖(l : Om l) ^ c₁ * (p - θ)‖ ≤ 1 := hsmall _ (le_add_of_nonneg_right hsum0)
  have hpos : 0 < ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [hnp]
    exact mul_pos (inv_pos.mpr (pow_pos hl0 c₁)) (norm_pos_iff.mpr hpθ)
  obtain ⟨c₂, hc₂⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl1)
  have hc₂' : ((l : ℝ) ^ c₂)⁻¹ ≤ ‖(l : Om l) ^ c₁ * (p - θ)‖ := by
    rw [← inv_pow]
    exact hc₂.le
  have hdvd : ∀ M : ℕ, (l : Per.Acris l) ^ M ∣ (l : Per.Acris l) ^ c₂ * s := by
    intro M
    obtain ⟨m, hMm, hm⟩ := hlink M
    have hle : ((l : ℝ) ^ m)⁻¹ ≤ ((l : ℝ) ^ M)⁻¹ :=
      inv_anti₀ (pow_pos hl0 M) (pow_le_pow_right₀ hl1.le hMm)
    refine hstep l P AI T s Cv.d (Cv.tw.d' m) (Cv.lay m).m M c₁ c₂ (fun i => (Cv.b i).trace)
      (fun j k => ((Cv.lay m).b j k).trace) (Cv.lay m).c (pv m) p θ (Cv.tw.Pi m) Cv.e (Cv.lay m).e V (V' m)
      hV (hV' m) hm (fun i => (pow_dvd_pow _ hMm).trans (Cv.unit m i)) (fun j => ?_) ((hθ m).trans hle) ht hd hc₂'
    have h := Cv.trace m j
    rw [Matrix.trace_sum] at h
    simp only [Matrix.trace_smul, smul_eq_mul] at h
    exact h.trans hle
  obtain ⟨htor, hcomp, -⟩ := GlobalTheory.T.acris_torsionFree_complete_frobenius_properties l K bk
  have hz := GlobalTheory.CrZero.eq_zero_of_forall_dvd _ hcomp.toIsHausdorff _ hdvd
  have hs0 : s = 0 := GlobalTheory.CrZero.pow_cancel (l : Per.Acris l) htor c₂ s 0 (by simpa using hz)
  haveI : Nontrivial P.R.B := GlobalTheory.Pst.nontrivial_B P
  haveI : Nontrivial (Per.Bcris l) := T.eB.injective.nontrivial
  rw [hs0, map_zero] at hs
  exact not_isUnit_zero hs
