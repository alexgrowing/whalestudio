import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.PeriodLatticeCountable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientsOfVectorGroup
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.UnipotentLatticeLift

namespace ReciprocityTheory.ChartRestriction.G.FD

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity
  ReciprocityTheory.ChartRestriction.G.FD.FundamentalDomainTranslate ReciprocityTheory.ChartRestriction.G.FD.PeriodLatticeCountable
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]

theorem norm_cexp_neg_four_pi_I_real (a : ℝ) : ‖cexp (-(4 * Real.pi * I) * (a : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp

theorem isHermFam_real_linear_comb {r : ℕ} (X : Data E r) (g N : ℕ) (ω : Fin N → X.Ψ → Fin 2 → Fin 2 → ℂ)
    (hω : ∀ j, ω j ∈ X.LZ g) (t : Fin N → ℝ) : IsHermFam (∑ j, (t j : ℂ) • ω j) := by
  intro τ i k
  have h : ∀ j, ω j τ k i = conj (ω j τ i k) := fun j => FourierCoefficientLattice.herm_of_LZ (X := X) (g := g) (hb := hω j) τ i k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul, Complex.conj_ofReal, h]

theorem fourier_coefficient_support_of (h3 : FourierCoefficientProperties (E := E)) (h2 : UnipotentLatticeLift (E := E)) :
    FourierCoefficientSupport (E := E) := by
  intro r X u hu hΛ la P hP hχ1 ν χ x hx
  classical
  have hiso : ∀ i k, herm X.Gm (u i) (u k) = 0 := hu.1
  have hu0 : herm X.Gm (u 0) (u 0) = 0 := hiso 0 0
  have hper : ∀ b ∈ X.LZ X.g, ∀ y ∈ X.dom, P (X.Zb u b y) = P y :=
    (h2 r X u hu hΛ).2.1 la P hP hχ1
  have hcov : ∀ b, IsHermFam b → ∀ y ∈ X.dom,
      X.fz u X.g χ P (X.Zb u b y) = cexp (4 * Real.pi * I * X.pairR χ b) * X.fz u X.g χ P y :=
    (h3 r X.toData u X.g hu X.g_pos la P hP.1 hP.2.1 hper χ).1.2.2
  by_cases hf : IsHermFam χ ∧ X.IsFreqZ X.g χ
  swap
  · have e : ∀ G, X.fz u X.g χ G x = 0 := fun G => by simp only [Data.fz, if_neg hf]
    rw [e, e]
    split_ifs <;> rfl
  by_cases hb : ∃ ω, X.IsLZBasis X.g ω
  swap
  · have e : ∀ G, X.fz u X.g χ G x = 0 := fun G => by simp only [Data.fz, if_pos hf, dif_neg hb]
    rw [e, e]
    split_ifs <;> rfl
  set ω := hb.choose with hωdef
  have hωLZ : ∀ j, ω j ∈ X.LZ X.g := hb.choose_spec.1
  set C : Set (Fin (4 * Fintype.card X.Ψ) → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) with hC
  set B : (Fin (4 * Fintype.card X.Ψ) → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ := fun t => ∑ j, (t j : ℂ) • ω j with hB
  have hBh : ∀ t, IsHermFam (B t) := fun t => isHermFam_real_linear_comb X.toData X.g _ ω hωLZ t
  have hfz : ∀ (G : Frame X.Ψ r → ℂ) y, X.fz u X.g χ G y =
      ∫ t in C, G (X.Zb u (B t) y) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) := by
    intro G y
    simp only [Data.fz, if_pos hf, dif_pos hb]
    rfl
  set χr : X.Ψ → ℝ := fun τ => (χ τ 0 0).re with hχrdef
  have hflowcov : ∀ (s : X.Ψ → ℝ), ∀ y ∈ X.dom,
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) y) =
        cexp (4 * Real.pi * I * ((∑ τ, χr τ * s τ : ℝ) : ℂ)) * X.fz u X.g χ P y := by
    intro s y hy
    rw [flow_eq_Zb X.toData u s y, hcov _ (diag_unit_family_hermitian X.toData s) y hy, real_pairing_diag_unit]
  have hpinv : ∀ p ∈ X.periods la,
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData p) x) = X.fz u X.g χ P x := by
    intro p hp
    rw [hfz, hfz]
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ => measurableSet_Icc) fun t _ => ?_
    rw [← flow_Zb_comm X.toData u hiso,
      sec_periodic X.toData la P hP (hΛ 0) hu0 hp _ (Data.Zb_dom X.toData u hiso _ (hBh t) hx)]
  have hfreq : X.fz u X.g χ P x ≠ 0 → ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, χr τ * p τ = k := by
    intro hne p hp
    have h1 := hflowcov p x hx
    rw [hpinv p hp] at h1
    have h2 : cexp (4 * Real.pi * I * ((∑ τ, χr τ * p τ : ℝ) : ℂ)) = 1 :=
      mul_right_cancel₀ hne (h1.symm.trans (one_mul _).symm)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨n, ?_⟩
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    have h3' : ((2 * ∑ τ, χr τ * p τ : ℝ) : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ hpi
      push_cast at hn ⊢
      linear_combination hn
    exact_mod_cast h3'
  have hcond : (∀ τ, χ τ 0 0 = (ν τ : ℂ)) ↔ χr = ν := by
    constructor
    · intro h
      funext τ
      simpa [hχrdef] using congrArg Complex.re (h τ)
    · intro h τ
      have h1 : χ τ 0 0 = ((χ τ 0 0).re : ℂ) :=
        (Complex.conj_eq_iff_re.1 (hf.1 τ 0 0).symm).symm
      rw [h1]
      exact congrArg (fun z : ℝ => (z : ℂ)) (congrFun h τ)
  by_cases hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k
  swap
  · have hfj0 : X.fj la (u 0) ν P = fun _ => 0 := by
      funext y
      simp only [Data.fj, if_neg hν]
    have hL : X.fz u X.g χ (X.fj la (u 0) ν P) x = 0 := by
      rw [hfj0, hfz]
      simp
    rw [hL]
    split_ifs with hc
    · by_contra hne
      apply hν
      intro p hp
      have hr := hcond.1 hc
      obtain ⟨k, hk⟩ := hfreq (fun h => hne h.symm) p hp
      exact ⟨k, by rw [← hr]; exact hk⟩
    · rfl

  have hDe := fd_exists X.toData la
  set D := hDe.choose with hDdef
  obtain ⟨hDm, hDfd, hDpos, hDfin⟩ := hDe.choose_spec
  have hfj : ∀ y, X.fj la (u 0) ν P y = ((volume D).toReal : ℂ)⁻¹ *
      ∫ s in D, P (X.flow (u 0) (cR X.toData s) y) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) := by
    intro y
    simp only [Data.fj, if_pos hν, dif_pos hDe]
    rfl
  have hCm : MeasurableSet C := MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hCc : IsCompact C := isCompact_univ_pi fun _ => isCompact_Icc

  set F : (Fin (4 * Fintype.card X.Ψ) → ℝ) → (X.Ψ → ℝ) → ℂ := fun t s =>
    P (X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x)) *
      cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) with hF
  have hherm_add : ∀ a b : X.Ψ → Fin 2 → Fin 2 → ℂ, IsHermFam a → IsHermFam b → IsHermFam (a + b) := by
    intro a b ha hb' τ i k
    simp only [Pi.add_apply, map_add, ha τ i k, hb' τ i k]
  have hflowZ : ∀ (s : X.Ψ → ℝ) t, X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x) =
      X.Zb u (e00 X.toData s + B t) x := by
    intro s t
    rw [flow_eq_Zb, Data.Zb_Zb X.toData u hiso]
  have hdom : ∀ (s : X.Ψ → ℝ) t, X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x) ∈ X.dom := by
    intro s t
    rw [hflowZ]
    exact Data.Zb_dom X.toData u hiso _ (hherm_add _ _ (diag_unit_family_hermitian X.toData s) (hBh t)) hx
  have he00c : Continuous (e00 X.toData) := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun k => ?_
    simp only [e00]
    split_ifs
    · fun_prop
    · exact continuous_const
  have hBc : Continuous B := by
    simp only [hB]
    fun_prop
  have hPc : Continuous fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) =>
      P (X.flow (u 0) (cR X.toData q.2) (X.Zb u (B q.1) x)) := by
    have e : (fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) =>
        P (X.flow (u 0) (cR X.toData q.2) (X.Zb u (B q.1) x))) =
        fun q => P (X.Zb u (e00 X.toData q.2 + B q.1) x) := by
      funext q
      rw [hflowZ]
    rw [e]
    refine hP.1.continuousOn.comp_continuous ((Zb_cont X.toData u x).comp ?_) fun q => ?_
    · exact (he00c.comp continuous_snd).add (hBc.comp continuous_fst)
    · exact Data.Zb_dom X.toData u hiso _ (hherm_add _ _ (diag_unit_family_hermitian X.toData q.2) (hBh q.1)) hx
  have hFc : Continuous (Function.uncurry F) := by
    simp only [hF, Function.uncurry_def]
    refine (hPc.mul ?_).mul ?_
    · fun_prop
    · have : Continuous fun q : (Fin (4 * Fintype.card X.Ψ) → ℝ) × (X.Ψ → ℝ) => X.pairR χ (B q.1) := by
        simp only [Data.pairR]
        fun_prop
      fun_prop

  obtain ⟨K, hK, hKrep⟩ := compact_reps X.toData la
  obtain ⟨M, hM⟩ := (hK.prod hCc).exists_bound_of_continuousOn
    ((continuous_norm.comp (hPc.comp (continuous_snd.prodMk continuous_fst))).continuousOn)
  have hbound : ∀ t ∈ C, ∀ s, ‖F t s‖ ≤ M := by
    intro t ht s
    obtain ⟨p, hp, hsp⟩ := hKrep s
    have hy : X.Zb u (B t) x ∈ X.dom := Data.Zb_dom X.toData u hiso _ (hBh t) hx
    have hPs : P (X.flow (u 0) (cR X.toData s) (X.Zb u (B t) x)) =
        P (X.flow (u 0) (cR X.toData (s - p)) (X.Zb u (B t) x)) := by
      have e1 : cR X.toData s = cR X.toData p + cR X.toData (s - p) := by
        rw [← cR_add]
        congr 1
        abel
      rw [e1, ← flow_flow X.toData hu0,
        sec_periodic X.toData la P hP (hΛ 0) hu0 hp _ (flow_real_mem_dom X.toData hu0 _ _ hy)]
    have h1 := hM (s - p, t) ⟨hsp, ht⟩
    simp only [Function.comp, norm_norm] at h1
    simp only [hF, norm_mul, Complex.norm_exp]
    rw [hPs]
    have h2 : (-(4 * (Real.pi : ℂ) * I) * ∑ τ, (ν τ : ℂ) * (s τ : ℂ)).re = 0 := by simp
    have h3 : (-(4 * (Real.pi : ℂ) * I) * (X.pairR χ (B t) : ℂ)).re = 0 := by simp
    rw [h2, h3, Real.exp_zero, mul_one, mul_one]
    exact h1
  have hfinC : volume C < ⊤ := hCc.measure_lt_top
  have hint : Integrable (Function.uncurry F) ((volume.restrict C).prod (volume.restrict D)) := by
    rw [Measure.prod_restrict]
    have : IsFiniteMeasure ((volume.prod volume).restrict (C ×ˢ D)) := by
      refine isFiniteMeasure_restrict.2 ?_
      rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top hfinC.ne hDfin.ne
    refine (integrable_const M).mono' hFc.aestronglyMeasurable ?_
    refine (ae_restrict_mem (hCm.prod hDm)).mono fun q hq => ?_
    exact hbound q.1 hq.1 q.2

  rw [hfz]
  have e1 : ∀ t, X.fj la (u 0) ν P (X.Zb u (B t) x) * cexp (-(4 * Real.pi * I) * X.pairR χ (B t)) =
      ((volume D).toReal : ℂ)⁻¹ * ∫ s in D, F t s := by
    intro t
    rw [hfj, mul_assoc, ← integral_mul_const]
  simp_rw [e1]
  rw [integral_const_mul, integral_integral_swap hint]
  have e2 : ∀ s, ∫ t in C, F t s = cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) *
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) x) := by
    intro s
    rw [hfz, ← integral_const_mul]
    refine setIntegral_congr_fun hCm fun t _ => ?_
    simp only [hF]
    rw [flow_Zb_comm X.toData u hiso]
    ring
  simp_rw [e2]
  have e3 : ∀ s : X.Ψ → ℝ, cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) *
      X.fz u X.g χ P (X.flow (u 0) (cR X.toData s) x) =
      X.fz u X.g χ P x * cexp (4 * Real.pi * I * ∑ τ, (((χr - ν) τ : ℝ) : ℂ) * s τ) := by
    intro s
    rw [hflowcov s x hx, mul_left_comm, ← mul_assoc, ← Complex.exp_add, mul_comm]
    congr 2
    simp only [Pi.sub_apply]
    push_cast
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  simp_rw [e3]
  rw [integral_const_mul]
  by_cases h0 : X.fz u X.g χ P x = 0
  · rw [h0]
    simp
  have hμ : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, (χr - ν) τ * p τ = k := by
    intro p hp
    obtain ⟨k1, hk1⟩ := hfreq h0 p hp
    obtain ⟨k2, hk2⟩ := hν p hp
    refine ⟨k1 - k2, ?_⟩
    simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, mul_sub]
    push_cast
    rw [hk1, hk2]
  rw [orth (X.periods la) D hDfd (χr - ν) hμ]
  have hvD : ((volume D).toReal : ℂ) ≠ 0 := by
    have : 0 < (volume D).toReal := ENNReal.toReal_pos hDpos.ne' hDfin.ne
    exact_mod_cast this.ne'
  by_cases hc : χr = ν
  · rw [if_pos (sub_eq_zero.2 hc), if_pos (hcond.2 hc)]
    field_simp
  · rw [if_neg (fun h => hc (sub_eq_zero.1 h)), if_neg (fun h => hc (hcond.1 h))]
    simp

theorem fourier_coefficient_support_holds : FourierCoefficientSupport (E := E) := fourier_coefficient_support_of fourier_coefficients_holds unipotent_lattice_lift

end ReciprocityTheory.ChartRestriction.G.FD
