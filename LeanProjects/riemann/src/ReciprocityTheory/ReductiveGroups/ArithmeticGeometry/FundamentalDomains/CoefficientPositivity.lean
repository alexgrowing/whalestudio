import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.LatticeMinorExistence
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ExponentialGrowthExclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.HolomorphicPeriodicityExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.M3bNormHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos

namespace ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity

open NumberField Complex MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.LatticeMinorExistence
  ReciprocityTheory.ChartRestriction.G.FD.ExponentialGrowthExclusion
open scoped ComplexConjugate ComplexOrder

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

lemma chiAt_nonneg (X : Data E r) (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (F : Frame X.Ψ r → ℂ) (hF : DifferentiableOn ℂ F X.dom)
    (hZ : ∀ b, IsHermFam b → ∀ x ∈ X.dom, F (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * F x)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la F y ≤ C) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hF0 : F x0 ≠ 0) (a : X.Ψ → Fin 2 → ℂ) (ha : ∀ τ, a τ ≠ 0) (τ0 : X.Ψ) :
    0 ≤ (X.chiAt χ a τ0).re := by
  classical
  by_contra hneg
  push_neg at hneg
  have he : X.IsIsoV (X.uvec u a) := isIsoV_uvec (X := X) hu ha
  have hreal : ∀ s : X.Ψ → ℝ, F (X.flowV (X.uvec u a) (fun τ => (s τ : ℂ)) x0) =
      cexp (4 * Real.pi * I * ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ) * F x0 := by
    intro s
    rw [Data.flowV_uvec (X := X), hZ _ (herm_rank1 X s a) x0 hx0, pairR_rank1]
    congr 3
    push_cast
    exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  have hcont := holomorphic_periodicity_extension r X (X.uvec u a) he F hF (fun τ => ((X.chiAt χ a τ).re : ℂ)) x0 hx0 hreal
  obtain ⟨T, hT_eq⟩ : ∃ T, T = X.ttV (X.uvec u a) x0 τ0 := ⟨_, rfl⟩
  have hT : 0 < T := by
    rw [hT_eq, Data.ttV]
    exact one_div_pos.2 (mul_pos (d4l4_c_pos X τ0) (Data.maj_pos (X := X) hx0 τ0 (he τ0).2))
  obtain ⟨b, hb_eq⟩ : ∃ b : ℝ, b = -(4 * Real.pi * (X.chiAt χ a τ0).re * T) := ⟨_, rfl⟩
  have hb : 0 < b := by
    have h1 := mul_pos (mul_pos (mul_pos four_pos Real.pi_pos) (neg_pos.2 hneg)) hT
    rw [hb_eq]
    linarith
  have hK : 0 < ‖F x0‖ * X.nfac la x0 := mul_pos (norm_pos_iff.2 hF0) (BoundedSectionAlgebra.nfac_pos (X := X) hx0 la)

  obtain ⟨y, hyM, hy1⟩ := (((tendsto_exp_mul_div_rpow_atTop (X.spread la τ0 / 2) b hb).eventually_gt_atTop
    (C / (‖F x0‖ * X.nfac la x0 * Real.exp (-b)))).and (Filter.eventually_ge_atTop 1)).exists
  obtain ⟨t, ht_eq⟩ : ∃ t : ℝ, t = T * (y - 1) := ⟨_, rfl⟩
  let s : X.Ψ → ℂ := Function.update 0 τ0 (I * t)
  have hs0 : s τ0 = I * t := by simp [s]
  have hsne : ∀ τ, τ ≠ τ0 → s τ = 0 := fun τ h => by simp [s, h]
  have hq : ∀ τ, 1 + (s τ).im / X.ttV (X.uvec u a) x0 τ = if τ = τ0 then y else 1 := by
    intro τ
    split_ifs with h
    · rw [h, hs0, ← hT_eq, ht_eq]
      simp only [Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, one_mul, zero_add]
      field_simp
      ring
    · rw [hsne τ h]
      simp
  have hdom : X.flowV (X.uvec u a) s x0 ∈ X.dom := by
    refine ((flowDomainCriterion_holds r X (X.uvec u a) he x0 hx0 s).1).2 fun τ => ?_
    rw [hq τ]
    split_ifs <;> linarith
  have hsum : ∑ τ, ((X.chiAt χ a τ).re : ℂ) * s τ = ((X.chiAt χ a τ0).re : ℂ) * (I * t) := by
    rw [Finset.sum_eq_single τ0 (fun τ _ h => by rw [hsne τ h, mul_zero])
      (fun h => absurd (Finset.mem_univ τ0) h), hs0]
  have hnormF : ‖F (X.flowV (X.uvec u a) s x0)‖ = Real.exp (b * (y - 1)) * ‖F x0‖ := by
    rw [hcont s hdom, hsum, norm_mul]
    congr 1
    have h1 : 4 * (Real.pi : ℂ) * I * (((X.chiAt χ a τ0).re : ℂ) * (I * t)) =
        ((b * (y - 1) : ℝ) : ℂ) := by
      rw [hb_eq, ht_eq]
      push_cast
      linear_combination (4 * (Real.pi : ℂ) * ((X.chiAt χ a τ0).re : ℂ) * T * (y - 1)) * Complex.I_sq
    rw [h1, Complex.norm_exp_ofReal]
  have hN := (m3bNorm_holds r X (X.uvec u a) he la x0 hx0 s hdom).2
  simp only [hq] at hN
  have hprod : ∏ τ, max (if τ = τ0 then y else 1) (if τ = τ0 then y else 1)⁻¹ ^ (X.spread la τ / 2) =
      y ^ (X.spread la τ0 / 2) := by
    rw [Finset.prod_eq_single τ0 (fun τ _ h => by simp [h]) (fun h => absurd (Finset.mem_univ τ0) h)]
    rw [if_pos rfl, max_eq_left ((inv_le_one_of_one_le₀ hy1).trans hy1)]
  rw [hprod] at hN
  have hY := BoundedSectionAlgebra.nfac_pos (X := X) hdom la
  have hypos : 0 < y ^ (X.spread la τ0 / 2) := Real.rpow_pos_of_pos (by linarith) _
  have hnf : X.nfac la x0 / y ^ (X.spread la τ0 / 2) ≤ X.nfac la (X.flowV (X.uvec u a) s x0) := by
    rw [div_le_iff₀ hY] at hN
    rw [div_le_iff₀ hypos]
    linarith [mul_comm (y ^ (X.spread la τ0 / 2)) (X.nfac la (X.flowV (X.uvec u a) s x0))]
  have hC' := hC _ hdom
  rw [BoundedSectionAlgebra.pnorm_eq (X := X), hnormF] at hC'
  have key : ‖F x0‖ * X.nfac la x0 * Real.exp (-b) *
      (Real.exp (b * y) / y ^ (X.spread la τ0 / 2)) ≤ C := by
    calc _ = Real.exp (b * (y - 1)) * ‖F x0‖ * (X.nfac la x0 / y ^ (X.spread la τ0 / 2)) := by
          rw [show b * (y - 1) = b * y + -b by ring, Real.exp_add]
          ring
      _ ≤ Real.exp (b * (y - 1)) * ‖F x0‖ * X.nfac la (X.flowV (X.uvec u a) s x0) :=
          mul_le_mul_of_nonneg_left hnf (by positivity)
      _ ≤ C := hC'
  rw [div_lt_iff₀ (mul_pos hK (Real.exp_pos _))] at hyM
  linarith

lemma psd_of (X : Data E r) (u : Fin 2 → Fin r → E) (hu : IsIsoPair X.Gm u) (la : Wt X.Ψ r)
    (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hχ : IsHermFam χ) (F : Frame X.Ψ r → ℂ)
    (hF : DifferentiableOn ℂ F X.dom)
    (hZ : ∀ b, IsHermFam b → ∀ x ∈ X.dom, F (X.Zb u b x) = cexp (4 * Real.pi * I * X.pairR χ b) * F x)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la F y ≤ C) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hF0 : F x0 ≠ 0) (τ0 : X.Ψ) : (Matrix.of (χ τ0)).PosSemidef := by
  refine posSemidef_of (X := X) hχ τ0 (fun x hx => ?_)
  have ha : ∀ τ : X.Ψ, (fun i => conj (x i)) ≠ 0 := by
    intro τ h
    apply hx
    funext i
    have h1 := congrFun h i
    simpa using h1
  have h2 := chiAt_nonneg X u hu la χ F hF hZ C hC hx0 hF0 (fun _ i => conj (x i)) ha τ0
  simpa [Data.chiAt, mul_comm, mul_left_comm, mul_assoc] using h2

lemma flow_eq_Zb (X : Data E r) (u : Fin 2 → Fin r → E) (ξ : Fin r → E) (a : X.Ψ → Fin 2 → ℂ)
    (hemb : ∀ τ : X.Ψ, Data.emb τ.1 ξ = X.uvec u a τ) (s : X.Ψ → ℝ) (y : Frame X.Ψ r) :
    X.flow ξ (fun τ => (s τ : ℂ)) y = X.Zb u (fun τ i k => (s τ : ℂ) * a τ i * conj (a τ k)) y := by
  have h1 : X.flow ξ (fun τ => (s τ : ℂ)) y = X.flowV (X.uvec u a) (fun τ => (s τ : ℂ)) y := by
    funext τ
    simp only [Data.flow, Data.flowV]
    congr 1
    rw [← hemb τ]
    ext i j
    simp [Data.flowMat, Data.flowMatV, Data.emb]
  rw [h1, X.flowV_uvec]

lemma fz_zero_of_inv (X : Data E r) (u : Fin 2 → Fin r → E) (hu : ∀ i k, herm X.Gm (u i) (u k) = 0)
    (g : ℕ) (χ : X.Ψ → Fin 2 → Fin 2 → ℂ) (hcond : IsHermFam χ ∧ X.IsFreqZ g χ)
    (hωex : ∃ ω, X.IsLZBasis g ω) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hPc : ContinuousOn P X.dom)
    (C : ℝ) (hC : ∀ y ∈ X.dom, X.pnorm la P y ≤ C) (ξ : Fin r → E) (hξ : herm X.Gm ξ ξ = 0)
    (a : X.Ψ → Fin 2 → ℂ) (hemb : ∀ τ : X.Ψ, Data.emb τ.1 ξ = X.uvec u a τ)
    (hcusp : ∀ y ∈ X.dom, X.fj la ξ 0 P y = 0) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom)
    (hinv : ∀ s : X.Ψ → ℝ, X.fz u g χ P (X.flow ξ (fun τ => (s τ : ℂ)) x0) = X.fz u g χ P x0) :
    X.fz u g χ P x0 = 0 := by
  classical
  obtain ⟨-, -, hfd_pos, hfd_top⟩ := (exists_fd X la).choose_spec
  have hωH : ∀ j, IsHermFam (hωex.choose j) := fun j => herm_of_LZ (X := X) (hωex.choose_spec.1 j)
  let K : Set (Fin (4 * Fintype.card X.Ψ) → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1
  let B : (Fin (4 * Fintype.card X.Ψ) → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ :=
    fun t => ∑ j, (t j : ℂ) • hωex.choose j
  let R : (X.Ψ → ℝ) → X.Ψ → Fin 2 → Fin 2 → ℂ := fun s τ i k => (s τ : ℂ) * a τ i * conj (a τ k)
  let e : (Fin (4 * Fintype.card X.Ψ) → ℝ) → ℂ := fun t => cexp (-(4 * Real.pi * I) * X.pairR χ (B t))
  have hfz : ∀ y, X.fz u g χ P y = ∫ t in K, P (X.Zb u (B t) y) * e t := by
    intro y
    simp only [Data.fz, if_pos hcond, dif_pos hωex]
    rfl
  have hHerm : ∀ s t, IsHermFam (B t + R s) := by
    intro s t τ i k
    have h1 := herm_comb (X := X) hωH t τ i k
    have h2 := herm_rank1 X s a τ i k
    simp only at h2
    show (B t + R s) τ k i = conj ((B t + R s) τ i k)
    simp only [Pi.add_apply, B, R, map_add, h1, h2]
  have hdom : ∀ s t, X.Zb u (B t + R s) x0 ∈ X.dom := fun s t => X.Zb_dom u hu _ (hHerm s t) hx0
  have hN0 := BoundedSectionAlgebra.nfac_pos (X := X) hx0 la
  have hbdP : ∀ s t, ‖P (X.Zb u (B t + R s) x0)‖ ≤ C / X.nfac la x0 := by
    intro s t
    have h1 := hC _ (hdom s t)
    rw [BoundedSectionAlgebra.pnorm_eq (X := X), X.nfac_Zb u hu _ (hHerm s t) la x0] at h1
    rw [le_div_iff₀ hN0]
    exact h1
  have he1 : ∀ t, ‖e t‖ = 1 := by
    intro t
    simp only [e]
    rw [show -(4 * (Real.pi : ℂ) * I) * (X.pairR χ (B t) : ℂ) =
      ((-(4 * Real.pi * X.pairR χ (B t)) : ℝ) : ℂ) * I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hZc : Continuous fun b : X.Ψ → Fin 2 → Fin 2 → ℂ => X.Zb u b x0 := by
    refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Data.Zb, Data.zmat, mat, Matrix.mul_apply, Matrix.of_apply]
    fun_prop
  have hBc : Continuous B := by
    simp only [B]
    fun_prop
  have hRc : Continuous R := by
    simp only [R]
    fun_prop
  have hec : Continuous e := by
    simp only [e, B, Data.pairR]
    fun_prop
  let f : (X.Ψ → ℝ) → (Fin (4 * Fintype.card X.Ψ) → ℝ) → ℂ := fun s t => P (X.Zb u (B t + R s) x0) * e t
  have hfc : Continuous (Function.uncurry f) := by
    have h1 : Continuous fun p : (X.Ψ → ℝ) × (Fin (4 * Fintype.card X.Ψ) → ℝ) =>
        P (X.Zb u (B p.2 + R p.1) x0) :=
      hPc.comp_continuous (hZc.comp ((hBc.comp continuous_snd).add (hRc.comp continuous_fst)))
        (fun p => hdom p.1 p.2)
    exact h1.mul (hec.comp continuous_snd)
  have hfb : ∀ s t, ‖f s t‖ ≤ C / X.nfac la x0 := fun s t => by
    simp only [f]
    rw [norm_mul, he1, mul_one]
    exact hbdP s t
  have hK : volume K < ⊤ := (isCompact_univ_pi fun _ => isCompact_Icc).measure_lt_top
  have hswap := integral_swap_of_bdd hfd_top hK hfc hfb

  have hL : ∫ s in (exists_fd X la).choose, ∫ t in K, f s t =
      (volume (exists_fd X la).choose).toReal • X.fz u g χ P x0 := by
    rw [← MeasureTheory.measureReal_def, ← MeasureTheory.setIntegral_const]
    congr 1
    funext s
    rw [← hinv s, hfz, flow_eq_Zb X u ξ a hemb s x0]
    simp only [f, R, X.Zb_Zb u hu]

  have hR0 : ∀ t, ∫ s in (exists_fd X la).choose, f s t = 0 := by
    intro t
    have hy := X.Zb_dom u hu (B t) (herm_comb (X := X) hωH t) hx0
    have hc := hcusp _ hy
    simp only [Data.fj] at hc
    rw [if_pos (fun p _ => ⟨0, by simp⟩), dif_pos (exists_fd X la)] at hc
    simp only [Pi.zero_apply, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero, mul_zero,
      Complex.exp_zero, mul_one] at hc
    have hV : ((volume (exists_fd X la).choose).toReal : ℂ)⁻¹ ≠ 0 :=
      inv_ne_zero (by exact_mod_cast (ENNReal.toReal_pos hfd_pos.ne' hfd_top.ne).ne')
    have hI := (mul_eq_zero.1 hc).resolve_left hV
    have hpt : ∀ s : X.Ψ → ℝ, P (X.Zb u (B t + R s) x0) =
        P (X.flow ξ (fun τ => (s τ : ℂ)) (X.Zb u (B t) x0)) := by
      intro s
      rw [flow_eq_Zb X u ξ a hemb s, X.Zb_Zb u hu, add_comm]
    simp only [f]
    rw [MeasureTheory.integral_mul_const]
    simp_rw [hpt]
    rw [hI, zero_mul]
  rw [hswap] at hL
  simp only [hR0, MeasureTheory.integral_zero] at hL
  have hV : (volume (exists_fd X la).choose).toReal ≠ 0 := (ENNReal.toReal_pos hfd_pos.ne' hfd_top.ne).ne'
  exact (smul_eq_zero.1 hL.symm).resolve_left hV

private lemma herm_add_left_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G (x + y) z = herm G x z + herm G y z := by
  simp only [herm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma herm_add_right_fundamental_domains (G : Matrix (Fin r) (Fin r) E) (x y z : Fin r → E) :
    herm G x (y + z) = herm G x y + herm G x z := by
  simp only [herm, cc, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

private lemma herm_smul_left_fundamental_domains' (G : Matrix (Fin r) (Fin r) E) (t : E) (x y : Fin r → E) :
    herm G (t • x) y = t * herm G x y := by
  simp only [herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

private lemma herm_smul_right_eq_cc_mul' (G : Matrix (Fin r) (Fin r) E) (t : E) (x y : Fin r → E) :
    herm G x (t • y) = cc t * herm G x y := by
  simp only [herm, cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem nonvanishing_coefficient_positivity_of (h2 : UnipotentLatticeLift (E := E)) (h3 : FourierCoefficientProperties (E := E)) :
    NonvanishingCoefficientPositivity (E := E) := by
  intro r X u hu hΛ la P hP hχΓ χ hex τ
  obtain ⟨x1, hx1, hfz⟩ := hex
  obtain ⟨-, hinvP, hβ⟩ := h2 r X u hu hΛ
  have hcond : IsHermFam χ ∧ X.IsFreqZ X.g χ := by
    by_contra hc
    exact hfz (by simp only [Data.fz, if_neg hc])
  have hωex : ∃ ω, X.IsLZBasis X.g ω := by
    by_contra hc
    exact hfz (by simp only [Data.fz, if_pos hcond, dif_neg hc])
  obtain ⟨⟨hPsec, C, hC⟩, hcusp⟩ := hP
  have hPinv := hinvP la P hPsec hχΓ
  obtain ⟨⟨hFd, -, hFZ⟩, hFn, -⟩ :=
    h3 r X.toData u X.g hu X.g_pos la P hPsec.1 hPsec.2.1 hPinv χ
  have hFC : ∀ y ∈ X.dom, X.pnorm la (X.fz u X.g χ P) y ≤ C := fun y hy =>
    hFn y hy C fun b hb => hC _ (X.toData.Zb_dom u hu.1 b hb hy)
  have hpsd := psd_of X.toData u hu la χ hcond.1 _ hFd hFZ C hFC hx1 hfz τ
  obtain ⟨β, -, rfl, -⟩ := hβ χ hcond.1 hcond.2
  refine posDef_of_posSemidef_det hpsd ?_
  have hdet : (Matrix.of (X.embH β τ)).det = τ.1 β.det := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    rfl
  rw [hdet]
  intro h0
  have hβ0 : β.det = 0 := (RingHom.injective τ.1) (h0.trans (map_zero τ.1).symm)

  obtain ⟨c, hc0, hcβ⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hβ0
  obtain ⟨d, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ c
  have hint' : ∀ i, ∃ y : 𝓞 E, algebraMap (𝓞 E) E y = (d : 𝓞 E) • c i := fun i =>
    RingHom.mem_rangeS.1 (hint i (Finset.mem_univ i))
  choose c' hc' using hint'
  set e : Fin 2 → E := fun i => algebraMap (𝓞 E) E (c' i) with he_def
  have hde : ∀ i, e i = algebraMap (𝓞 E) E d * c i := fun i => by
    simp only [he_def, hc', Algebra.smul_def]
  have hdne : algebraMap (𝓞 E) E d ≠ 0 := by
    rw [Ne, ← map_zero (algebraMap (𝓞 E) E)]
    exact fun h => nonZeroDivisors.coe_ne_zero d (IsFractionRing.injective (𝓞 E) E h)
  have he0 : e ≠ 0 := by
    intro h
    apply hc0
    funext i
    have h1 := congrFun h i
    rw [hde, Pi.zero_apply] at h1
    simpa [hdne] using h1
  have hek : ∀ k, ∑ i, e i * β i k = 0 := by
    intro k
    have h1 := congrFun hcβ k
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h1
    simp only [hde, mul_assoc, ← Finset.mul_sum, h1, mul_zero]
  set ξ : Fin r → E := ∑ i, e i • u i with hξ_def
  have hξΛ : ξ ∈ X.Λ := by
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [he_def]
    dsimp only
    rw [algebraMap_smul E (c' i) (u i)]
    exact Submodule.smul_mem _ _ (hΛ i)
  have hξ0 : ξ ≠ 0 := fun h => he0 (funext (Fintype.linearIndependent_iff.1 hu.2 e h))
  have hξξ : herm X.Gm ξ ξ = 0 := by
    simp only [hξ_def, Fin.sum_univ_two, herm_add_left_fundamental_domains, herm_add_right_fundamental_domains, herm_smul_left_fundamental_domains',
      herm_smul_right_eq_cc_mul', hu.1, mul_zero, add_zero]
  have hemb : ∀ σ : X.Ψ, Data.emb σ.1 ξ = X.uvec u (fun σ i => σ.1 (e i)) σ := by
    intro σ
    funext j
    simp [Data.emb, Data.uvec, hξ_def, Finset.sum_apply, map_sum, map_mul]

  have hinv : ∀ s : X.Ψ → ℝ, X.fz u X.g (X.embH β) P (X.flow ξ (fun τ => (s τ : ℂ)) x1) =
      X.fz u X.g (X.embH β) P x1 := by
    intro s
    rw [flow_eq_Zb X.toData u ξ _ hemb s x1, hFZ _ (herm_rank1 X.toData s _) x1 hx1, pairR_rank1]
    have hz : ∀ σ, X.chiAt (X.embH β) (fun σ i => σ.1 (e i)) σ = 0 := by
      intro σ
      rw [chiAt_embH, Finset.sum_comm]
      have h1 : ∑ k, ∑ i, β i k * e i * cc (e k) = 0 := Finset.sum_eq_zero fun k _ => by
        rw [← Finset.sum_mul,
          show (∑ i, β i k * e i) = ∑ i, e i * β i k from Finset.sum_congr rfl fun i _ => mul_comm _ _,
          hek k, zero_mul]
      rw [h1, map_zero]
    simp [hz]
  exact hfz (fz_zero_of_inv X.toData u hu.1 X.g _ hcond hωex la P hPsec.1.continuousOn C hC ξ hξξ _
    hemb (hcusp ξ ⟨hξΛ, hξξ, hξ0⟩) hx1 hinv)

end

end ReciprocityTheory.ChartRestriction.G.FD.CoefficientPositivity
