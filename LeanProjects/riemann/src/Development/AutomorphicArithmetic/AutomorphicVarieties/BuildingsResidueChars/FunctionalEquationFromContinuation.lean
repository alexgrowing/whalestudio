import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.AdjointEta.EtaOK

open NumberField IsDedekindDomain Polynomial Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.SmGL
open UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter GlobalTheory.HenQ UpperTheory.V.Z.Inf UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.Ad
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.LocalField
open GroundTheory.Automorphic.GodementSection (localChar)
open Ad3P.DihedralUnramifiedPlaces (toH)
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private lemma gC_ne {s : ℂ} (hs : 0 < s.re) : Complex.Gammaℂ s ≠ 0 := by
  rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
  refine mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hs) (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
  simp only [Complex.add_re, Complex.one_re]; linarith

private lemma gC_diff {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gammaℂ s := by
  have h := (Complex.differentiable_Gammaℂ_inv s).inv (inv_ne_zero (gC_ne hs))
  have e : (fun z : ℂ => (Complex.Gammaℂ z)⁻¹)⁻¹ = Complex.Gammaℂ := by
    funext z; simp
  rwa [e] at h

private lemma arch_eq (k : ℕ) (s : ℂ) : arch k s = Complex.Gammaℂ (s + k - 1) ^ 2 * Complex.Gammaℂ s := by
  rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one s]
  simp only [arch, Ad3.lR, if_true, add_zero, Bool.false_eq_true, if_false]
  ring

private lemma sh_pos {k : ℕ} (hk : 3 ≤ k) {s : ℂ} (hs : 0 < s.re) : 0 < (s + (k : ℂ) - 1).re := by
  have : (3 : ℝ) ≤ k := by exact_mod_cast hk
  simp only [Complex.sub_re, Complex.add_re, Complex.natCast_re, Complex.one_re]; linarith

private lemma arch_ne {k : ℕ} (hk : 3 ≤ k) {s : ℂ} (hs : 0 < s.re) : arch k s ≠ 0 := by
  rw [arch_eq]
  exact mul_ne_zero (pow_ne_zero _ (gC_ne (sh_pos hk hs))) (gC_ne hs)

private lemma arch_diff {k : ℕ} (hk : 3 ≤ k) {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ (arch k) s := by
  have e : arch k = fun s => Complex.Gammaℂ (s + k - 1) ^ 2 * Complex.Gammaℂ s := funext (arch_eq k)
  rw [e]
  have h1 : DifferentiableAt ℂ (fun z : ℂ => Complex.Gammaℂ (z + (k : ℂ) - 1)) s :=
    DifferentiableAt.comp (𝕜 := ℂ) (g := Complex.Gammaℂ) (f := fun z : ℂ => z + (k : ℂ) - 1) s
      (gC_diff (sh_pos hk hs)) ((differentiableAt_id.add_const _).sub_const 1)
  exact (h1.pow 2).mul (gC_diff hs)

private lemma ne_of_pos {s : ℂ} (hs : 0 < s.re) : s ≠ 0 := by
  rintro rfl; simp at hs

private lemma arch_succ {k : ℕ} (hk : 3 ≤ k) {s : ℂ} (hs : 0 < s.re) :
    arch k (s + 1) = arch k s * ((s + k - 1) ^ 2 * s) * ((2 * (Real.pi : ℂ)) ^ 3)⁻¹ := by
  have e : s + 1 + (k : ℂ) - 1 = (s + k - 1) + 1 := by ring
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [arch_eq, arch_eq, e, Complex.Gammaℂ_add_one (ne_of_pos (sh_pos hk hs)), Complex.Gammaℂ_add_one (ne_of_pos hs)]
  field_simp

private lemma fac_diff (c₀ : ℂ) (t : ℝ) {q : ℝ} (hq : 1 < q) {P : ℂ[X]} (hP : ∀ x : ℂ, 1 < ‖x‖ → P.eval x ≠ 0)
    {s : ℂ} (hs : s.re < 1) : DifferentiableAt ℂ (fac c₀ t q P) s := by
  have hq0 : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have h1 : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (-z)) s :=
    differentiableAt_id.neg.const_cpow (Or.inl hq0)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => (q : ℂ) ^ (1 - z)) s :=
    (differentiableAt_id.const_sub 1).const_cpow (Or.inl hq0)
  have h3 : DifferentiableAt ℂ (fun z : ℂ => P.eval ((q : ℂ) ^ (-z))) s :=
    DifferentiableAt.comp (g := fun x => P.eval x) s (P.differentiableAt) h1
  have h4 : DifferentiableAt ℂ (fun z : ℂ => P.eval ((q : ℂ) ^ (1 - z))) s :=
    DifferentiableAt.comp (g := fun x => P.eval x) s (P.differentiableAt) h2
  have h5 : DifferentiableAt ℂ (fun z : ℂ => c₀ * Complex.exp (t * z)) s := by fun_prop
  have h6 : P.eval ((q : ℂ) ^ (1 - s)) ≠ 0 := by
    apply hP
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    apply Real.one_lt_rpow hq
    simp only [Complex.sub_re, Complex.one_re]; linarith
  exact (h5.mul h3).div h4 h6

private lemma glue (F G : ℂ → ℂ) (hF : ∀ s : ℂ, 1 / 4 < s.re → DifferentiableAt ℂ F s)
    (hG : ∀ s : ℂ, s.re < 3 / 4 → DifferentiableAt ℂ G s)
    (h : ∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → F s = G s) :
    ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ (∀ s : ℂ, 1 / 4 < s.re → Z s = F s) ∧ ∀ s : ℂ, s.re < 3 / 4 → Z s = G s := by
  have a : ∀ s : ℂ, 1 / 4 < s.re → (if 1 / 4 < s.re then F s else G s) = F s := fun s hs => if_pos hs
  have b : ∀ s : ℂ, s.re < 3 / 4 → (if 1 / 4 < s.re then F s else G s) = G s := fun s hs => by
    split_ifs with h'
    · exact h s h' hs
    · rfl
  refine ⟨fun s => if 1 / 4 < s.re then F s else G s, fun s => ?_, a, b⟩
  by_cases hs : 1 / 4 < s.re
  · refine (hF s hs).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with z hz using a z hz
  · have hs' : s.re < 3 / 4 := by linarith [not_lt.mp hs]
    refine (hG s hs').congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_lt Complex.continuous_re continuous_const).mem_nhds hs'] with z hz using b z hz

theorem UpperTheory.functional_equation_from_continuation :
    ∀ (k : ℕ) (L L' Λ Λ' : ℂ → ℂ) (g c₀ : ℂ) (t q : ℝ) (P : ℂ[X]), 3 ≤ k → 1 < q →
        DifferentiableOn ℂ Λ {s | 1 / 4 < s.re} → DifferentiableOn ℂ Λ' {s | 1 / 4 < s.re} →
        (∀ s : ℂ, 1 < s.re → Λ s = L s) → (∀ s : ℂ, s.re < 0 → Λ' (1 - s) = L' s) → (∃ s : ℂ, 1 < s.re ∧ L s ≠ 0) →
        (∀ x : ℂ, 1 < ‖x‖ → P.eval x ≠ 0) →
        (∀ s : ℂ, 1 / 4 < s.re → s.re < 3 / 4 → Λ s * arch k s = g * arch k (1 - s) * fac c₀ t q P s * Λ' (1 - s)) →
        ∃ β : ℂ[X], β ≠ 0 ∧ PairG L L' β q P := by
  intro k L L' Λ Λ' g c₀ t q P hk hq hΛ hΛ' hL hL' ⟨s₀, hs₀, hne⟩ hP hFE
  have hopen : IsOpen {s : ℂ | 1 / 4 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hπ : (2 * (Real.pi : ℂ)) ^ 3 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  obtain ⟨Z, hZ, hZr, hZl⟩ := glue (fun s => Λ s * arch k s)
    (fun s => g * arch k (1 - s) * fac c₀ t q P s * Λ' (1 - s))
    (fun s hs => (hΛ.differentiableAt (hopen.mem_nhds hs)).mul (arch_diff hk (by linarith)))
    (fun s hs => by
      have h1 : 1 / 4 < (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
      have h2 : DifferentiableAt ℂ (fun z : ℂ => arch k (1 - z)) s :=
        DifferentiableAt.comp (g := arch k) (f := fun z : ℂ => 1 - z) s (arch_diff hk (by linarith))
          (differentiableAt_id.const_sub 1)
      have h3 : DifferentiableAt ℂ (fun z : ℂ => Λ' (1 - z)) s :=
        DifferentiableAt.comp (g := Λ') (f := fun z : ℂ => 1 - z) s (hΛ'.differentiableAt (hopen.mem_nhds h1))
          (differentiableAt_id.const_sub 1)
      exact ((h2.const_mul g).mul (fac_diff c₀ t hq hP (by linarith))).mul h3) hFE
  refine ⟨(X + C ((k : ℂ) - 1)) ^ 2 * X * ((X - C ((k : ℂ) - 1)) ^ 2 * (-X)), ?_, Z,
    fun s => Z (s + 1) * ((s - (k - 1)) ^ 2 * (-s)), arch k, fun s => g * arch k (1 - s),
    ((2 * (Real.pi : ℂ)) ^ 3)⁻¹, (2 * (Real.pi : ℂ)) ^ 3, c₀, t, 1, hZ, ?_, ?_, inv_ne_zero hπ, hπ, ?_, ?_⟩
  · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_add_C_ne_zero _)) X_ne_zero)
      (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (neg_ne_zero.mpr X_ne_zero))
  · exact (hZ.comp (differentiable_id.add_const 1)).mul (by fun_prop)
  · intro h0
    have h1 := hZr s₀ (by linarith)
    rw [h0, hL s₀ hs₀] at h1
    exact mul_ne_zero hne (arch_ne hk (by linarith)) h1.symm
  · intro s hs
    have h1 : 1 < (s + 1).re := by simp only [Complex.add_re, Complex.one_re]; linarith
    refine ⟨by rw [hZr s (by linarith), hL s hs], ?_⟩
    show Z (s + 1) * _ = _
    rw [hZr (s + 1) (by linarith), hL _ h1, arch_succ hk (by linarith)]
    simp only [eval_mul, eval_pow, eval_add, eval_sub, eval_neg, eval_X, eval_C]
    ring
  · intro s hs
    have h1 : (s + 1).re < 0 := by simp only [Complex.add_re, Complex.one_re]; linarith
    have h2 : 0 < (-s).re := by simp only [Complex.neg_re]; linarith
    refine ⟨by rw [hZl s (by linarith), hL' s (by linarith)]; ring, ?_⟩
    show Z (s + 1) * _ = _ * _ * (g * arch k (1 - s)) * _
    have e1 : (1 : ℂ) - s = -s + 1 := by ring
    have e2 : (1 : ℂ) - (s + 1) = -s := by ring
    rw [hZl (s + 1) (by linarith), hL' _ h1, e1, e2, arch_succ hk h2]
    field_simp
    ring
