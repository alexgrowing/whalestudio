import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.ExistsRealSplitPrimitiveElementPadicFiniteExt
import Mathlib.NumberTheory.Padics.Hensel
import Mathlib.NumberTheory.NumberField.CMField
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IsCMOfConj
open Formalism.BasicNotions Formalism.BasicNotions.Loc NumberField

private theorem isCM_of_conj (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (h : ∀ x : K, ∃ y : K, ∀ φ : K →+* ℂ, φ y = starRingEnd ℂ (φ x)) : IsCMField K :=
  _root_.UpperTheory.Reformulated.B.Qh8.isCM_of_conj K h

open Polynomial in
private theorem exists_sqrt (l : ℕ) [hl : Fact l.Prime] :
    ∃ d : ℚ_[l], d ^ 2 = 1 - 4 * (l : ℚ_[l]) := by
  have h3 : ‖((l : ℕ) : ℤ_[l])‖ < 1 := PadicInt.norm_natCast_lt_one_iff.2 dvd_rfl
  obtain ⟨z, hz, -⟩ := hensels_lemma (p := l) (R := ℤ_[l]) (F := X ^ 2 - X + C (l : ℤ_[l])) (a := 0) (by
    have e1 : aeval (0 : ℤ_[l]) (X ^ 2 - X + C (l : ℤ_[l]) : ℤ_[l][X]) = ((l : ℕ) : ℤ_[l]) := by
      simp
    have e2 : aeval (0 : ℤ_[l]) (derivative (X ^ 2 - X + C (l : ℤ_[l]) : ℤ_[l][X])) = -1 := by
      simp
    rw [e1, e2, norm_neg, norm_one, one_pow]
    exact h3)
  have h4 : z ^ 2 - z + (l : ℤ_[l]) = 0 := by simpa using hz
  have h5 : (z : ℚ_[l]) ^ 2 - z + (l : ℚ_[l]) = 0 := by
    have := congrArg (fun x : ℤ_[l] => (x : ℚ_[l])) h4
    simpa using this
  exact ⟨2 * z - 1, by linear_combination 4 * h5⟩

private theorem conj_of_sq (w : ℂ) (r : ℝ) (hr : r < 0) (h : w ^ 2 = r) : starRingEnd ℂ w = -w := by
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have h3 : w.re = 0 := by
    by_contra h0
    have : w.im = 0 := by
      have : w.re * w.im = 0 := by linarith
      exact (mul_eq_zero.1 this).resolve_left h0
    rw [this] at h1
    nlinarith [mul_self_nonneg w.re]
  apply Complex.ext <;> simp [h3]

open Polynomial in
private theorem conj_of_root (g : ℚ[X]) (hg : g ≠ 0) (hs : (g.map (algebraMap ℚ ℝ)).Splits) (w : ℂ)
    (h : aeval w g = 0) : starRingEnd ℂ w = w := by
  have h1 : g.map (algebraMap ℚ ℝ) ≠ 0 := Polynomial.map_ne_zero hg
  have h2 : w ∈ ((g.map (algebraMap ℚ ℝ)).map (algebraMap ℝ ℂ)).roots := by
    rw [mem_roots (Polynomial.map_ne_zero h1), IsRoot.def, eval_map_algebraMap, aeval_map_algebraMap]
    exact h
  rw [hs.roots_map] at h2
  obtain ⟨r, -, rfl⟩ := Multiset.mem_map.1 h2
  exact Complex.conj_ofReal r

theorem UpperTheory.exists_totally_imaginary_generator_of_isCMField :
    ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : IsCMField M) (f : M →+* Om l), IntermediateField.adjoin ℚ_[l] (Set.range f) = K.1 ∧ ∃ (δ : M) (d : ℚ_[l]), δ ≠ 0 ∧ f δ = algebraMap ℚ_[l] (Om l) d ∧ ∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ := by
  intro l hl K
  obtain ⟨β, g, hgm, hgs, hβ, hK⟩ := UpperTheory.exists_real_split_primitive_element_padic_finite_ext l K
  obtain ⟨d, hd⟩ := exists_sqrt l
  have hl1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_lt.le
  set D : Om l := algebraMap ℚ_[l] (Om l) d with hD
  have hD2 : D ^ 2 = 1 - 4 * (l : Om l) := by
    rw [hD, ← map_pow, hd]; simp [map_ofNat]
  have hβi : IsIntegral ℚ β := ⟨g, hgm, hβ⟩
  have hDi : IsIntegral ℚ D := by
    apply IsIntegral.of_pow two_pos
    rw [hD2]
    have : (1 - 4 * (l : Om l)) = algebraMap ℚ (Om l) (1 - 4 * l) := by simp
    rw [this]
    exact isIntegral_algebraMap
  let M : IntermediateField ℚ (Om l) := IntermediateField.adjoin ℚ {β, D}
  have hfd : FiniteDimensional ℚ M := IntermediateField.finiteDimensional_adjoin (by
    rintro x (rfl | rfl)
    · exact hβi
    · exact hDi)
  have hNF : NumberField M := { to_charZero := inferInstance, to_finiteDimensional := hfd }
  let b : M := ⟨β, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  let δ : M := ⟨D, IntermediateField.subset_adjoin ℚ _ (by simp)⟩
  have hδ2 : δ ^ 2 = 1 - 4 * (l : M) := by
    apply (algebraMap M (Om l)).injective
    rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_natCast]
    exact hD2
  have hb : Polynomial.aeval b g = 0 := by
    apply (algebraMap M (Om l)).injective
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact hβ
  have hδφ2 : ∀ φ : M →+* ℂ, φ δ ^ 2 = ((1 - 4 * l : ℝ) : ℂ) := fun φ => by
    rw [← map_pow, hδ2]; simp [map_ofNat]
  have hδc : ∀ φ : M →+* ℂ, starRingEnd ℂ (φ δ) = -φ δ := fun φ =>
    conj_of_sq _ _ (by linarith) (hδφ2 φ)
  have hδ0 : ∀ φ : M →+* ℂ, φ δ ≠ 0 := fun φ h => by
    have := hδφ2 φ
    rw [h, zero_pow two_ne_zero] at this
    have : (1 - 4 * l : ℝ) = 0 := by exact_mod_cast this.symm
    linarith
  have hbc : ∀ φ : M →+* ℂ, starRingEnd ℂ (φ b) = φ b := fun φ => by
    refine conj_of_root g hgm.ne_zero hgs _ ?_
    have := Polynomial.aeval_algHom_apply φ.toRatAlgHom b g
    rw [hb, map_zero] at this
    exact this
  have htc : IsTotallyComplex M := ⟨fun w => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    intro h
    have h1 : starRingEnd ℂ (w.embedding δ) = w.embedding δ := RingHom.congr_fun h δ
    rw [hδc] at h1
    exact hδ0 w.embedding (by linear_combination (-1 / 2 : ℂ) * h1)⟩
  have hCM : IsCMField M := by
    refine isCM_of_conj _ ?_
    rintro ⟨x, hx⟩
    induction hx using IntermediateField.adjoin_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨b, fun φ => (hbc φ).symm⟩
      · exact ⟨-δ, fun φ => by rw [map_neg]; exact (hδc φ).symm⟩
    | algebraMap a =>
      refine ⟨algebraMap ℚ M a, fun φ => ?_⟩
      change φ (algebraMap ℚ M a) = starRingEnd ℂ (φ (algebraMap ℚ M a))
      simp
    | add x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a + b, fun φ => ?_⟩
      rw [map_add, ha, hb, ← map_add, ← map_add]
      rfl
    | inv x hx ihx =>
      obtain ⟨a, ha⟩ := ihx
      refine ⟨a⁻¹, fun φ => ?_⟩
      rw [map_inv₀, ha, ← map_inv₀, ← map_inv₀]
      rfl
    | mul x y hx hy ihx ihy =>
      obtain ⟨a, ha⟩ := ihx
      obtain ⟨b, hb⟩ := ihy
      refine ⟨a * b, fun φ => ?_⟩
      rw [map_mul, ha, hb, ← map_mul, ← map_mul]
      rfl
  refine ⟨M, inferInstance, hNF, hCM, algebraMap M (Om l), ?_, δ, d, ?_, rfl, hδc⟩
  · apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      have hβK : β ∈ K.1 := hK ▸ IntermediateField.mem_adjoin_simple_self _ β
      have hle : M.toSubfield ≤ K.1.toSubfield := by
        rw [IntermediateField.adjoin_toSubfield, Subfield.closure_le]
        rintro y (⟨q, rfl⟩ | rfl | rfl)
        · simp
        · exact hβK
        · exact K.1.algebraMap_mem d
      exact hle x.2
    · rw [← hK, IntermediateField.adjoin_le_iff]
      rintro _ rfl
      exact IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩
  · intro h
    have φ : M →+* ℂ := Classical.choice inferInstance
    exact hδ0 φ (by rw [h, map_zero])
