import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BetaPf
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ.Isolate

section Tr
variable {E : Type} [Field E] [NumberField E]

theorem trace_re (z : E) : ((Algebra.trace ℚ E z : ℚ) : ℝ) = ∑ τ : E →+* ℂ, (τ z).re := by
  have h := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := z)
  have h2 : ∑ σ : E →ₐ[ℚ] ℂ, σ z = ∑ τ : E →+* ℂ, τ z :=
    (Fintype.sum_equiv (RingHom.equivRatAlgHom E ℂ) _ _ (fun _ => rfl)).symm
  rw [h2] at h
  have := congrArg Complex.re h
  simpa [Complex.re_sum] using this

theorem eq_zero_of_trace (z : E) (h : ∀ a : 𝓞 E, Algebra.trace ℚ E (z * a) = 0) : z = 0 := by
  apply (traceForm_nondegenerate ℚ E).1
  intro y
  rw [← (integralBasis E).sum_repr y]
  simp only [map_sum, map_smul, Algebra.traceForm_apply, integralBasis_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have := h (RingOfIntegers.basis E i)
  rw [show (algebraMap (𝓞 E) E) (RingOfIntegers.basis E i) = (RingOfIntegers.basis E i : E) from rfl, this, smul_zero]

theorem exists_den : ∃ D : ℕ, 0 < D ∧ ∀ z : E, (∀ a : 𝓞 E, ∃ m : ℤ, Algebra.trace ℚ E (z * a) = m) →
    IsIntegral ℤ ((D : E) * z) := by
  classical
  set d := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) (NumberField.integralBasis E) with hd
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image d)
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, fun z hz => ?_⟩
  have key : IsIntegral ℤ ((y : E) * z) := by
    rw [← d.sum_repr z, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    obtain ⟨m, hm⟩ := hz (RingOfIntegers.basis E i)
    have : d.repr z i = m := by
      rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, integralBasis_apply]
      exact hm
    rw [this]
    have h1 := h (d i) (by simp)
    have : (y : E) * ((m : ℚ) • d i) = m • (y • d i) := by
      simp [Algebra.smul_def]; ring
    rw [this]
    exact h1.zsmul m
  rcases Int.natAbs_eq y with e | e
  · rw [e] at key; simpa using key
  · rw [e] at key
    have := key.neg
    simpa using this

variable {X : Type} [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X)

theorem trace_pairE (x : X) (a : 𝓞 E) :
    Algebra.trace ℚ E (GlobalTheory.ArcQ.pairE (E := E) ξ x * a) = (ξ (a • x) : ℤ) := by
  classical
  have hb : ∀ j, Algebra.trace ℚ E (GlobalTheory.ArcQ.pairE (E := E) ξ x * (RingOfIntegers.basis E j : E)) =
      (ξ ((RingOfIntegers.basis E j) • x) : ℤ) := by
    intro j
    unfold GlobalTheory.ArcQ.pairE
    rw [Finset.sum_mul, map_sum]
    have : ∀ i, Algebra.trace ℚ E ((Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E)
        (NumberField.integralBasis E) i * ((ξ ((NumberField.RingOfIntegers.basis E i) • x) : ℤ) : E) *
        (RingOfIntegers.basis E j : E)) = if j = i then ((ξ ((NumberField.RingOfIntegers.basis E i) • x) : ℤ) : ℚ) else 0 := by
      intro i
      have h := LinearMap.BilinForm.apply_dualBasis_left (B := Algebra.traceForm ℚ E) (traceForm_nondegenerate ℚ E)
        (NumberField.integralBasis E) i j
      rw [Algebra.traceForm_apply, integralBasis_apply] at h
      rw [mul_right_comm, mul_comm, ← zsmul_eq_mul, map_zsmul]
      erw [h]
      split_ifs <;> simp
    simp [this]
  conv => enter [1]; rw [← (RingOfIntegers.basis E).sum_repr a]
  conv => enter [2]; rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [Finset.sum_smul, map_sum, smul_assoc, map_zsmul, Finset.mul_sum, mul_smul_comm]
  push_cast
  refine Finset.sum_congr rfl fun j _ => ?_
  erw [hb]
  simp

theorem pairE_add (x y : X) : GlobalTheory.ArcQ.pairE (E := E) ξ (x + y) =
    GlobalTheory.ArcQ.pairE (E := E) ξ x + GlobalTheory.ArcQ.pairE (E := E) ξ y := by
  simp [GlobalTheory.ArcQ.pairE, smul_add, mul_add, Finset.sum_add_distrib]

theorem pairE_smul (a : 𝓞 E) (x : X) : GlobalTheory.ArcQ.pairE (E := E) ξ (a • x) =
    GlobalTheory.ArcQ.pairE (E := E) ξ x * a := by
  rw [← sub_eq_zero]
  apply eq_zero_of_trace
  intro b
  rw [sub_mul, map_sub, trace_pairE, mul_assoc]
  have := trace_pairE ξ x (a * b)
  rw [← mul_smul, mul_comm b a, ← this]
  simp

theorem pairE_zsmul (a : ℤ) (x : X) : GlobalTheory.ArcQ.pairE (E := E) ξ (a • x) =
    a * GlobalTheory.ArcQ.pairE (E := E) ξ x := by
  have := pairE_smul (E := E) ξ (a : 𝓞 E) x
  rw [Int.cast_smul_eq_zsmul] at this
  rw [this]; simp [mul_comm]

theorem exists_mul_eq_int (b : 𝓞 E) (hb : b ≠ 0) : ∃ (c : 𝓞 E) (n : ℤ), n ≠ 0 ∧ c * b = n := by
  have h := Ideal.absNorm_mem (Ideal.span {b})
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  refine ⟨c, Ideal.absNorm (Ideal.span {b}), ?_, by simpa using hc⟩
  simpa [Ideal.absNorm_eq_zero_iff] using hb

theorem pairE_ne_zero [Module.Finite ℤ X] [Module.Free ℤ X] (hξ : ξ ≠ 0) (h1 : Module.finrank (𝓞 E) X = 1)
    (x : X) (hx : x ≠ 0) : GlobalTheory.ArcQ.pairE (E := E) ξ x ≠ 0 := by
  intro h0
  apply hξ
  have hz : ∀ a : 𝓞 E, ξ (a • x) = 0 := by
    intro a
    have := trace_pairE ξ x a
    rw [h0, zero_mul, map_zero] at this
    exact_mod_cast this.symm
  haveI : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  ext y
  have hli : ¬ LinearIndependent (𝓞 E) ![x, y] := by
    intro h
    have := h.fintype_card_le_finrank
    simp [h1] at this
  rw [LinearIndependent.pair_iff] at hli
  push Not at hli
  obtain ⟨a, b, hab, hne⟩ := hli
  have hb : b ≠ 0 := by
    intro hb
    have ha : a ≠ 0 := fun ha => hne ha hb
    obtain ⟨c, n, hn, hc⟩ := exists_mul_eq_int a ha
    rw [hb, zero_smul, add_zero] at hab
    have : n • x = 0 := by rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← hc, mul_smul, hab, smul_zero]
    exact hx ((smul_eq_zero.mp this).resolve_left hn)
  obtain ⟨c, n, hn, hc⟩ := exists_mul_eq_int b hb
  have : (c * a) • x + n • y = 0 := by
    rw [← Int.cast_smul_eq_zsmul (𝓞 E), ← hc, mul_smul, mul_smul, ← smul_add, hab, smul_zero]
  have h2 := congrArg ξ this
  rw [map_add, hz, map_zsmul, map_zero, zero_add, smul_eq_mul] at h2
  simpa [hn] using h2

end Tr

section CM
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem cc_mul' (x y : E) : cc (x * y) = cc x * cc y := map_mul (IsCMField.complexConj E) x y
theorem cc_add' (x y : E) : cc (x + y) = cc x + cc y := map_add (IsCMField.complexConj E) x y
theorem cc_sub' (x y : E) : cc (x - y) = cc x - cc y := map_sub (IsCMField.complexConj E) x y
theorem cc_int (n : ℤ) : cc (n : E) = n := map_intCast (IsCMField.complexConj E) n
theorem cc_nat (n : ℕ) : cc (n : E) = n := map_natCast (IsCMField.complexConj E) n
theorem cc_two : cc (2 : E) = 2 := by simpa using cc_nat (E := E) 2
theorem cc_cc' (x : E) : cc (cc x) = x := IsCMField.complexConj_apply_apply E x
theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = (starRingEnd ℂ) (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x
theorem trace_cc (x : E) : Algebra.trace ℚ E (cc x) = Algebra.trace ℚ E x :=
  Algebra.trace_eq_of_algEquiv ((IsCMField.complexConj E).restrictScalars ℚ) x
theorem cc_integral {x : E} (h : IsIntegral ℤ x) : IsIntegral ℤ (cc x) :=
  h.map ((IsCMField.complexConj E).toRingEquiv.toRingHom.toIntAlgHom)
theorem im_zero {x : E} (h : cc x = x) (τ : E →+* ℂ) : (τ x).im = 0 := by
  have := emb_cc τ x
  rw [h] at this
  exact Complex.conj_eq_iff_im.mp this.symm

theorem exists_sym (a : 𝓞 E) : ∃ t : 𝓞 E, cc (t : E) = t ∧ ∀ μ : E, cc μ = μ →
    Algebra.trace ℚ E (μ * t) = 2 * Algebra.trace ℚ E (μ * a) := by
  refine ⟨⟨a + cc (a : E), a.2.add (cc_integral a.2)⟩, ?_, fun μ hμ => ?_⟩
  · change cc ((a : E) + cc (a : E)) = (a : E) + cc (a : E)
    rw [cc_add', cc_cc', add_comm]
  · change Algebra.trace ℚ E (μ * ((a : E) + cc (a : E))) = _
    rw [mul_add, map_add, ← trace_cc (μ * cc (a : E)), cc_mul', hμ, cc_cc']; ring

theorem exists_sep (S : Finset E) (hS : ∀ μ ∈ S, μ ≠ 0 ∧ cc μ = μ) :
    ∃ t : 𝓞 E, cc (t : E) = t ∧ ∀ μ ∈ S, Algebra.trace ℚ E (μ * t) ≠ 0 := by
  classical
  let e := (Fintype.equivFin (Module.Free.ChooseBasisIndex ℤ (𝓞 E))).symm
  let b := (RingOfIntegers.basis E).reindex e.symm
  let w : E → Fin (Fintype.card (Module.Free.ChooseBasisIndex ℤ (𝓞 E))) → ℝ :=
    fun μ j => ((Algebra.trace ℚ E (μ * (b j : E)) : ℚ) : ℝ)
  have hw : ∀ (μ : E) (n : Fin _ → ℤ), ((Algebra.trace ℚ E (μ * ((∑ j, n j • b j : 𝓞 E) : E)) : ℚ) : ℝ) =
      ∑ j, w μ j * n j := by
    intro μ n
    have : ((∑ j, n j • b j : 𝓞 E) : E) = ∑ j, n j • (b j : E) := by simp
    rw [this, Finset.mul_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_smul_comm, map_zsmul]
    simp [w, mul_comm]
  obtain ⟨n, hn⟩ := ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.exists_int_avoid (S.image w) (by
    intro z hz h0
    obtain ⟨μ, hμ, rfl⟩ := Finset.mem_image.mp hz
    apply (hS μ hμ).1
    apply eq_zero_of_trace
    intro a
    have := hw μ (b.repr a)
    rw [b.sum_repr a, h0] at this
    simpa using this)
  obtain ⟨t, ht, ht'⟩ := exists_sym (∑ j, n j • b j)
  refine ⟨t, ht, fun μ hμ h => hn _ (Finset.mem_image_of_mem w hμ) ?_⟩
  rw [ht' μ (hS μ hμ).2] at h
  rw [← hw]
  have : Algebra.trace ℚ E (μ * ((∑ j, n j • b j : 𝓞 E) : E)) = 0 := by linarith
  rw [this]; simp

def Freq (ν : E) : Prop := cc ν = ν ∧ (∀ τ : E →+* ℂ, 0 ≤ (τ ν).re) ∧
  ∀ t : 𝓞 E, cc (t : E) = t → ∃ m : ℤ, Algebra.trace ℚ E (ν * t) = m

theorem slice_finite (J : ℚ) : {ν : E | Freq ν ∧ Algebra.trace ℚ E ν = J}.Finite := by
  obtain ⟨D, hD, h⟩ := exists_den (E := E)
  have hfin := Embeddings.finite_of_norm_le E ℂ (D * (2 * J))
  refine Set.Finite.of_finite_image (f := fun ν => (D : E) * (2 * ν)) (hfin.subset ?_) ?_
  · rintro _ ⟨ν, ⟨⟨h1, h2, h3⟩, hJ⟩, rfl⟩
    refine ⟨h _ fun a => ?_, fun φ => ?_⟩
    · obtain ⟨t, ht, ht'⟩ := exists_sym a
      obtain ⟨m, hm⟩ := h3 t ht
      refine ⟨m, ?_⟩
      rw [← hm, ht' ν h1, mul_assoc, two_mul, map_add, two_mul]
    · have e1 : ‖φ ν‖ = (φ ν).re := by
        rw [← Complex.abs_re_eq_norm.mpr (im_zero h1 φ), abs_of_nonneg (h2 φ)]
      have e2 : (φ ν).re ≤ J := by
        rw [← hJ, trace_re]
        exact Finset.single_le_sum (f := fun τ : E →+* ℂ => (τ ν).re) (fun τ _ => h2 τ) (Finset.mem_univ φ)
      simp only [map_mul, map_natCast, map_ofNat, norm_mul, Complex.norm_natCast, Complex.norm_ofNat, e1]
      gcongr
  · intro x _ y _ hxy
    have hD' : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
    simpa [hD'] using hxy

theorem int_eq_of_weighted_sum_eq_with_small_errors (M R A B : ℝ) (i j : ℤ) (hi : (0 : ℝ) ≤ i) (hj : (0 : ℝ) ≤ j) (hM : 0 ≤ M)
    (hR : M * (2 * j + 1) < R) (hA : |A| ≤ M * i) (hB : |B| ≤ M * j) (h : R * i + A = R * j + B) : i = j := by
  by_contra hij
  have hR0 : 0 ≤ R := le_trans (by positivity) hR.le
  have hdiff : R * ((i : ℝ) - j) = B - A := by linarith
  have habs : |R * ((i : ℝ) - j)| ≤ M * (i + j) := by
    rw [hdiff]
    calc |B - A| ≤ |B| + |A| := abs_sub _ _
      _ ≤ M * j + M * i := add_le_add hB hA
      _ = M * (i + j) := by ring
  have hne : (1 : ℝ) ≤ |(i : ℝ) - j| := by
    have : (i - j : ℤ) ≠ 0 := sub_ne_zero.mpr hij
    have h := Int.one_le_abs this
    exact_mod_cast h
  have hkey : (i : ℝ) + j ≤ (2 * j + 1) * |(i : ℝ) - j| := by
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : (i : ℝ) + 1 ≤ j := by exact_mod_cast h
      rw [abs_of_nonpos (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ j - i by linarith)
        (show (0 : ℝ) ≤ 2 * j + 1 by linarith)]
    · have h1 : (j : ℝ) + 1 ≤ i := by exact_mod_cast h
      rw [abs_of_pos (by linarith)]
      nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ i - j by linarith)
        (show (0 : ℝ) ≤ 2 * j by linarith)]
  rw [abs_mul, abs_of_nonneg hR0] at habs
  have : R * |(i : ℝ) - j| ≤ M * ((2 * j + 1) * |(i : ℝ) - j|) :=
    le_trans habs (mul_le_mul_of_nonneg_left hkey hM)
  nlinarith [abs_nonneg ((i : ℝ) - j)]

theorem exists_isolating (ν₀ : E) (h₀ : Freq ν₀) : ∃ u : 𝓞 E, cc (u : E) = u ∧ (∀ τ : E →+* ℂ, 0 < (τ u).re) ∧
    ∀ ν, Freq ν → Algebra.trace ℚ E (ν * u) = Algebra.trace ℚ E (ν₀ * u) → ν = ν₀ := by
  classical
  have hfin := slice_finite (E := E) (Algebra.trace ℚ E ν₀)
  obtain ⟨t, ht, hsep⟩ := exists_sep ((hfin.toFinset.filter (· ≠ ν₀)).image (· - ν₀)) (by
    intro μ hμ
    obtain ⟨ν, hν, rfl⟩ := Finset.mem_image.mp hμ
    rw [Finset.mem_filter, Set.Finite.mem_toFinset] at hν
    exact ⟨sub_ne_zero.mpr hν.2, by rw [cc_sub', hν.1.1.1, h₀.1]⟩)
  set M : ℝ := ∑ τ : E →+* ℂ, |(τ t).re| with hM
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hle : ∀ τ : E →+* ℂ, |(τ t).re| ≤ M := fun τ =>
    Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)
  have hint : ∀ ν : E, Freq ν → ∃ i : ℤ, Algebra.trace ℚ E ν = i ∧ (0 : ℝ) ≤ i ∧
      |((Algebra.trace ℚ E (ν * t) : ℚ) : ℝ)| ≤ M * i := by
    intro ν hν
    obtain ⟨i, hi⟩ := hν.2.2 1 (by simpa using cc_nat (E := E) 1)
    have hi' : Algebra.trace ℚ E ν = i := by simpa using hi
    have hs : (i : ℝ) = ∑ τ : E →+* ℂ, (τ ν).re := by rw [← trace_re, hi']; simp
    refine ⟨i, hi', hs ▸ Finset.sum_nonneg fun τ _ => hν.2.1 τ, ?_⟩
    rw [trace_re, hs, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    rw [map_mul, Complex.mul_re, im_zero hν.1, zero_mul, sub_zero, abs_mul, abs_of_nonneg (hν.2.1 τ), mul_comm]
    exact mul_le_mul_of_nonneg_right (hle τ) (hν.2.1 τ)
  obtain ⟨j, hj, hj0, hjb⟩ := hint ν₀ h₀
  obtain ⟨R, hR⟩ : ∃ R : ℕ, M * (2 * j + 1) < R := exists_nat_gt _
  have hu : (((R : 𝓞 E) + t : 𝓞 E) : E) = R + (t : E) := by simp
  have htr : ∀ ν : E, Algebra.trace ℚ E (ν * (R + (t : E))) = R * Algebra.trace ℚ E ν + Algebra.trace ℚ E (ν * t) := by
    intro ν
    rw [mul_add, map_add, mul_comm ν R, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul]
  refine ⟨R + t, ?_, fun τ => ?_, fun ν hν h => ?_⟩
  · rw [hu, cc_add', cc_nat, ht]
  · rw [hu, map_add, map_natCast, Complex.add_re, Complex.natCast_re]
    have h1 := (abs_le.mp (hle τ)).1
    nlinarith [mul_nonneg hM0 hj0]
  · rw [hu, htr, htr] at h
    obtain ⟨i, hi, hi0, hib⟩ := hint ν hν
    have hij : i = j := by
      refine int_eq_of_weighted_sum_eq_with_small_errors M R _ _ i j hi0 hj0 hM0 hR hib hjb ?_
      rw [hi, hj] at h
      exact_mod_cast h
    by_contra hne
    have e : Algebra.trace ℚ E ν = Algebra.trace ℚ E ν₀ := by rw [hi, hj, hij]
    refine hsep (ν - ν₀) (Finset.mem_image_of_mem _ ?_) ?_
    · rw [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨⟨hν, e⟩, hne⟩
    · rw [sub_mul, map_sub]; rw [e] at h; linarith

end CM

theorem exists_form_isolating : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite ℤ X] [Module.Free ℤ X] (ξ : Module.Dual ℤ X) (N : ℕ) (ν₀ : E), ξ ≠ 0 → Module.finrank (𝓞 E) X = 1 → 0 < N → cc ν₀ = ν₀ → (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) → (∀ s, LevelPar ξ N s → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m) → ∃ (be : LinearMap.BilinForm ℤ X) (s : E) (jj : ℤ), IsBePar ξ be s ∧ (∀ x y, be x y = be y x) ∧ (∀ x, x ≠ 0 → 0 < be x x) ∧ (∀ x y, (2 * N : ℤ) ∣ be x y) ∧ BetaAt ξ N be ν₀ jj := by
  intro E _ _ _ X _ _ _ _ ξ N ν₀ hξ h1 hN hc hpos hint
  obtain ⟨D, hD, hden⟩ := exists_den (E := E)
  set p : X → E := GlobalTheory.ArcQ.pairE (E := E) ξ with hp
  have hq : ∀ y, IsIntegral ℤ ((D : E) * cc (p y)) := by
    intro y
    have := cc_integral (hden (p y) fun a => ⟨_, trace_pairE ξ y a⟩)
    rwa [cc_mul', cc_nat] at this
  have hval : ∀ (t : 𝓞 E) (x y : X), ∃ m : ℤ,
      Algebra.trace ℚ E (2 * ((N * D : E) * t) * p x * cc (p y)) = 2 * N * m := by
    intro t x y
    refine ⟨ξ ((t * ⟨_, hq y⟩ : 𝓞 E) • x), ?_⟩
    rw [← trace_pairE]
    have : 2 * ((N * D : E) * t) * p x * cc (p y) = (2 * N : ℚ) • (p x * ((t : E) * (D * cc (p y)))) := by
      simp [Algebra.smul_def]; ring
    rw [this, map_smul, smul_eq_mul]
    rfl
  have hreal : ∀ t : 𝓞 E, cc (t : E) = t → cc ((N * D : E) * t) = (N * D : E) * t := by
    intro t ht
    rw [cc_mul', cc_mul', cc_nat, cc_nat, ht]
  have hlev : ∀ t : 𝓞 E, cc (t : E) = t → LevelPar ξ N ((N * D : E) * t) := by
    intro t ht
    refine ⟨hreal t ht, fun x y => ?_⟩
    obtain ⟨m, hm⟩ := hval t x y
    exact ⟨2 * m, by rw [hm]; push_cast; ring⟩
  have hfreq : ∀ ν : E, cc ν = ν → (∀ τ : E →+* ℂ, 0 ≤ (τ ν).re) →
      (∀ s, LevelPar ξ N s → ∃ m : ℤ, Algebra.trace ℚ E (ν * s) = m) → Freq (ν * (N * D)) := by
    intro ν a b c
    refine ⟨by rw [cc_mul', cc_mul', cc_nat, cc_nat, a], fun τ => ?_, fun t ht => ?_⟩
    · have : (τ (ν * (N * D))).re = (τ ν).re * (N * D) := by simp
      rw [this]
      exact mul_nonneg (b τ) (by positivity)
    · rw [mul_assoc]; exact c _ (hlev t ht)
  obtain ⟨u, hu, hupos, huniq⟩ := exists_isolating _ (hfreq ν₀ hc hpos hint)
  set s : E := (N * D : E) * u with hs
  choose m hm using hval u
  let f : X → X → ℤ := fun x y => 2 * N * m x y
  have hf : ∀ x y, Algebra.trace ℚ E (2 * s * p x * cc (p y)) = (f x y : ℚ) := by
    intro x y; rw [hm]; simp [f]
  let be : LinearMap.BilinForm ℤ X := LinearMap.mk₂ ℤ f
    (fun x x' y => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, hp, pairE_add, ← map_add]; congr 1; ring)
    (fun n x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul n, ← hf, ← hf, hp, pairE_zsmul, ← zsmul_eq_mul (Algebra.trace ℚ E _) n, ← map_zsmul]
      congr 1; rw [zsmul_eq_mul]; ring)
    (fun x y y' => by
      apply Int.cast_injective (α := ℚ)
      rw [Int.cast_add, ← hf, ← hf, ← hf, hp, pairE_add, cc_add', ← map_add]; congr 1; ring)
    (fun n x y => by
      apply Int.cast_injective (α := ℚ)
      rw [smul_eq_mul, Int.cast_mul n, ← hf, ← hf, hp, pairE_zsmul, cc_mul', cc_int,
        ← zsmul_eq_mul (Algebra.trace ℚ E _) n, ← map_zsmul]
      congr 1; rw [zsmul_eq_mul]; ring)
  have hbe : ∀ x y, be x y = f x y := fun _ _ => rfl
  obtain ⟨jj, hjj⟩ := hint s (hlev u hu)
  have hND : (0 : ℝ) < N * D := by positivity
  have hND' : (N * D : E) ≠ 0 := by exact_mod_cast (Nat.mul_pos hN hD).ne'
  refine ⟨be, s, jj, ⟨hreal u hu, hf⟩, fun x y => ?_, fun x hx => ?_, fun x y => ⟨m x y, rfl⟩, hc, fun s' hs' => ?_⟩
  · apply Int.cast_injective (α := ℚ)
    rw [hbe, hbe, ← hf, ← hf, ← trace_cc, cc_mul', cc_mul', cc_mul', cc_cc', cc_two, hreal u hu]
    congr 1; ring
  · have : (0 : ℝ) < ((f x x : ℚ) : ℝ) := by
      rw [← hf, trace_re]
      refine Finset.sum_pos (fun τ _ => ?_) Finset.univ_nonempty
      have h0 : τ (p x) ≠ 0 := (map_ne_zero τ).mpr (pairE_ne_zero ξ hξ h1 x hx)
      have e : (τ (2 * s * p x * cc (p x))).re = 2 * ((N * D) * (τ u).re) * Complex.normSq (τ (p x)) := by
        rw [mul_assoc, map_mul, map_mul τ (p x), emb_cc, Complex.mul_conj, hs]
        simp [map_ofNat]
      rw [e]
      have := hupos τ
      have := Complex.normSq_pos.mpr h0
      positivity
    rw [hbe]
    exact_mod_cast this
  · have hss : s' = s := by
      obtain ⟨x, hx⟩ : ∃ x : X, x ≠ 0 := by
        by_contra hx
        push Not at hx
        exact hξ (by ext y; simp [hx y])
      have h0 : p x ≠ 0 := pairE_ne_zero ξ hξ h1 x hx
      have h0' : cc (p x) ≠ 0 := fun h => h0 (by rw [← cc_cc' (p x), h]; simpa using cc_nat (E := E) 0)
      have : 2 * (s' - s) * p x * cc (p x) = 0 := by
        apply eq_zero_of_trace
        intro a
        have e1 := hs'.2 (a • x) x
        have e2 := hf (a • x) x
        rw [hbe, ← e2, ← sub_eq_zero, ← map_sub] at e1
        rw [← e1, hp, pairE_smul]
        congr 1; ring
      simpa [h0, h0', sub_eq_zero] using this
    subst hss
    refine ⟨hjj, fun ν a b c d => ?_⟩
    have := huniq _ (hfreq ν a b c) (by rw [mul_assoc ν, mul_assoc ν₀, d, hjj])
    exact mul_right_cancel₀ hND' this

end GlobalTheory.ArcQ.Isolate
