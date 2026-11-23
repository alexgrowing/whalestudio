import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.InhabSt
import ReciprocityTheory.SemistableReduction.SemiDegCA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.QCoreGlobPf
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.TraceFormDualOneTraceFormDual
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant

noncomputable section

open NumberField Module ReciprocityTheory.GeometryOfNumbersTheory
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

section Line

variable {L : Type} [Field L] [NumberField L]

def lineHerm (n : (L →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s) : HermFam L L where
  form s x y := n s * (starRingEnd ℂ (s x) * s y)
  add_right s x y z := by simp [mul_add]
  smul_right s a x y := by simp [mul_left_comm]
  conj_symm s x y := by simp [mul_comm]
  posDef s m v hv := by
    have hli : LinearIndependent L fun i (_ : Fin 1) => v i :=
      hv.map' (LinearEquiv.funUnique (Fin 1) L L).symm.toLinearMap (LinearEquiv.ker _)
    have h := (standardHermitian_gram_posDef L s _ hli).smul (a := (n s : ℂ)) (by exact_mod_cast hn s)
    convert h using 1
    ext i j
    simp

theorem deg_lineHerm (n : (L →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s) {𝔠 : FractionalIdeal (𝓞 L)⁰ L} (h𝔠 : 𝔠 ≠ 0) :
    deg (lineHerm n hn) (𝔠 : Submodule (𝓞 L) L) =
      -Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ L - meanLog L n / 2 := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ 𝔠, a ≠ 0 := by
    simpa [FractionalIdeal.eq_zero_iff] using h𝔠
  have hf : IsFrame L (𝔠 : Submodule (𝓞 L) L) (fun _ : Fin 1 => a) :=
    ⟨fun _ => ha, linearIndependent_unique_iff.mpr ha0, fun x _ => by
      rw [Set.range_const, SetLike.mem_coe, Submodule.mem_span_singleton]
      exact ⟨x / a, div_mul_cancel₀ x ha0⟩⟩
  let 𝔟 := FractionalIdeal.spanSingleton (𝓞 L)⁰ a⁻¹ * 𝔠
  have hm : ∀ x, x ∈ 𝔟 ↔ a * x ∈ 𝔠 := fun x => by
    rw [FractionalIdeal.mem_singleton_mul]
    exact ⟨fun ⟨y, hy, e⟩ => by rwa [e, mul_inv_cancel_left₀ ha0], fun h => ⟨_, h, by field_simp⟩⟩
  have h1 := ReciprocityTheory.MultiplicativeHeights.SemiDegIdx.absNorm_mul_relIndex_one (𝔟 : Submodule (𝓞 L) L)
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔟) (Submodule.one_le.2 ((hm 1).2 (by simpa using ha)))
  have e1 : (1 : Submodule (𝓞 L) L).toAddSubgroup.map (AddMonoidHom.mulLeft a) =
      (Submodule.span (𝓞 L) (Set.range fun _ : Fin 1 => a)).toAddSubgroup := by
    ext x
    simp [Submodule.mem_span_singleton, Algebra.smul_def, mul_comm]
  have e2 : (𝔟 : Submodule (𝓞 L) L).toAddSubgroup.map (AddMonoidHom.mulLeft a) =
      (𝔠 : Submodule (𝓞 L) L).toAddSubgroup := by
    ext x
    refine ⟨?_, fun h => ⟨a⁻¹ * x, (hm _).2 (by rwa [mul_inv_cancel_left₀ ha0]), mul_inv_cancel_left₀ ha0 x⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact (hm y).1 hy
  rw [← AddSubgroup.relIndex_map_map_of_injective (f := AddMonoidHom.mulLeft a) _ _ (mul_right_injective₀ ha0),
    e1, e2] at h1
  change FractionalIdeal.absNorm 𝔟 * _ = 1 at h1
  rw [map_mul, FractionalIdeal.absNorm_span_singleton, Algebra.norm_inv, abs_inv] at h1
  have hN : Algebra.norm ℚ a ≠ 0 := Algebra.norm_ne_zero_iff.2 ha0
  have hc : FractionalIdeal.absNorm 𝔠 ≠ 0 := (map_ne_zero _).2 h𝔠
  have h2 := (eq_inv_of_mul_eq_one_right h1)
  have h3 := congrArg (fun q : ℚ => Real.log (q : ℝ)) h2
  simp only [Rat.cast_natCast, mul_inv, inv_inv, Rat.cast_mul, Rat.cast_inv, Rat.cast_abs] at h3
  rw [Real.log_mul (by simpa using hN) (by simpa using hc), Real.log_inv] at h3
  have h4 : ∀ s, Real.log ((lineHerm n hn).gram s fun _ : Fin 1 => a).det.re =
      Real.log (n s) + Real.log (Complex.normSq (s a)) := fun s => by
    rw [← Real.log_mul (hn s).ne' (by simpa using ha0), Matrix.det_fin_one]
    congr 1
    simp [HermFam.gram, lineHerm, Complex.normSq_apply]
  rw [arakelovDegree_eq_degreeOfFamily _ (FractionalIdeal.fg_of_isNoetherianRing le_rfl 𝔠) hf, degreeOfFamily, h3, meanLog]
  simp only [h4, Finset.sum_add_distrib, ds_sum_log_normSq_embeddings a ha0]
  ring

end Line

section Norm

variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]

theorem absNorm_extendedHom [Algebra E L] (𝔞 : FractionalIdeal (𝓞 E)⁰ E) :
    FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L) 𝔞) = FractionalIdeal.absNorm 𝔞 ^ finrank E L := by
  have key : ∀ I : Ideal (𝓞 E), FractionalIdeal.absNorm (FractionalIdeal.extendedHom L (𝓞 L)
      (I : FractionalIdeal (𝓞 E)⁰ E)) = FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 E)⁰ E) ^ finrank E L :=
    fun I => by
      rw [FractionalIdeal.extendedHom_coeIdeal_eq_map, FractionalIdeal.coeIdeal_absNorm,
        FractionalIdeal.coeIdeal_absNorm, Ideal.absNorm_algebraMap,
        ← IsFractionRing.finrank_eq (𝓞 E) E (𝓞 L) L, Nat.cast_pow]
  have h := 𝔞.den_mul_self_eq_num'
  rw [← FractionalIdeal.coeIdeal_span_singleton] at h
  have h0 : FractionalIdeal.absNorm ((Ideal.span {(𝔞.den : 𝓞 E)} : Ideal (𝓞 E)) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    simp
  have h1 := key 𝔞.num
  rw [← h, map_mul, map_mul, map_mul, key, mul_pow] at h1
  exact mul_left_cancel₀ (pow_ne_zero _ h0) h1

theorem exists_fractionalIdeal_eq_span_image (τ : E →+* L) {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) :
    ∃ 𝔠 : FractionalIdeal (𝓞 L)⁰ L, 𝔠 ≠ 0 ∧ (𝔠 : Submodule (𝓞 L) L) = Submodule.span (𝓞 L) (τ '' 𝔞) ∧
      Real.log (FractionalIdeal.absNorm 𝔠) / finrank ℚ L = Real.log (FractionalIdeal.absNorm 𝔞) / finrank ℚ E := by
  let _ := τ.toAlgebra
  refine ⟨FractionalIdeal.extendedHom L (𝓞 L) 𝔞, by rwa [Ne, FractionalIdeal.extendedHom_eq_zero_iff],
    FractionalIdeal.coe_extendedHom_eq_span L (𝓞 L) 𝔞, ?_⟩
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  rw [absNorm_extendedHom, Rat.cast_pow, Real.log_pow, ← finrank_mul_finrank ℚ E L, Nat.cast_mul]
  field_simp

theorem meanLog_comp (j : E →+* L) (n : (E →+* ℂ) → ℝ) : meanLog L (fun s => n (s.comp j)) = meanLog E n := by
  let _ := j.toAlgebra
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  have h := ReciprocityTheory.ChartRestriction.G.FreeQuotientRank.sum_embeddings_restrict (K₁ := L) fun s => Real.log (n s)
  rw [meanLog, meanLog, ← finrank_mul_finrank ℚ E L, Nat.cast_mul, div_eq_iff (by positivity)]
  refine h.trans ?_
  field_simp

theorem log_absNorm_conjFrac [IsCMField E] {𝔞 : FractionalIdeal (𝓞 E)⁰ E} (h𝔞 : 𝔞 ≠ 0) :
    Real.log (FractionalIdeal.absNorm (conjFrac 𝔞)) = Real.log (FractionalIdeal.absNorm 𝔞) := by
  obtain ⟨𝔠, -, h1, h2⟩ := exists_fractionalIdeal_eq_span_image
    ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E) h𝔞
  have h3 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  have e : ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E) '' 𝔞 =
      ((conjFrac 𝔞 : Submodule (𝓞 E) E) : Set E) := by
    ext x
    refine ⟨?_, fun h => ⟨_, mem_conjFrac.1 h, IsCMField.complexConj_apply_apply E x⟩⟩
    rintro ⟨y, hy, rfl⟩
    exact cc_mem_conjFrac.2 hy
  rw [e, Submodule.span_eq, FractionalIdeal.coeToSubmodule_inj] at h1
  rwa [h1, div_left_inj' h3.ne'] at h2

theorem log_rootDiscr_tower [Algebra E L] : Real.log (rootDiscr L) =
    Real.log (Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L))) / finrank ℚ L + Real.log (rootDiscr E) := by
  have h1 : (0 : ℝ) < finrank E L := by exact_mod_cast finrank_pos
  have h2 : (0 : ℝ) < finrank ℚ E := by exact_mod_cast finrank_pos
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow E (𝓞 E) L (𝓞 L)
  have h3 : Ideal.absNorm (differentIdeal (𝓞 E) (𝓞 L)) ≠ 0 := fun h0 => by
    simp [h0, discr_ne_zero] at h
  have h4 := congrArg (fun m : ℕ => Real.log (m : ℝ)) h
  have p : ∀ m : ℤ, m ≠ 0 → (0 : ℝ) < (|m| : ℤ) := fun m hm => by exact_mod_cast abs_pos.2 hm
  simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_natAbs] at h4
  rw [Real.log_mul (by exact_mod_cast h3) (pow_ne_zero _ (p _ (discr_ne_zero E)).ne'), Real.log_pow] at h4
  rw [rootDiscr_def, rootDiscr_def, Real.log_rpow (p _ (discr_ne_zero L)), Real.log_rpow (p _ (discr_ne_zero E)), h4,
    ← finrank_mul_finrank ℚ E L, Nat.cast_mul]
  field_simp

end Norm

section Different

variable {K E M L : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E]
  [Field M] [NumberField M] [Field L] [NumberField L]

theorem two_mul_deg_lineHerm_different {𝔄 : FractionalIdeal (𝓞 E)⁰ E}
    (h𝔄 : 𝔄 * conjFrac 𝔄 = (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹)
    (n : (M →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s) (j : M →+* L) (τ : E →+* L) :
    2 * deg (lineHerm (fun s => n (s.comp j)) fun _ => hn _)
        (Submodule.span (𝓞 L) (τ '' (𝔄 * differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))) =
      -meanLog M n + Real.log (rootDiscr K) - Real.log (rootDiscr E) := by
  have h0 : (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot
  have h1 : 𝔄 ≠ 0 := left_ne_zero_of_mul (h𝔄 ▸ inv_ne_zero h0)
  have nz : ∀ {𝔞 : FractionalIdeal (𝓞 E)⁰ E}, 𝔞 ≠ 0 → (FractionalIdeal.absNorm 𝔞 : ℝ) ≠ 0 := fun h => by
    simpa using h
  obtain ⟨𝔠, h𝔠, e, h2⟩ := exists_fractionalIdeal_eq_span_image τ (mul_ne_zero h1 h0)
  have h3 := congrArg (fun 𝔞 => Real.log (FractionalIdeal.absNorm 𝔞 : ℚ)) h𝔄
  simp only [map_mul, map_inv₀, Rat.cast_mul, Rat.cast_inv, Real.log_inv] at h3
  rw [Real.log_mul (nz h1) (nz (conjFrac_ne_zero h1)), log_absNorm_conjFrac h1] at h3
  rw [map_mul, Rat.cast_mul, Real.log_mul (nz h1) (nz h0)] at h2
  rw [← e, deg_lineHerm _ _ h𝔠, meanLog_comp, neg_div, h2, log_rootDiscr_tower (E := K) (L := E)]
  rw [FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast] at h3 ⊢
  linear_combination -h3 / (finrank ℚ E : ℝ)

end Different

section Period

open AlgebraicGeometry CategoryTheory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped UpperHalfPlane

variable {d : ℕ} [NeZero d] {K : Type} [Field K] [NumberField K]

omit [NeZero d] in
theorem rootDiscr_eq_sqrt (h2 : finrank ℚ K = 2) (hD : discr K = -d) : rootDiscr K = √d := by
  rw [rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
  simp

theorem chowla_selberg_of_mean_log (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) {M : Type} [Field M] [NumberField M]
    (n : (M →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s)
    (h : ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) →
      (∑ s, Real.log (n s)) / finrank ℚ M =
        (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K) :
    ((-meanLog M n : ℝ) : ℂ) =
      (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (𝔄 : FractionalIdeal (𝓞 E)⁰ E),
      𝔄 * conjFrac 𝔄 = (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ →
      ∀ (L : Type) [Field L] [NumberField L] (j : M →+* L) (τ : E →+* L),
      ((2 * deg (lineHerm (fun s => n (s.comp j)) fun _ => hn _)
          (Submodule.span (𝓞 L) (τ '' (𝔄 * differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))) : ℝ) : ℂ) =
        (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) : ℝ)
          - deriv χ.LFunction 1 / χ.LFunction 1 := by
  obtain ⟨σ⟩ : Nonempty (K →+* ℂ) := inferInstance
  choose τ hτ using exists_isIdealClassPoint h2 hD σ
  have h1 := chowla_selberg_eta h2 hD hd hχ σ hτ
  have h3 := h σ τ hτ
  rw [Finset.sum_neg_distrib, neg_div, ← neg_eq_iff_eq_neg] at h3
  rw [← h3] at h1
  refine ⟨h1, fun E _ _ _ _ 𝔄 h𝔄 L _ _ j τ => ?_⟩
  have h4 : (0 : ℝ) < √d := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < d))
  have h5 : 0 < rootDiscr E := Real.rpow_pos_of_pos (by exact_mod_cast abs_pos.2 (discr_ne_zero E)) _
  rw [two_mul_deg_lineHerm_different h𝔄 n hn, Complex.ofReal_sub, Complex.ofReal_add, meanLog, h1,
    rootDiscr_eq_sqrt h2 hD, Real.log_div (by positivity) h4.ne', Real.log_div (by positivity) h5.ne']
  push_cast
  ring

theorem chowla_selberg_lie_lines (hC : CMCurve) (h7 : 7 ≤ d) (hs : Squarefree d) (h4 : d % 4 = 3)
    (h2 : finrank ℚ K = 2) (hr : ∃ r : K, r ^ 2 = -(d : K)) {χ : DirichletCharacter ℂ d} (hχ : IsKroneckerChar χ) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (w : M) (P : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A),
      (w : ℂ) = (1 + Complex.I * √d) / 2 ∧ P.g = 1 ∧ IsLieBasis ![v] ∧
      (∃ (P₀ : Out.PolAV (Sp M)) (φ : P₀.A.left ⟶ P.A.left) (v₀ : epsR M ⟶ P₀.A) (W : P₀.A ⟶ P₀.A),
        IsPolFibre (algebraMap (𝓞 M) M) P P₀ φ ∧ IsVecOver (algebraMap (𝓞 M) M) φ v v₀ ∧ IsLieBasis ![v₀] ∧
        IsMonHom W ∧ (W ≫ W) * (𝟙 P₀.A) ^ ((1 + d) / 4) = W ∧ IsLieComb ![w] ![v₀] (v₀ ≫ W)) ∧
      (∀ (P' : Out.PolAV (Sp ℂ)) (φ : P'.A.left ⟶ P.A.left),
        IsPolFibre ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) P P' φ → ∀ u : HolUnif P'.A P'.L P'.g,
        ∃ c : ℂ, c ≠ 0 ∧ ∀ z, z ∈ u.Λ ↔ ∃ m n : ℤ, z = fun _ => c * (m + n * (w : ℂ))) ∧
      ∃ (n : (M →+* ℂ) → ℝ) (hn : ∀ s, 0 < n s),
        (∀ s r, IsLieNormSq P v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
        ((-meanLog M n : ℝ) : ℂ) =
          (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / √d) : ℝ) - deriv χ.LFunction 1 / χ.LFunction 1 ∧
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (𝔄 : FractionalIdeal (𝓞 E)⁰ E),
          𝔄 * conjFrac 𝔄 = (differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹ →
          ∀ (L : Type) [Field L] [NumberField L] (j : M →+* L) (τ : E →+* L),
          ((2 * deg (lineHerm (fun s => n (s.comp j)) fun _ => hn _)
              (Submodule.span (𝓞 L) (τ '' (𝔄 * differentIdeal (𝓞 K) (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E))) : ℝ) : ℂ) =
            (Real.eulerMascheroniConstant + Real.log (2 * Real.pi / rootDiscr E) : ℝ)
              - deriv χ.LFunction 1 / χ.LFunction 1 := by
  obtain ⟨M, _, w, P, v, hw, hg, hv, hW, hΛ, hn, hm⟩ := hC d h7 hs h4 K h2 hr
  obtain ⟨r, hr⟩ := hr
  choose n hn0 hn using hn
  exact ⟨M, inferInstance, w, P, v, hw, hg, hv, hW, hΛ, n, hn0, hn,
    chowla_selberg_of_mean_log h2 (discr_eq_neg_of_sq_eq h2 hs h4 hr) (by omega) hχ n hn0
      (hm n fun s => (hn s _).2 rfl)⟩

end Period

end GlobalTheory
