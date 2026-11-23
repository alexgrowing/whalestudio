import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslateMomentsAll
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SpanImageLeOf
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StarDetMulDetMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowPrincipal
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MaxVDetLat
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

noncomputable section

namespace GlobalTheory.MomT.ChiUnit

open GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation

theorem norm_integer_le {E K : Type} [Field E] [NumberField E] [NormedField K] [IsUltrametricDist K] (ψ : E →+* K) (r : 𝓞 E) :
    ‖ψ r‖ ≤ 1 := by
  have h : IsIntegral ℤ (ψ r) := (r.isIntegral_coe).map ψ.toIntAlgHom
  by_contra H
  push Not at H
  obtain ⟨f, hf, e⟩ := h
  rw [hf.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finsetSum] at e
  have e2 := congrArg norm (eq_neg_of_add_eq_zero_left e)
  rw [norm_neg, norm_pow] at e2
  rcases Nat.eq_zero_or_pos f.natDegree with h0 | h0
  · simp [h0] at e2
  · have := IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (s := Finset.range f.natDegree)
      (f := fun i => Polynomial.eval₂ (algebraMap ℤ K) (ψ r) (Polynomial.C (f.coeff i) * Polynomial.X ^ i))
      (C := ‖ψ r‖ ^ (f.natDegree - 1)) (by positivity) (fun i hi => by
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow, norm_mul, norm_pow]
        have h1 : ‖algebraMap ℤ K (f.coeff i)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one _ _
        have h2 : ‖ψ r‖ ^ i ≤ ‖ψ r‖ ^ (f.natDegree - 1) :=
          pow_le_pow_right₀ H.le (by have := Finset.mem_range.1 hi; omega)
        calc _ ≤ 1 * _ := mul_le_mul h1 h2 (by positivity) zero_le_one
          _ = _ := one_mul _)
    rw [← e2] at this
    exact absurd this (not_le.2 (pow_lt_pow_right₀ H (by omega)))

theorem exists_prime_under {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ψ : E →+* ℂ_[p]) :
    ∃ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal ∧ ∀ r : 𝓞 E, r ∉ P.asIdeal → ‖ψ r‖ = 1 := by
  let I : Ideal (𝓞 E) :=
    { carrier := {r | ‖ψ r‖ < 1}
      add_mem' := fun {a b} ha hb => by
        show ‖ψ ((a + b : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_add, map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ha hb)
      zero_mem' := by
        show ‖ψ ((0 : 𝓞 E) : E)‖ < 1
        simp
      smul_mem' := fun c a ha => by
        show ‖ψ ((c * a : 𝓞 E) : E)‖ < 1
        rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul]
        exact (mul_le_of_le_one_left (norm_nonneg _) (norm_integer_le ψ c)).trans_lt ha }
  have hI : ∀ r, r ∈ I ↔ ‖ψ r‖ < 1 := fun _ => Iff.rfl
  have h1 : ∀ r, r ∉ I → ‖ψ r‖ = 1 := fun r hr =>
    le_antisymm (norm_integer_le ψ r) (not_lt.1 hr)
  have hp : (p : 𝓞 E) ∈ I := by
    rw [hI, RingOfIntegers.coe_eq_algebraMap, map_natCast, map_natCast, ← map_natCast (algebraMap ℚ_[p] ℂ_[p]),
      norm_algebraMap']
    exact Padic.norm_p_lt_one
  refine ⟨⟨I, ⟨?_, fun {a b} hab => ?_⟩, ?_⟩, hp, h1⟩
  · rw [Ideal.ne_top_iff_one, hI]
    simp
  · by_contra H
    push Not at H
    rw [hI, RingOfIntegers.coe_eq_algebraMap, map_mul, map_mul, norm_mul] at hab
    have ha := h1 a H.1
    have hb := h1 b H.2
    rw [RingOfIntegers.coe_eq_algebraMap] at ha hb
    rw [ha, hb] at hab
    simp at hab
  · intro h
    rw [h, Ideal.mem_bot] at hp
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast hp)

theorem norm_eq_one_of_val {E : Type} [Field E] [NumberField E] {p : ℕ} [Fact p.Prime] (ψ : E →+* ℂ_[p]) {y : E}
    (hy : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → P.valuation E y = 1) : ‖ψ y‖ = 1 := by
  obtain ⟨P, hP, h1⟩ := exists_prime_under ψ
  have key : ∀ x : E, IntAt P x → ‖ψ x‖ ≤ 1 := by
    rintro x ⟨r, s, hs, e⟩
    have := congrArg (fun z => ‖ψ z‖) e
    have h2 := h1 s hs
    rw [RingOfIntegers.coe_eq_algebraMap] at h2
    simp only [map_mul, norm_mul, h2, one_mul] at this
    rw [this]
    exact norm_integer_le ψ r
  have hv := hy P hP
  have h0 : y ≠ 0 := by rintro rfl; simp at hv
  obtain ⟨a, b⟩ := (GlobalTheory.CharValCompare.val_eq_one_iff h0).1 hv
  have hb := key _ b
  rw [map_inv₀, norm_inv, inv_le_one₀ (norm_pos_iff.2 (by simpa using h0))] at hb
  exact le_antisymm (key _ a) hb

variable {D : D7} {X : Fields} {s : Seam D X} {χ : TaylorLogMetric.IdE D → ℂ}

theorem symm_conj (hs : s.Ok) (x : D.host.E) : s.iE.symm (D.host.conj x) = star (s.iE.symm x) := by
  apply s.iE.injective
  rw [hs.2, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

theorem normOne_idTo (hs : s.Ok) {I J : Submodule (𝓞 X.E) X.E} (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    TaylorLogMetric.N1 D (idTo s I) := by
  obtain ⟨t1, t2, t3, -⟩ := GlobalTheory.IdealTransport.transport D X s
  exact ⟨idTo s J, fun x => by rw [t1, t1, h1, symm_conj hs], by rw [← t2, h2, t3]⟩

theorem chi_span (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {y : X.E} (hy : star y * y = 1) :
    χ (idTo s (Submodule.span (𝓞 X.E) {y})) = ∏ τ, (s.σ₀ (X.emb τ y))⁻¹ := by
  obtain ⟨-, -, -, t4, -⟩ := GlobalTheory.IdealTransport.transport D X s
  letI := D.host.cmStar
  have hst : star (s.iE y) = s.iE (star y) := by
    apply D.host.φ₀.injective
    rw [hs.2]
    change D.host.φ₀ (@NumberField.IsCMField.complexConj D.host.E _ _
      (D.host.isCMField_hostE) _ (s.iE y)) = _
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply]
  have hu : s.iE y ∈ unitary D.host.E := by
    rw [Unitary.mem_iff, mul_comm (s.iE y), and_self, hst, ← map_mul, hy, map_one]
  have := hχ.2 ⟨_, hu⟩
  rw [t4, this, ← s.iT.prod_comp]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [hs.1]

theorem chi_pow (hs : s.Ok) (hχ : TaylorLogMetric.IsChi D χ) {I J : Submodule (𝓞 X.E) X.E}
    (h1 : ∀ x, x ∈ J ↔ star x ∈ I) (h2 : I * J = 1) :
    ∃ (h : ℕ) (y : X.E), 0 < h ∧ star y * y = 1 ∧ Submodule.span (𝓞 X.E) {y} = I ^ h ∧
      χ (idTo s I) ^ h = ∏ τ, (s.σ₀ (X.emb τ y))⁻¹ := by
  obtain ⟨c1, h, y, hh, hy, hyI⟩ := GlobalTheory.NormOneIdeal.pow_eq_span_norm_one X.E I J h1 h2
  obtain ⟨-, t2, -⟩ := GlobalTheory.IdealTransport.transport D X s
  have hn : ∀ n : ℕ, TaylorLogMetric.N1 D (idTo s (I ^ n)) := fun n => normOne_idTo hs (c1 n) (by rw [← mul_pow, h2, one_pow])
  have hp : ∀ n : ℕ, χ (idTo s (I ^ n)) = χ (idTo s I) ^ n := by
    intro n
    induction n with
    | zero =>
      rw [pow_zero, pow_zero, Submodule.one_eq_span, chi_span hs hχ (by simp)]
      simp
    | succ n ih => rw [pow_succ, pow_succ, t2, hχ.1 _ _ (hn n) (normOne_idTo hs h1 h2), ih]
  exact ⟨h, y, hh, hy, hyI, by rw [← chi_span hs hχ hy, hyI, hp]⟩

theorem map_mem_Qbar {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) (x : E) : φ x ∈ TaylorLogMetric.Qbar :=
  mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom φ.toRatAlgHom)

theorem chi_det_unit : ∀ (D : D7) (X : Fields) (s : Seam D X) (χ : TaylorLogMetric.IdE D → ℂ) (p : ℕ) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ϖ : 𝓞 X.E) (n : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → s.Ok → TaylorLogMetric.IsChi D χ → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsSdLat N → (∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → localization₂ P.asIdeal N = stdAt X.E n P) → χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)) ∈ TaylorLogMetric.Qbar ∧ ‖TaylorLogMetric.lamC lam (χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D n) (s.lat N)))‖ = 1 := by
  intro D X s χ p _ lam ϖ n N _ hs hχ hϖ hN hS
  obtain ⟨-, -, -, -, -, t6⟩ := GlobalTheory.IdealTransport.transport D X s
  rw [t6]
  obtain ⟨J, h1, h2⟩ := GlobalTheory.DetSelfDual.detLat_mul_conj X.E n N hN
  obtain ⟨h, y, hh, hy, hyI, e⟩ := chi_pow hs hχ h1 h2
  have hv1 : ∀ P : HeightOneSpectrum (𝓞 X.E), ϖ ∈ P.asIdeal → P.valuation X.E y = 1 := by
    intro P hP
    have h3 : MaxV P (detLat N) 1 := by
      have := GlobalTheory.CharVal.DetFrame.maxV_detLat X.E n N P 1 (fun x => by rw [hS P hP]; rfl)
      simpa using this
    have := h3.pow h
    rw [← hyI, one_pow] at this
    exact (maxV_span_singleton y).unique this
  have hv : ∀ P : HeightOneSpectrum (𝓞 X.E), (p : 𝓞 X.E) ∈ P.asIdeal → P.valuation X.E y = 1 := by
    intro P hP
    rw [← hϖ] at hP
    rcases P.isPrime.mem_or_mem hP with hP | hP
    · exact hv1 P hP
    · have := GlobalTheory.CharValCompare.val_star_eq_one (hv1 (conjPrime₂ P) ((mem_conjP P ϖ).2 hP))
      rw [GlobalTheory.CharValCompare.conjP_conjP] at this
      have h4 := congrArg (P.valuation X.E) hy
      rwa [map_mul, this, one_mul, map_one] at h4
  let φ : X.Tau → X.E →+* TaylorLogMetric.Qbar := fun τ =>
    (s.σ₀.comp (X.emb τ)).codRestrict TaylorLogMetric.Qbar (map_mem_Qbar (s.σ₀.comp (X.emb τ)))
  have e' : χ (idTo s (detLat N)) ^ h = ((∏ τ, (φ τ y)⁻¹ : TaylorLogMetric.Qbar) : ℂ) := by
    rw [e]
    simp [φ]
  have hmem : χ (idTo s (detLat N)) ∈ TaylorLogMetric.Qbar := by
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hh ?_)
    rw [e']
    exact mem_algebraicClosure_iff.1 (Subtype.prop _)
  refine ⟨hmem, ?_⟩
  rw [TaylorLogMetric.lamC, dif_pos hmem]
  have e2 : (⟨_, hmem⟩ : TaylorLogMetric.Qbar) ^ h = ∏ τ, (φ τ y)⁻¹ := Subtype.ext (by rw [← e']; simp)
  have e3 := congrArg (fun z => ‖lam z‖) e2
  simp only [map_pow, norm_pow, map_prod, norm_prod, map_inv₀, norm_inv] at e3
  rw [Finset.prod_eq_one (fun τ _ => by
    have := norm_eq_one_of_val (lam.comp (φ τ)) hv
    rw [RingHom.comp_apply] at this
    rw [this, inv_one])] at e3
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hh.ne').1 e3

end GlobalTheory.MomT.ChiUnit
