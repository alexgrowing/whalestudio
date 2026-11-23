import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhitGenLowOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.UnrPDifferentiable

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Gen.WL

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory GlobalTheory.Cont PositivityTheory.PfSWUS.Loc PositivityTheory.Rg.Sw Filter
open scoped TensorProduct Matrix Topology

theorem det_mul_eq_zero_of_lt {R : Type*} [CommRing R] {M n : ℕ} (h : M < n)
    (X : Matrix (Fin n) (Fin M) R) (Y : Matrix (Fin M) (Fin n) R) : (X * Y).det = 0 := by
  let e : Matrix (Fin M) (Fin n) R := Matrix.of fun i k => if Fin.castLE h.le i = k then 1 else 0
  have he : e * eᵀ = 1 := by
    ext i j
    simp only [e, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply, ite_mul, one_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, Fin.castLE_inj, eq_comm (a := j)]
  have : X * Y = (X * e) * (eᵀ * Y) := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc e, he, Matrix.one_mul]
  rw [this, Matrix.det_mul, Matrix.det_eq_zero_of_column_eq_zero (A := X * e) ⟨M, h⟩, zero_mul]
  intro a
  simp only [Matrix.mul_apply, e, Matrix.of_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [if_neg, mul_zero]
  intro hh
  have := congrArg Fin.val hh
  simp at this
  omega

theorem densZero {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : M < n) (v : HeightOneSpectrum (𝓞 F))
    (μv : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (νv : Measure (HermR (Fv F v) σ n))
    (Φv : (Fin n → Fin M → Fv F v ⊗[F] E) → ℂ) :
    IsContDensityOn μv (gramR (Fv F v) σ J) Subtype.val νv
      {S | IsUnit (S : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det} Φv 0 := by
  haveI : Nontrivial (Fv F v ⊗[F] E) := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain F
    (Fv F v) E (algebraMap F (Fv F v)).injective (algebraMap F E).injective
  refine ⟨continuousOn_const, fun S _ hS => ?_⟩
  have : gramR (Fv F v) σ J ⁻¹' (Subtype.val '' S) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun X ⟨s, hs, e⟩ => ?_
    have hu := hS hs
    simp only [Set.mem_setOf_eq] at hu
    rw [e] at hu
    let A : Matrix (Fin n) (Fin M) (Fv F v ⊗[F] E) := Matrix.of fun a i => sigR (Fv F v) σ (X a i)
    let B : Matrix (Fin M) (Fin n) (Fv F v ⊗[F] E) := Matrix.of fun i b => ∑ j, JR (Fv F v) J i j * X b j
    have hg : gramR (Fv F v) σ J X = A * B := by
      ext a b
      simp only [gramR, hR, hform, Matrix.mul_apply, A, B, Matrix.of_apply, Finset.mul_sum, mul_assoc]
    rw [hg, det_mul_eq_zero_of_lt h] at hu
    exact not_isUnit_zero hu
  simp [this]

theorem eSp_pow {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (M i : ℕ) : eSp E v ^ (M + i) = eSp E v ^ ((M : ℤ) - (i : ℕ)) := by
  unfold eSp
  split_ifs
  · rw [zpow_sub₀ (by norm_num), zpow_natCast, zpow_natCast, pow_add]
    rcases neg_one_pow_eq_or ℂ i with h | h <;> simp [h, div_neg]
  · simp

theorem count (c d M n : ℕ) (hd : 1 ≤ d) (h : M < n) :
    (∑ i : Fin n, (if 1 ≤ (M : ℤ) - ((i : ℕ) : ℤ) then 0 else if (M : ℤ) - ((i : ℕ) : ℤ) = 0 then c + d - 1 else d)) + 1
      = d * (n - M) + c := by
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ =>
    if 1 ≤ (M : ℤ) - (i : ℤ) then 0 else if (M : ℤ) - (i : ℤ) = 0 then c + d - 1 else d) n]
  obtain ⟨r, rfl⟩ : ∃ r, n = M + 1 + r := ⟨n - M - 1, by omega⟩
  clear h
  induction r with
  | zero =>
    rw [Nat.add_zero, Finset.sum_range_succ, Finset.sum_eq_zero fun i hi => by
      have := Finset.mem_range.1 hi
      rw [if_pos (by omega)]]
    rw [if_neg (by omega), if_pos (by omega)]
    have : M + 1 - M = 1 := by omega
    rw [this, mul_one]
    omega
  | succ r ih =>
    rw [show M + 1 + (r + 1) = M + 1 + r + 1 by ring, Finset.sum_range_succ, add_right_comm, ih]
    rw [if_neg (by omega), if_neg (by omega)]
    have : M + 1 + r + 1 - M = (M + 1 + r - M) + 1 := by omega
    rw [this, Nat.mul_succ]
    ring

theorem analyticAt_update_zero {G A : ℂ → ℂ} {s₀ c : ℂ} {K N : ℕ} (hc : c ≠ 0) (hKN : K < N)
    (hA : AnalyticAt ℂ A s₀) (h : ∀ᶠ z in 𝓝[≠] s₀, c * (z - s₀) ^ K * G z = (z - s₀) ^ N * A z) :
    AnalyticAt ℂ (fun z => if z = s₀ then 0 else G z) s₀ := by
  have hB : AnalyticAt ℂ (fun z => c⁻¹ * ((z - s₀) ^ (N - K) * A z)) s₀ :=
    analyticAt_const.mul ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => (z - s₀) ^ (N - K)) s₀).mul hA)
  refine hB.congr ?_
  filter_upwards [eventually_nhdsWithin_iff.1 h] with z hz
  by_cases hzs : z = s₀
  · subst hzs
    rw [if_pos rfl, sub_self, zero_pow (by omega), zero_mul, mul_zero]
  · rw [if_neg hzs]
    have hx : z - s₀ ≠ 0 := sub_ne_zero.2 hzs
    have h1 := hz hzs
    have hN : (z - s₀) ^ N = (z - s₀) ^ K * (z - s₀) ^ (N - K) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hN] at h1
    have hcc : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
    apply mul_left_cancel₀ (mul_ne_zero hc (pow_ne_zero K hx))
    rw [h1]
    linear_combination ((z - s₀) ^ K * (z - s₀) ^ (N - K) * A z) * hcc

theorem hasProd_split' {α : Type} (f : α → ℂ) (S : Finset α) (D : ℂ)
    (h : HasProd (fun v : {v // v ∉ S} => f v) D) : HasProd f ((∏ v ∈ S, f v) * D) :=
  PositivityTheory.SiegelWeilFormula.Gen.W.hasProd_split f S D h

end PositivityTheory.SiegelWeilFormula.Gen.WL

end
