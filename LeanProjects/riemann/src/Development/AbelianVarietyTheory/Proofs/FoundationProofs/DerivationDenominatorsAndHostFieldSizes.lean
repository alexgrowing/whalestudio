import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.NormSum.Denom

theorem norm_le_one {C : Type*} [NormedField C] [IsUltrametricDist C] {x : C}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem norm_natCast (p : ℕ) [Fact p.Prime] {N : ℕ} (hN : N ≠ 0) :
    ‖(N : ℂ_[p])‖ = (p : ℝ) ^ (-(N.factorization p : ℝ)) := by
  have h1 := PadicComplex.norm_extends' p (N : ℚ_[p])
  have h2 : (((N : ℚ_[p]) : PadicAlgCl p) : ℂ_[p]) = (N : ℂ_[p]) := by simp
  have h3 : ‖(N : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p N : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast hN), Padic.valuation_natCast]
  rw [← h2, h1, h3, Nat.factorization_def _ Fact.out, ← Real.rpow_intCast, Int.cast_neg,
    Int.cast_natCast]

variable {E : Type} [Field E] [NumberField E]

def InCodiff (x : E) : Prop := ∀ y : 𝓞 E, ∃ n : ℤ, (n : ℚ) = Algebra.trace ℚ E (x * y)

theorem InCodiff.gal {x : E} (hx : InCodiff x) (σ : E ≃ₐ[ℚ] E) : InCodiff (σ x) := by
  intro y
  obtain ⟨n, hn⟩ := hx ⟨σ.symm y, map_isIntegral_int σ.symm y.isIntegral_coe⟩
  refine ⟨n, hn.trans ?_⟩
  rw [← Algebra.trace_eq_of_algEquiv σ, map_mul]
  congr 2
  exact σ.apply_symm_apply _

theorem InCodiff.mul_different {x : E} (hx : InCodiff x) {a : 𝓞 E}
    (ha : a ∈ differentIdeal ℤ (𝓞 E)) : IsIntegral ℤ ((a : E) * x) := by
  have h1 : (a : E) ∈ IsLocalization.coeSubmodule E (differentIdeal ℤ (𝓞 E)) :=
    (IsLocalization.mem_coeSubmodule E _).2 ⟨a, ha, rfl⟩
  rw [coeSubmodule_differentIdeal ℤ ℚ, Submodule.mem_div_iff_forall_mul_mem] at h1
  have h2 : x ∈ Submodule.traceDual ℤ ℚ (1 : Submodule (𝓞 E) E) := by
    rw [Submodule.mem_traceDual]
    intro b hb
    obtain ⟨y, rfl⟩ := Submodule.mem_one.1 hb
    obtain ⟨n, hn⟩ := hx y
    exact ⟨n, hn⟩
  obtain ⟨z, hz⟩ := Submodule.mem_one.1 (h1 x h2)
  rw [← hz]
  exact z.isIntegral_coe

theorem InCodiff.mul_different_pow {x : E} (hx : InCodiff x) (h : ℕ) :
    ∀ a ∈ differentIdeal ℤ (𝓞 E) ^ h, IsIntegral ℤ ((a : E) * x ^ h) := by
  induction h with
  | zero => intro a _; simpa using a.isIntegral_coe
  | succ h ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha (fun u hu v hv => ?_) (fun u v hu hv => ?_)
    · have := (ih u hu).mul (hx.mul_different hv)
      rw [RingOfIntegers.coe_eq_algebraMap, map_mul, pow_succ, mul_mul_mul_comm]
      exact this
    · have := hu.add hv
      rw [RingOfIntegers.coe_eq_algebraMap, map_add, add_mul]
      exact this

theorem exists_discr_pow_mul_isIntegral [IsGalois ℚ E] :
    ∃ h : ℕ, 0 < h ∧ ∀ x : E, InCodiff x →
      IsIntegral ℤ ((((discr E).natAbs : ℕ) : E) ^ h * x ^ (h * Module.finrank ℚ E)) := by
  have hne : differentIdeal ℤ (𝓞 E) ∈ nonZeroDivisors (Ideal (𝓞 E)) :=
    mem_nonZeroDivisors_iff_ne_zero.2 differentIdeal_ne_bot
  refine ⟨Fintype.card (ClassGroup (𝓞 E)), Fintype.card_pos, fun x hx => ?_⟩
  set h := Fintype.card (ClassGroup (𝓞 E))
  have hpr : (differentIdeal ℤ (𝓞 E) ^ h).IsPrincipal := by
    rw [← ClassGroup.mk0_eq_one_iff (pow_mem hne h)]
    have : (⟨differentIdeal ℤ (𝓞 E) ^ h, pow_mem hne h⟩ : nonZeroDivisors (Ideal (𝓞 E))) =
        ⟨differentIdeal ℤ (𝓞 E), hne⟩ ^ h := rfl
    rw [this, map_pow, pow_card_eq_one]
  obtain ⟨a, ha⟩ := hpr
  have hmem : a ∈ differentIdeal ℤ (𝓞 E) ^ h := by
    rw [ha]; exact Submodule.mem_span_singleton_self a
  have hN : (Algebra.norm ℤ a).natAbs = (discr E).natAbs ^ h := by
    rw [← Ideal.absNorm_span_singleton, ← absNorm_differentIdeal E (𝓞 E), ← map_pow, ha]
  have h1 : ∀ σ : E ≃ₐ[ℚ] E, IsIntegral ℤ (σ (a : E) * x ^ h) := fun σ => by
    have := map_isIntegral_int σ ((hx.gal σ.symm).mul_different_pow h a hmem)
    simpa using this
  have h2 : IsIntegral ℤ (∏ σ : E ≃ₐ[ℚ] E, (σ (a : E) * x ^ h)) :=
    IsIntegral.prod _ fun σ _ => h1 σ
  rw [Finset.prod_mul_distrib, ← Algebra.norm_eq_prod_automorphisms, Finset.prod_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, ← pow_mul, ← Algebra.coe_norm_int] at h2
  rw [← Nat.cast_pow, ← hN]
  have h3 : algebraMap ℚ E ((Algebra.norm ℤ a : ℤ) : ℚ) = ((Algebra.norm ℤ a : ℤ) : E) := by simp
  rw [h3] at h2
  rcases Int.natAbs_eq (Algebra.norm ℤ a) with h4 | h4
  · rw [h4] at h2
    simpa using h2
  · rw [h4] at h2
    have := h2.neg
    simpa using this

theorem InCodiff.norm_le [IsGalois ℚ E] {x : E} (hx : InCodiff x) (p : ℕ) [Fact p.Prime] (ρ : E →+* ℂ_[p]) :
    ‖ρ x‖ ≤ (p : ℝ) ^ (((discr E).natAbs.factorization p : ℝ) / Module.finrank ℚ E) := by
  obtain ⟨h, hh, H⟩ := exists_discr_pow_mul_isIntegral (E := E)
  have h1 := norm_le_one (map_isIntegral_int ρ (H x hx))
  have hd : (discr E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero E)
  rw [map_mul, map_pow, map_pow, map_natCast, norm_mul, norm_pow, norm_pow, norm_natCast p hd, mul_comm h,
    pow_mul, ← mul_pow, pow_le_one_iff_of_nonneg (by positivity) hh.ne'] at h1
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hn : 0 < Module.finrank ℚ E := Module.finrank_pos
  rw [Real.rpow_neg hp.le, inv_mul_le_iff₀ (by positivity), mul_one] at h1
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) hn.ne', ← Real.rpow_mul_natCast hp.le,
    div_mul_cancel₀ _ (by exact_mod_cast hn.ne')]
  exact h1

theorem exists_dual_pair : ∃ (m : ℕ) (w : Fin m → 𝓞 E) (w' : Fin m → E), (∀ k, InCodiff (w' k)) ∧
    ∀ σ τ : E →+* ℂ, ∑ k, τ (w' k) * σ (w k) = if σ = τ then 1 else 0 := by
  let ι := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b := integralBasis E
  let b' := (Algebra.traceForm ℚ E).dualBasis (traceForm_nondegenerate ℚ E) b
  have hb : ∀ i j, Algebra.trace ℚ E (b' i * b j) = if j = i then 1 else 0 := fun i j => by
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_left _ _ _ _
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun k => RingOfIntegers.basis E (e.symm k), fun k => b' (e.symm k), fun k y => ?_,
    fun σ τ => ?_⟩
  · refine ⟨(RingOfIntegers.basis E).repr y (e.symm k), ?_⟩
    have : (y : E) = ∑ j, (RingOfIntegers.basis E).repr y j • b j := by
      conv_lhs => rw [← (RingOfIntegers.basis E).sum_repr y]
      simp [b, integralBasis_apply]
    rw [this, Finset.mul_sum, map_sum]
    simp only [mul_smul_comm, map_zsmul, hb]
    simp
  · let A : Matrix ι (E →ₐ[ℚ] ℂ) ℂ := Matrix.of fun i φ => φ (b' i)
    let B : Matrix (E →ₐ[ℚ] ℂ) ι ℂ := Matrix.of fun φ j => φ (b j)
    have hAB : A * B = 1 := by
      ext i j
      have := trace_eq_sum_embeddings (K := ℚ) (L := E) ℂ (x := b' i * b j)
      rw [hb] at this
      simp only [Matrix.mul_apply, A, B, Matrix.of_apply, ← map_mul, ← this, Matrix.one_apply]
      by_cases hij : i = j
      · simp [hij]
      · simp [hij, Ne.symm hij]
    have hcard : Fintype.card ι = Fintype.card (E →ₐ[ℚ] ℂ) := by
      rw [AlgHom.card, Module.finrank_eq_card_basis b]
    have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv (Fintype.equivOfCardEq hcard)).1 hAB
    have := congrFun (congrFun hBA σ.toRatAlgHom) τ.toRatAlgHom
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply, Matrix.one_apply] at this
    rw [← e.symm.sum_comp] at this
    have h2 : σ.toRatAlgHom = τ.toRatAlgHom ↔ σ = τ :=
      ⟨fun h => RingHom.ext fun x => DFunLike.congr_fun h x, fun h => by rw [h]⟩
    simp only [h2] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [b, integralBasis_apply, mul_comm]

theorem single_mem_YYl (D : D7) (a d : ℕ) (i : Fin d) (j : Fin a) (w : 𝓞 D.host.E) :
    Matrix.single i j (w : D.host.E) ∈ YYl D (stdL D a) (stdL D d) := by
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h1 := D.host.𝔟_spec.1
    rw [h, Ideal.bot_mul] at h1
    exact differentIdeal_ne_bot h1
  refine Submodule.subset_span ⟨1, ?_, Matrix.single i j (w : D.host.E), Submodule.subset_span ?_, by simp⟩
  · have : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤ D.host.AA0 := by
      unfold Host.AA0
      exact one_le_inv₀ (by simpa [pos_iff_ne_zero] using hb) |>.2 FractionalIdeal.coeIdeal_le_one
    exact this (FractionalIdeal.one_mem_one _)
  · intro x hx s _
    have hj : x j ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := hx j trivial
    rw [Matrix.single_mulVec, Function.update_apply]
    split_ifs
    · exact Submodule.smul_mem _ w hj
    · exact Submodule.zero_mem _

theorem exists_letters (D : D7) : ∃ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl := by
  have := D.host.hostE_isGalois
  have hd : (discr D.host.E).natAbs ≠ 0 := Int.natAbs_ne_zero.2 (discr_ne_zero _)
  refine ⟨(discr D.host.E).natAbs.primeFactors,
    fun p => ((discr D.host.E).natAbs.factorization p : ℝ) / Module.finrank ℚ D.host.E,
    fun l hl => Nat.prime_of_mem_primeFactors hl, fun l => by positivity, fun l hl => ?_, le_of_eq ?_, ?_⟩
  · rw [← Nat.support_factorization, Finsupp.notMem_support_iff] at hl
    simp [hl]
  · have h1 : |(discr D.host.E : ℝ)| = ((discr D.host.E).natAbs : ℝ) := by
      rw [Nat.cast_natAbs]; push_cast; rfl
    unfold Host.rdE
    rw [h1, Real.log_rpow (by positivity), Real.log_nat_eq_sum_factorization, Finsupp.sum,
      Nat.support_factorization, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  · intro p _ lam a d k
    obtain ⟨m, w, w', hw', horth⟩ := exists_dual_pair (E := D.host.E)
    have halg : ∀ x, embT D k.1 x ∈ Qbar := fun x =>
      mem_algebraicClosure_iff.2 ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D k.1).toRatAlgHom)
    let φ : D.host.E →+* Qbar := (embT D k.1).codRestrict Qbar halg
    refine ⟨m, fun i => φ (w' i), fun i => Matrix.single k.2.1 k.2.2 (w i : D.host.E),
      fun i => single_mem_YYl D a d _ _ _, fun i => (hw' i).norm_le p (lam.comp φ), ?_⟩
    funext τ s t
    have hinj : embT D τ = embT D k.1 ↔ τ = k.1 :=
      ⟨fun h => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h)), fun h => by rw [h]⟩
    have h2 := horth (embT D τ) (embT D k.1)
    simp only [hinj] at h2
    simp only [coordV, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.single_apply]
    by_cases hst : k.2.1 = s ∧ k.2.2 = t
    · simp only [hst, and_self, if_true, and_true]
      exact h2.symm
    · have : ¬ (τ = k.1 ∧ s = k.2.1 ∧ t = k.2.2) := fun h => hst ⟨h.2.1.symm, h.2.2.symm⟩
      simp [hst, this]

theorem d_le_rd_sq (D : D7) : (D.host.d : ℝ) ≤ D.host.rdE ^ 2 ∧ 0 ≤ D.host.rdE := by
  have h := factRd D.R D.host
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((D.R.e : ℝ) + 1 - (2 : ℝ) ^ (-(D.R.e : ℝ))) := by
    apply Real.one_le_rpow (by norm_num)
    have : (2 : ℝ) ^ (-(D.R.e : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by simp)
    have : (0 : ℝ) ≤ D.R.e := Nat.cast_nonneg _
    linarith
  have hd : (0 : ℝ) ≤ D.host.d := Nat.cast_nonneg _
  have h2 : Real.sqrt (D.host.d : ℝ) ≤ D.host.rdE :=
    (le_mul_of_one_le_left (Real.sqrt_nonneg _) h1).trans h.1
  have h3 := Real.sq_sqrt hd
  have h4 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
  exact ⟨h3 ▸ h4, (Real.sqrt_nonneg _).trans h2⟩

end GlobalTheory.NormSum.Denom

namespace GlobalTheory.NormSum

theorem letters_and_sizes : ∀ (D : D7), admG1 D → (∃ (S : Finset ℕ) (dl : ℕ → ℝ), Letters D S dl) ∧ Real.log D.host.d ≤ 2 * Real.log D.host.rdE ∧ 1 ≤ D.host.rdE ∧ 1 ≤ fF D ∧ Fintype.card D.what₂.Tau = fF D ∧ Module.finrank ℚ D.host.E = 2 * fF D := by
  intro D _
  obtain ⟨h1, h0⟩ := Denom.d_le_rd_sq D
  have hd : (1 : ℝ) ≤ D.host.d := by exact_mod_cast D.host.hyp.2.1.one_le
  refine ⟨Denom.exists_letters D, ?_, by nlinarith, ?_, D.what₂.card_Tau, ?_⟩
  · have := Real.log_le_log (by linarith) h1
    rw [Real.log_pow] at this
    exact_mod_cast this
  · unfold fF Ranks.f Ranks.n
    have := D.R.ord_pos
    omega
  · rw [D.host.finrank_cmField]
    unfold fF Ranks.f Ranks.n
    ring

end GlobalTheory.NormSum
