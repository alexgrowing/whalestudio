import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemLsB
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdealPeriodLatticeOfCurveDatum

open NumberField

open scoped Pointwise

namespace GlobalTheory.VacRead

theorem mul_smul_eq_span_absNorm {K : Type} [Field K] [NumberField K] [IsGalois ℚ K]
    (h2 : Module.finrank ℚ K = 2) (τ : K ≃ₐ[ℚ] K) (hτ : τ ≠ 1) (I : Ideal (𝓞 K)) :
    I * (τ • I) = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} := by
  classical
  by_cases hI : I = ⊥
  · subst hI; simp
  have huniv : (Finset.univ : Finset (K ≃ₐ[ℚ] K)) = {1, τ} := by
    symm; apply Finset.eq_univ_of_card
    rw [Finset.card_pair (Ne.symm hτ), ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h2]
  have hI0 : I ∈ nonZeroDivisors (Ideal (𝓞 K)) := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 K)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have hprin : (I ^ h).IsPrincipal := by
    have h1 : ClassGroup.mk0 (⟨I, hI0⟩ ^ h) = 1 := by rw [map_pow, pow_card_eq_one]
    exact (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨x, hx⟩ := hprin
  have hx' : I ^ h = Ideal.span {x} := hx
  have hτx : τ • (I ^ h) = Ideal.span {τ • x} := by
    rw [hx', Ideal.pointwise_smul_def, Ideal.map_span, Set.image_singleton]
    rfl
  have hnorm : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = x * (τ • x) := by
    have hp : ((Algebra.norm ℤ x : ℤ) : 𝓞 K) = ∏ σ : K ≃ₐ[ℚ] K, σ • x := by
      apply RingOfIntegers.ext
      have h1 := Algebra.norm_eq_prod_automorphisms ℚ (x : K)
      rw [← Algebra.coe_norm_int] at h1
      change algebraMap (𝓞 K) K _ = algebraMap (𝓞 K) K _
      rw [map_prod, map_intCast]
      rw [map_intCast] at h1
      exact h1
    rw [hp, huniv, Finset.prod_pair (Ne.symm hτ), one_smul]
  have key : (I * (τ • I)) ^ h = Ideal.span {((Ideal.absNorm I : ℕ) : 𝓞 K)} ^ h := by
    rw [mul_pow, ← smul_pow', hx', ← hx', hτx, hx', Ideal.span_singleton_mul_span_singleton, ← hnorm,
      Ideal.span_singleton_pow, ← Nat.cast_pow, ← map_pow, hx', Ideal.absNorm_span_singleton]
    rcases Int.natAbs_eq (Algebra.norm ℤ x) with h4 | h4
    · conv_lhs => rw [h4]
      rw [Int.cast_natCast]
    · conv_lhs => rw [h4]
      rw [Int.cast_neg, Ideal.span_singleton_neg, Int.cast_natCast]
  exact pow_left_injective hpos key

theorem hostConj_quadraticGenerator_eq_neg (D : Formalism.BasicNotions.D7) :
    D.host.conj (D.host.sqd) = -D.host.sqd :=
  D.host.conj_sqd

theorem conj_mul_cE_absNorm (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) :
    (∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, ∃ o : 𝓞 D.host.E,
      D.host.conj α * β = (Ideal.absNorm cc : D.host.E) * (o : D.host.E)) ∧
    (Ideal.absNorm cc : D.host.E) ∈ Submodule.span (𝓞 D.host.E)
      {t | ∃ α ∈ GlobalTheory.VacRead.cE D cc, ∃ β ∈ GlobalTheory.VacRead.cE D cc, t = D.host.conj α * β} := by
  classical
  haveI : Algebra.IsQuadraticExtension ℚ D.host.K := ⟨GlobalTheory.CurveLattice.finrank_hostK D⟩
  let τ : D.host.K ≃ₐ[ℚ] D.host.K := D.host.conj.restrictNormal D.host.K
  have hτ : ∀ k : D.host.K, ((τ k : D.host.K) : D.host.E) = D.host.conj (k : D.host.E) :=
    fun k => AlgEquiv.restrictNormal_commutes D.host.conj D.host.K k
  have hτ1 : τ ≠ 1 := by
    intro h1
    have hs : D.host.sqd ∈ D.host.K :=
      IntermediateField.mem_adjoin_simple_self ℚ _
    have h2 := hτ ⟨_, hs⟩
    rw [h1, AlgEquiv.one_apply, hostConj_quadraticGenerator_eq_neg] at h2
    have h3 : D.host.sqd = 0 := by
      have : (2 : D.host.E) * D.host.sqd = 0 := by
        simp only at h2; linear_combination h2
      simpa using this
    have h4 := D.host.sqd_sq
    rw [h3] at h4
    have hd : (D.host.d : D.host.E) ≠ 0 := by exact_mod_cast D.host.hyp.2.1.pos.ne'
    exact hd (by simpa using h4.symm)
  have hI := mul_smul_eq_span_absNorm (GlobalTheory.CurveLattice.finrank_hostK D) τ hτ1 cc

  let iK : 𝓞 D.host.K →+* 𝓞 D.host.E := algebraMap (𝓞 D.host.K) (𝓞 D.host.E)
  have hiK : ∀ k : 𝓞 D.host.K, ((iK k : 𝓞 D.host.E) : D.host.E) = ((k : D.host.K) : D.host.E) := fun k => rfl
  have hsm : ∀ k : 𝓞 D.host.K, (((τ • k : 𝓞 D.host.K) : D.host.K) : D.host.E) = D.host.conj ((k : D.host.K) : D.host.E) :=
    fun k => hτ k
  set N : D.host.E := (Ideal.absNorm cc : D.host.E) with hN
  let M : Submodule (𝓞 D.host.E) D.host.E := Submodule.span (𝓞 D.host.E) {N}
  have hgen : ∀ c₁ ∈ cc, ∀ c₂ ∈ cc, D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) ∈ M := by
    intro c₁ h₁ c₂ h₂
    have hm : c₂ * (τ • c₁) ∈ cc * (τ • cc) := Ideal.mul_mem_mul h₂ (Ideal.smul_mem_pointwise_smul _ _ _ h₁)
    rw [hI, Ideal.mem_span_singleton'] at hm
    obtain ⟨k, hk⟩ := hm
    have hE : D.host.conj ((c₁ : D.host.K) : D.host.E) * ((c₂ : D.host.K) : D.host.E) = (iK k : D.host.E) * N := by
      rw [hiK, ← hsm, mul_comm, hN]
      have := congrArg (fun y : 𝓞 D.host.K => ((y : D.host.K) : D.host.E)) hk
      simp only [map_mul, map_natCast] at this
      push_cast at this ⊢
      rw [← this]
    rw [hE]
    exact Submodule.mem_span_singleton.mpr ⟨iK k, rfl⟩
  have hpart : ∀ α ∈ GlobalTheory.VacRead.cE D cc, ∀ β ∈ GlobalTheory.VacRead.cE D cc, D.host.conj α * β ∈ M := by
    intro α hα β hβ
    induction hα using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨c₁, h₁, rfl⟩ := hx
      have hle : GlobalTheory.VacRead.cE D cc ≤ M.comap (LinearMap.mulLeft (𝓞 D.host.E) (D.host.conj ((c₁ : D.host.K) : D.host.E))) := by
        refine Submodule.span_le.mpr ?_
        rintro y ⟨c₂, h₂, rfl⟩
        exact hgen c₁ h₁ c₂ h₂
      exact hle hβ
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, add_mul]; exact M.add_mem hx hy
    | smul o x _ hx =>
      have : D.host.conj (o • x) * β = (RingOfIntegers.mapRingHom (D.host.conj : D.host.E →+* D.host.E) o) • (D.host.conj x * β) := by
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]
        rfl
      rw [this]
      exact M.smul_mem _ hx
  refine ⟨fun α hα β hβ => ?_, ?_⟩
  · obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.mp (hpart α hα β hβ)
    exact ⟨o, by rw [← ho, Algebra.smul_def, mul_comm]⟩
  · have hNK : ((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) ∈ cc * (τ • cc) := by
      rw [hI]; exact Ideal.mem_span_singleton_self _
    have hcoe : N = ((((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K) : D.host.K) : D.host.E) := by
      rw [hN]; push_cast; rfl
    rw [hcoe]
    refine Submodule.mul_induction_on hNK ?_ ?_
    · intro a ha b hb
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb
      have hb' : b = τ • (τ⁻¹ • b) := by rw [smul_inv_smul]
      refine Submodule.subset_span ⟨((τ⁻¹ • b : 𝓞 D.host.K) : D.host.K), Submodule.subset_span ⟨_, hb, rfl⟩,
        ((a : D.host.K) : D.host.E), Submodule.subset_span ⟨a, ha, rfl⟩, ?_⟩
      conv_lhs => rw [hb']
      rw [← hsm]
      push_cast
      ring
    · intro x y hx hy
      push_cast
      exact Submodule.add_mem _ hx hy

end GlobalTheory.VacRead
