import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfForallAlgHomEq
open scoped TensorProduct

namespace GlobalTheory.SymDesc

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]

theorem injective_quotient (Q : Ideal R₁) (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    Function.Injective (algebraMap R (R₁ ⧸ Q)) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  have : r ∈ Q.comap (algebraMap R R₁) := by
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hr
  rwa [hQ, Ideal.mem_bot] at this

theorem exists_sub_mem_of_under_eq_bot [IsIntegrallyClosed R] [CharZero R]
    [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q : Ideal R₁) [Q.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    ∃ e : R, s - algebraMap R R₁ e ∈ Q := by
  classical
  let A := R₁ ⧸ Q
  let K₀ := FractionRing A
  let F := FractionRing R
  have hRA : Function.Injective (algebraMap R A) := injective_quotient Q hQ
  have hRK : Function.Injective (algebraMap R K₀) := by
    rw [IsScalarTower.algebraMap_eq R A K₀]
    exact (IsFractionRing.injective A K₀).comp hRA
  haveI : FaithfulSMul R K₀ := (faithfulSMul_iff_algebraMap_injective R K₀).2 hRK
  letI : Algebra F K₀ := FractionRing.liftAlgebra R K₀
  haveI : IsScalarTower R F K₀ := FractionRing.isScalarTower_liftAlgebra R K₀
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hRA
  haveI : Algebra.IsAlgebraic R A := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R K₀ := (IsFractionRing.isAlgebraic_iff' R A K₀).1 inferInstance
  haveI : Algebra.IsAlgebraic F K₀ :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff R F K₀).1 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  let π : R₁ →+* K₀ := (algebraMap A K₀).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ r : R, π (algebraMap R R₁ r) = algebraMap F K₀ (algebraMap R F r) := by
    intro r
    have hq : (Ideal.Quotient.mk Q) ((algebraMap R R₁) r) = algebraMap R A r := by
      first | rfl | exact Ideal.Quotient.mk_algebraMap _ _ | simp [A]
    simp only [π, RingHom.comp_apply]
    rw [hq, ← IsScalarTower.algebraMap_apply R A K₀, ← IsScalarTower.algebraMap_apply R F K₀]
  obtain ⟨e', he'⟩ := GlobalTheory.mem_range_of_forall_algHom_eq F K₀ inferInstance (π s) (by
    intro Ω _ _ φ₁ φ₂
    have h := hs Ω (φ₁.toRingHom.comp π) (φ₂.toRingHom.comp π) (by
      ext r
      simp only [RingHom.comp_apply, hπ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes])
    simpa using h)
  have hint : IsIntegral R (π s) := by
    have h1 : IsIntegral R (Ideal.Quotient.mk Q s) := Algebra.IsIntegral.isIntegral _
    exact h1.map (IsScalarTower.toAlgHom R A K₀)
  rw [← he'] at hint
  have hint' : IsIntegral R e' :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R F K₀) (algebraMap F K₀).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsFractionRing.injective A K₀
  rw [map_zero]
  have h : π (s - algebraMap R R₁ y) = 0 := by
    rw [map_sub, hπ, hy, he', sub_self]
  exact h

theorem eq_of_sub_mem [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q Q' : Ideal R₁) [Q.IsPrime] [Q'.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥)
    (hQ' : Q'.comap (algebraMap R R₁) = ⊥) (e e' : R) (he : s - algebraMap R R₁ e ∈ Q)
    (he' : s - algebraMap R R₁ e' ∈ Q') : e = e' := by
  classical
  let F := FractionRing R
  let M := AlgebraicClosure F
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R F M]
    exact (algebraMap F M).injective.comp (IsFractionRing.injective R F)
  haveI : FaithfulSMul R M := (faithfulSMul_iff_algebraMap_injective R M).2 hRM
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRM
  have key : ∀ (P : Ideal R₁) [P.IsPrime], P.comap (algebraMap R R₁) = ⊥ →
      ∃ j : R₁ →+* M, j.comp (algebraMap R R₁) = algebraMap R M ∧ ∀ x ∈ P, j x = 0 := by
    intro P _ hP
    have hRA : Function.Injective (algebraMap R (R₁ ⧸ P)) := injective_quotient P hP
    haveI : FaithfulSMul R (R₁ ⧸ P) := (faithfulSMul_iff_algebraMap_injective R _).2 hRA
    haveI : Module.IsTorsionFree R (R₁ ⧸ P) := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRA
    haveI : Algebra.IsAlgebraic R (R₁ ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let l : (R₁ ⧸ P) →ₐ[R] M := IsAlgClosed.lift
    refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_, fun x hx => ?_⟩
    · ext r
      simp only [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
    · simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨j, hj, hj0⟩ := key Q hQ
  obtain ⟨j', hj', hj0'⟩ := key Q' hQ'
  have h := hs M j j' (hj.trans hj'.symm)
  have h1 : j s = algebraMap R M e := by
    have := hj0 _ he
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj]
  have h2 : j' s = algebraMap R M e' := by
    have := hj0' _ he'
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj']
  exact hRM (h1.symm.trans (h.trans h2))

end GlobalTheory.SymDesc

namespace GlobalTheory

theorem exists_eq_algebraMap_of_forall_ringHom_eq : ∀ (R R₁ : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ →
    Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) →
    ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  intro R R₁ _ _ _ _ _ _ hfin hff s hs
  haveI := hfin
  haveI := hff
  haveI : Algebra.IsIntegral R R₁ := Algebra.IsIntegral.of_finite R R₁
  have hinj : Function.Injective (algebraMap R R₁) := FaithfulSMul.algebraMap_injective R R₁
  have hker : Ideal.comap (algebraMap R R₁) (⊥ : Ideal R₁) ≤ ⊥ := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    exact hinj (by rw [hr, map_zero])
  obtain ⟨Q₀, -, hQ₀, hQ₀b⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R) ⊥ hker
  haveI := hQ₀
  obtain ⟨e, he⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q₀ hQ₀b
  refine ⟨e, fun K _ i₁ => ?_⟩
  let P := RingHom.ker i₁
  haveI : P.IsPrime := RingHom.ker_isPrime i₁
  haveI : P.LiesOver (P.under R) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R)) (q := P.under R) P bot_le
  have hQb : Q.comap (algebraMap R R₁) = ⊥ := hQo.over.symm
  obtain ⟨e₁, he₁⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q hQb
  have hee := SymDesc.eq_of_sub_mem s hs Q₀ Q hQ₀b hQb e e₁ he he₁
  subst hee
  have hm : s - algebraMap R R₁ e ∈ P := hQP he₁
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  exact hm

end GlobalTheory
