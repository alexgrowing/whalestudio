import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealGeneratedPrimeToL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonHomIdPow

set_option autoImplicit false

noncomputable section

open NumberField TensorProduct GlobalTheory.RealMult

namespace GlobalTheory.KSSymm

theorem dual_smul_comm {S L : Type*} [CommRing S] [AddCommGroup L] [Module S L] [Module.Invertible S L]
    (ℓ : Module.Dual S L) (x y : L) : ℓ x • y = ℓ y • x := by
  have e := congrArg (fun z ↦ TensorProduct.lid S L (ℓ.rTensor L z))
    (show x ⊗ₜ[S] y = y ⊗ₜ[S] x from Module.Invertible.tmul_comm ..)
  simpa using e

theorem eq_zero_of_coprime {M : Type*} [AddCommGroup M] {x : M}
    (h : ∀ l : ℕ, l.Prime → ∃ n : ℕ, n.Coprime l ∧ n • x = 0) : x = 0 := by
  by_contra hx
  obtain ⟨l, hl, hd⟩ := Nat.exists_prime_and_dvd (n := addOrderOf x) (by rwa [Ne, AddMonoid.addOrderOf_eq_one_iff])
  obtain ⟨n, hn, e⟩ := h l hl
  exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hn.symm (hd.trans (addOrderOf_dvd_of_nsmul_eq_zero e)))

theorem symm_of_casimir {R S L W ι : Type*} [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup L] [Module R L]
    [Module S L] [IsScalarTower R S L] [Module.Invertible S L] [AddCommGroup W] [Module R W] [Fintype ι]
    (e t : ι → S) (τ : S →ₗ[R] R) (n m : ℕ)
    (cas : ∀ (f : S →ₗ[R] R) (s : S), ∑ i, f (s * e i) • t i = s * ∑ i, f (e i) • t i)
    (tr : ∑ i, τ (t i) • e i = n)
    (ρ : S → W → W) (β : W →ₗ[R] L →ₗ[R] R) (hβ : ∀ s f v, β (ρ s f) v = β f (s • v))
    (rad : ∀ f, β f = 0 → m • f = 0) (κ : W →ₗ[R] L) (hκ : ∀ s f, κ (ρ s f) = s • κ f) (f f' : W) :
    (m * n * n) • (β f (κ f') - β f' (κ f)) = 0 := by
  let Φ : W → Module.Dual S L := fun f ↦
    { toFun v := ∑ i, β f (e i • v) • t i
      map_add' := fun v w ↦ by simp only [smul_add, map_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun s v ↦ by
        have := cas (β f ∘ₗ (LinearMap.toSpanSingleton S L v).restrictScalars R) s
        simpa [smul_smul, mul_comm] using this }
  have Φv : ∀ f v, Φ f v = ∑ i, β f (e i • v) • t i := fun _ _ ↦ rfl
  have Φρ : ∀ s f v, Φ (ρ s f) v = s * Φ f v := fun s f v ↦ by
    rw [← smul_eq_mul, ← map_smul]
    simp only [Φv, hβ, smul_comm s]
  have Φsub : ∀ f f' v, Φ (f - f') v = Φ f v - Φ f' v := fun f f' v ↦ by
    simp only [Φv, map_sub, LinearMap.sub_apply, sub_smul, Finset.sum_sub_distrib]
  have τΦ : ∀ f v, τ (Φ f v) = n • β f v := fun f v ↦ by
    have : β f ((∑ i, τ (t i) • e i) • v) = n • β f v := by rw [tr, Nat.cast_smul_eq_nsmul, map_nsmul]
    rw [← this, Φv, Finset.sum_smul, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [smul_assoc, τ.map_smul, (β f).map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  have k : ∀ u, (m * n) • (Φ f u • κ f' - Φ f' u • κ f) = 0 := fun u ↦ by
    have z : β (n • (ρ (Φ f u) f' - ρ (Φ f' u) f)) = 0 := LinearMap.ext fun v ↦ by
      have c := congrArg (Φ f') (dual_smul_comm (Φ f) u v)
      rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at c
      rw [map_nsmul, LinearMap.smul_apply, ← τΦ, Φsub, Φρ, Φρ, c, mul_comm, sub_self, map_zero, LinearMap.zero_apply]
    have := congrArg κ (rad _ z)
    rwa [← mul_smul, map_nsmul, map_sub, hκ, hκ, map_zero] at this
  have k' : ∀ w : Module.Dual S L ⊗[S] L,
      (m * n) • (contractLeft S L w * (Φ f (κ f') - Φ f' (κ f))) = 0 := fun w ↦ by
    induction w with
    | zero => simp
    | add x y hx hy => rw [map_add, add_mul, smul_add, hx, hy, add_zero]
    | tmul ℓ u =>
      have c := congrArg ℓ (k u)
      have c₁ := congrArg (Φ f) (dual_smul_comm ℓ u (κ f'))
      have c₂ := congrArg (Φ f') (dual_smul_comm ℓ u (κ f))
      simp only [map_nsmul, map_sub, map_smul, smul_eq_mul, map_zero] at c c₁ c₂
      rw [contractLeft_apply, mul_sub, c₁, c₂, ← c, mul_comm (ℓ _), mul_comm (ℓ _)]
  obtain ⟨w, hw⟩ := (Module.Invertible.bijective (R := S) (M := L)).2 1
  have := congrArg τ (k' w)
  rwa [hw, one_mul, map_nsmul, map_sub, τΦ, τΦ, map_zero, ← smul_sub, ← mul_smul] at this

theorem exists_form (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] :
    ∃ (n : ℕ) (τ : 𝓞 F →ₗ[ℤ] ℤ) (t : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → 𝓞 F), n.Coprime l ∧
      (∀ i x, τ (t i * x) = n * (RingOfIntegers.basis F).repr x i) ∧ ∀ y, (∀ x, τ (y * x) = 0) → y = 0 := by
  classical
  have h1 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ≠ 0 := one_ne_zero
  let 𝔡 : FracId F := Units.mk0 (FractionalIdeal.dual ℤ ℚ 1) (FractionalIdeal.dual_ne_zero ℤ ℚ h1)
  have mem : ∀ x : F, x ∈ 𝔡.elt ↔ ∀ a : 𝓞 F, ∃ z : ℤ, (z : ℚ) = Algebra.trace ℚ F (x * a) := fun x ↦ by
    refine (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h1).trans ⟨fun h a ↦ ?_, fun h a ha ↦ ?_⟩
    · exact h _ ((FractionalIdeal.mem_one_iff _).2 ⟨a, rfl⟩)
    · obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 ha
      exact h a
  have dual : ∀ i (x : 𝓞 F), Algebra.trace ℚ F ((integralBasis F).traceDual i * x) =
      ((RingOfIntegers.basis F).repr x i : ℚ) := fun i x ↦ by
    conv_lhs => rw [← (RingOfIntegers.basis F).sum_repr x]
    simp only [map_sum, map_zsmul, Finset.mul_sum, mul_smul_comm, ← integralBasis_apply,
      RingOfIntegers.coe_eq_algebraMap, Module.Basis.trace_traceDual_mul]
    simp
  obtain ⟨δ, hδ, hgen⟩ := GlobalTheory.FracGen.exists_gen F 𝔡 l
  obtain ⟨n, -, hn, hu⟩ := GlobalTheory.PolPrimeTo.exists_uniform 𝔡 l δ hgen
  choose τ hτ using (mem δ).1 δ.2
  choose t ht using fun i ↦ hu ⟨(integralBasis F).traceDual i, (mem _).2 fun a ↦ ⟨_, (dual i a).symm⟩⟩
  refine ⟨n, (AddMonoidHom.mk' τ fun a b ↦ Int.cast_injective (α := ℚ) ?_).toIntLinearMap, t, hn,
    fun i x ↦ Int.cast_injective (α := ℚ) ?_, fun y hy ↦ ?_⟩
  · rw [Int.cast_add, hτ, hτ, hτ, ← map_add, ← mul_add]
    simp
  · have e := congrArg Subtype.val (ht i)
    simp only [Submodule.coe_smul, Algebra.smul_def, map_natCast] at e
    change ((τ _ : ℤ) : ℚ) = _
    rw [hτ, Int.cast_mul, ← dual, Int.cast_natCast, ← nsmul_eq_mul, ← map_nsmul, nsmul_eq_mul, ← mul_assoc, e]
    simp [mul_comm, mul_left_comm]
  · have z : (δ : F) * y = 0 := by
      refine (traceForm_nondegenerate ℚ F).1 _ fun x ↦ ?_
      rw [← (integralBasis F).sum_repr x, map_sum]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have e : ((τ (y * RingOfIntegers.basis F i) : ℤ) : ℚ) = 0 := by exact_mod_cast hy _
      rw [hτ] at e
      rw [map_smul, Algebra.traceForm_apply, integralBasis_apply, mul_assoc]
      simpa using Or.inr e
    simpa using (mul_eq_zero.1 z).resolve_left hδ

theorem exists_casimir (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] :
    ∃ (n : ℕ) (e t : Module.Free.ChooseBasisIndex ℤ (𝓞 F) → R ⊗[ℤ] 𝓞 F) (τ : R ⊗[ℤ] 𝓞 F →ₗ[R] R), n.Coprime l ∧
      (∀ (f : R ⊗[ℤ] 𝓞 F →ₗ[R] R) (s : R ⊗[ℤ] 𝓞 F), ∑ i, f (s * e i) • t i = s * ∑ i, f (e i) • t i) ∧
      ∑ i, τ (t i) • e i = n := by
  obtain ⟨n, τ, t, hn, ht, nd⟩ := exists_form F l
  set b := RingOfIntegers.basis F
  have cas : ∀ a j, a * t j = ∑ i, b.repr (a * b i) j • t i := fun a j ↦ sub_eq_zero.1 <| nd _ fun x ↦ by
    rw [sub_mul, map_sub, Finset.sum_mul, map_sum, mul_comm a, mul_assoc, ht, sub_eq_zero]
    conv_lhs => rw [← b.sum_repr x]
    simp only [Finset.mul_sum, map_sum, mul_smul_comm, smul_mul_assoc, map_smul, ht, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  refine ⟨n, fun i ↦ 1 ⊗ₜ b i, fun i ↦ 1 ⊗ₜ t i, (AlgebraTensorModule.rid ℤ R R).toLinearMap ∘ₗ τ.baseChange R, hn,
    fun f s ↦ ?_, ?_⟩
  · induction s with
    | zero => simp
    | add x y hx hy => simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib, hx, hy]
    | tmul r a =>
      have e₁ : ∀ i, (r ⊗ₜ[ℤ] a * (1 : R) ⊗ₜ[ℤ] b i) = r • ∑ j, b.repr (a * b i) j • (1 : R) ⊗ₜ[ℤ] b j := fun i ↦ by
        simp only [← tmul_smul, ← tmul_sum, b.sum_repr]
        simp [smul_tmul']
      have e₂ : ∀ j, (r ⊗ₜ[ℤ] a * (1 : R) ⊗ₜ[ℤ] t j) = r • ∑ i, b.repr (a * b i) j • (1 : R) ⊗ₜ[ℤ] t i := fun j ↦ by
        simp only [← tmul_smul, ← tmul_sum, ← cas]
        simp [smul_tmul']
      simp only [Finset.mul_sum, mul_smul_comm, e₁, e₂, map_smul, map_sum, map_zsmul, Finset.smul_sum,
        Finset.sum_smul, smul_assoc]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [smul_comm (f _), smul_comm (f _)]
  · have e : ∀ i, τ (t i) = n * b.repr 1 i := fun i ↦ by rw [← ht, mul_one]
    have e' : ∑ i, τ (t i) • b i = n := by
      simp only [e, mul_smul, ← Finset.smul_sum, b.sum_repr]
      simp
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul, LinearEquiv.coe_coe, AlgebraTensorModule.rid_tmul,
      smul_assoc, one_smul, ← tmul_smul, ← tmul_sum, e']
    exact map_natCast (Algebra.TensorProduct.includeRight (R := ℤ) (A := R)) n

end GlobalTheory.KSSymm
