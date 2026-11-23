import Formalism.LagrangeIdealLifts.Statement

namespace Formalism.LIFT

theorem gammaGradedStep_holds : GradedStep := by
  intro ℓ _ A _ _ B M D _ _ _ _ W i n hn
  obtain ⟨t, ht⟩ := B.γX
  obtain ⟨n', hn', hγ⟩ := W.γ_N n hn
  have hw : ∀ k : ℕ, ∃ r : A, (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ k
      = algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) + B.X * r := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨r, hr⟩ := ih
      refine ⟨r * (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t)
        + algebraMap ℤ_[ℓ] A ((B.u : ℤ_[ℓ]) ^ k) * t, ?_⟩
      rw [pow_succ, hr, pow_succ, map_mul]; ring
  obtain ⟨r, hr⟩ := hw i
  have hγn : W.γ n = n + B.X • n' := by rw [← hγ]; abel
  refine ⟨r • n + (algebraMap ℤ_[ℓ] A (B.u : ℤ_[ℓ]) + B.X * t) ^ i • n', ?_, ?_⟩
  · exact W.N.add_mem (W.N.smul_mem _ hn) (W.N.smul_mem _ hn')
  · rw [W.γ_smul, map_pow, ht, mul_pow, hγn, hr,
      ← algebraMap_smul A ((B.u : ℤ_[ℓ]) ^ i) (B.X ^ i • n)]
    module

theorem uGraded_of (h : GradedStep) : UGraded := by
  intro ℓ _ A _ _ B M D _ _ _ _ W K
  induction K with
  | zero =>
    intro n hn
    exact ⟨0, W.N.zero_mem, n, hn, by simp⟩
  | succ K ih =>
    intro n hn
    obtain ⟨x, hx, n', hn', he⟩ := ih n hn
    obtain ⟨n'', hn'', hg⟩ := h ℓ A B M D W (K + 1) n' hn'
    refine ⟨((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n', ?_, -n'', W.N.neg_mem hn'', ?_⟩
    · exact W.N.add_mem (Submodule.smul_of_tower_mem _ _ hx) (W.N.smul_mem _ hn')
    · rw [Finset.prod_Icc_succ_top (by omega), mul_comm, mul_smul, he]
      have e1 : B.X • (((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • x + B.X ^ K • n')
          = ((B.u : ℤ_[ℓ]) ^ (K + 1) - 1) • (B.X • x) + B.X ^ (K + 1) • n' := by
        rw [smul_add, smul_comm, ← mul_smul, ← pow_succ']
      rw [e1, LinearMap.map_add, LinearMap.map_smul]
      have e2 : W.γ (B.X ^ (K + 1) • n') = ((B.u : ℤ_[ℓ]) ^ (K + 1)) • (B.X ^ (K + 1) • n')
          + B.X ^ (K + 1 + 1) • n'' := by rw [← hg]; abel
      rw [e2]
      simp only [sub_smul, one_smul, smul_add, smul_sub, smul_neg]
      abel

namespace GradedDegree

variable {ℓ : ℕ} [Fact ℓ.Prime] {A : Type} [CommRing A] [Algebra ℤ_[ℓ] A] {B : Base ℓ A} {M : ℕ}

theorem X_pow_inj {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (k : ℕ) (x : D) (h : B.X ^ k • x = 0) : x = 0 := by
  induction k generalizing x with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply W.X_inj
    rw [← mul_smul, ← pow_succ']
    exact h

theorem aeval_mul_X {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (p : Polynomial ℤ_[ℓ]) : Polynomial.aeval g (p * Polynomial.X) = Polynomial.aeval g p * g := by
  rw [map_mul, Polynomial.aeval_X]

theorem aeval_mem {D : Type} [AddCommGroup D] [Module ℤ_[ℓ] D] (g : D →ₗ[ℤ_[ℓ]] D)
    (S : D → Prop) (hadd : ∀ x y, S x → S y → S (x + y))
    (hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x)) (hg : ∀ x, S x → S (g x))
    (p : Polynomial ℤ_[ℓ]) : ∀ x, S x → S (Polynomial.aeval g p x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x hx
    rw [Polynomial.aeval_C, Module.algebraMap_end_apply]
    exact hsmul c x hx
  · intro p q hp hq x hx
    rw [map_add, LinearMap.add_apply]
    exact hadd _ _ (hp x hx) (hq x hx)
  · intro k c h x hx
    rw [pow_succ, ← mul_assoc, aeval_mul_X, Module.End.mul_apply]
    exact h _ (hg x hx)

theorem hom_aeval {D D' : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] [AddCommGroup D'] [Module A D'] [Module ℤ_[ℓ] D']
    [IsScalarTower ℤ_[ℓ] A D'] {W : WD B M D} {W' : WD B M D'} (f : Hom W W')
    (p : Polynomial ℤ_[ℓ]) : ∀ x, f.f (Polynomial.aeval W.γ p x) = Polynomial.aeval W'.γ p (f.f x) := by
  refine Polynomial.induction_on p ?_ ?_ ?_
  · intro c x
    rw [Polynomial.aeval_C, Polynomial.aeval_C, Module.algebraMap_end_apply,
      Module.algebraMap_end_apply, LinearMap.map_smul_of_tower]
  · intro p q hp hq x
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  · intro k c h x
    rw [pow_succ, ← mul_assoc, aeval_mul_X, aeval_mul_X, Module.End.mul_apply,
      Module.End.mul_apply, h, f.γ_comm]

theorem graded_prod (hG : GradedStep) {D : Type} [AddCommGroup D] [Module A D] [Module ℤ_[ℓ] D]
    [IsScalarTower ℤ_[ℓ] A D] (W : WD B M D) (i j : ℕ) (hij : i ≤ j) :
    ∀ m ∈ W.N, ∃ m' ∈ W.N, Polynomial.aeval W.γ
      (∏ k ∈ Finset.Ico i j, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ k))) (B.X ^ i • m)
        = B.X ^ j • m' := by
  induction j, hij using Nat.le_induction with
  | base => intro m hm; exact ⟨m, hm, by simp⟩
  | succ j hij ih =>
    intro m hm
    obtain ⟨m', hm', he⟩ := ih m hm
    obtain ⟨m'', hm'', hg⟩ := hG ℓ A B M D W j m' hm'
    refine ⟨m'', hm'', ?_⟩
    rw [Finset.prod_Ico_succ_top hij, mul_comm, map_mul, Module.End.mul_apply, he, map_sub,
      Polynomial.aeval_X, Polynomial.aeval_C, LinearMap.sub_apply, Module.algebraMap_end_apply, hg]

end GradedDegree

open GradedDegree in
theorem wBTail_of (hG : GradedStep) (hL : LagrangeIdealCyc) : WBTail := by
  intro ℓ _ A _ _ B M D₁ D₂ _ _ _ _ _ _ _ _ W₁ W₂ f s a hs hs2 hv hX n hn
  obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp (hL ℓ B.u s hs hs2 hv a)
  let S : D₂ → Prop := fun y => ∃ m ∈ W₁.N, y = f.f (B.X ^ a • m)
  have hadd : ∀ x y, S x → S y → S (x + y) := by
    rintro x y ⟨m, hm, rfl⟩ ⟨m', hm', rfl⟩
    exact ⟨m + m', W₁.N.add_mem hm hm', by rw [smul_add, map_add]⟩
  have hsmul : ∀ (c : ℤ_[ℓ]) x, S x → S (c • x) := by
    rintro c x ⟨m, hm, rfl⟩
    exact ⟨c • m, Submodule.smul_of_tower_mem _ _ hm,
      by rw [smul_comm (B.X ^ a) c m]; exact (LinearMap.map_smul_of_tower f.f c _).symm⟩
  have hγS : ∀ x, S x → S (W₂.γ x) := by
    rintro x ⟨m, hm, rfl⟩
    obtain ⟨m', hm', hg⟩ := hG ℓ A B M D₁ W₁ a m hm
    refine ⟨((B.u : ℤ_[ℓ]) ^ a) • m + B.X • m',
      W₁.N.add_mem (Submodule.smul_of_tower_mem _ _ hm) (W₁.N.smul_mem _ hm'), ?_⟩
    have e : W₁.γ (B.X ^ a • m) = ((B.u : ℤ_[ℓ]) ^ a) • (B.X ^ a • m) + B.X ^ (a + 1) • m' := by
      rw [← hg]; abel
    rw [← f.γ_comm, e, smul_add, smul_comm (B.X ^ a) ((B.u : ℤ_[ℓ]) ^ a) m, ← mul_smul, ← pow_succ]
  obtain ⟨m, hm, hfm⟩ := hX n hn
  have hP₁ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.range a, (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i))) (B.X ^ a • n)) := by
    obtain ⟨m₁, hm₁, h1⟩ := graded_prod hG W₁ 0 a (Nat.zero_le a) m hm
    rw [← Finset.range_eq_Ico, pow_zero, one_smul] at h1
    exact ⟨m₁, hm₁, by rw [← hfm, ← hom_aeval, h1]⟩
  have hP₂ : S (Polynomial.aeval W₂.γ
      (∏ i ∈ Finset.Ico a (2 * a), (Polynomial.X - Polynomial.C ((B.u : ℤ_[ℓ]) ^ i)))
        (B.X ^ a • n)) := by
    obtain ⟨n₂, hn₂, h2⟩ := graded_prod hG W₂ a (2 * a) (by omega) n hn
    obtain ⟨m₂, hm₂, hfm₂⟩ := hX n₂ hn₂
    exact ⟨m₂, hm₂, by rw [h2, LinearMap.map_smul, hfm₂, ← mul_smul, ← pow_add, two_mul]⟩
  have key : S (Polynomial.aeval W₂.γ (Polynomial.C ((ℓ : ℤ_[ℓ]) ^
      (2 * a * s + padicValNat ℓ (2 * a).factorial))) (B.X ^ a • n)) := by
    rw [← hαβ, map_add, map_mul, map_mul, LinearMap.add_apply, Module.End.mul_apply,
      Module.End.mul_apply]
    exact hadd _ _ (aeval_mem W₂.γ S hadd hsmul hγS α _ hP₁)
      (aeval_mem W₂.γ S hadd hsmul hγS β _ hP₂)
  rw [Polynomial.aeval_C, Module.algebraMap_end_apply] at key
  obtain ⟨m₃, hm₃, h3⟩ := key
  refine ⟨m₃, hm₃, ?_⟩
  have h0 := X_pow_inj W₂ a (f.f m₃ - ((ℓ : ℤ_[ℓ]) ^ (2 * a * s + padicValNat ℓ (2 * a).factorial)) • n)
    (by rw [smul_sub, ← LinearMap.map_smul, smul_comm (B.X ^ a), ← h3, sub_self])
  exact sub_eq_zero.mp h0

end Formalism.LIFT
