import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

namespace GlobalTheory.TorFin

theorem pow_mul_mem_of_mul_mem {A : Type} [Ring A] [Algebra ℂ A] {I : Submodule ℂ A} {H : A}
    (hH : ∀ i ∈ I, H * i ∈ I) (m : ℕ) {x : A} (hx : x ∈ I) : H ^ m * x ∈ I := by
  induction m with
  | zero => simpa using hx
  | succ m ih => rw [pow_succ', mul_assoc]; exact hH _ ih

theorem finiteDimensional_span_pow_mul_pow :
    ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W]
      (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' →
      (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) →
      IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) →
      (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) →
      FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) := by
  intro A U W _ _ _ _ _ _ Z I H H' κ Λ hc hHI hH'I hIZ hΛ ⟨N, hN⟩ ⟨N', hN'⟩ hfin hker
  set K : Submodule ℂ A := Subalgebra.toSubmodule Z with hK
  let κK : K →ₗ[ℂ] U := κ ∘ₗ K.subtype
  let f : ℕ × ℕ → K →ₗ[ℂ] W := fun p => Λ ∘ₗ LinearMap.mulLeft ℂ (H ^ p.1 * H' ^ p.2) ∘ₗ K.subtype
  have hle : ∀ p, LinearMap.ker κK ≤ LinearMap.ker (f p) := by
    intro p z hz
    simp only [LinearMap.mem_ker] at hz ⊢
    exact hker z.1 z.2 hz _
  have hQ : Module.Finite ℂ (K ⧸ LinearMap.ker κK) := by
    have hr : LinearMap.range κK = K.map κ := by
      simp [κK, LinearMap.range_comp, Submodule.range_subtype]
    haveI : Module.Finite ℂ (LinearMap.range κK) := by rw [hr]; exact hfin
    exact Module.Finite.equiv (κK.quotKerEquivRange).symm
  have hfp : ∀ p, Module.Finite ℂ (LinearMap.range (f p)) := by
    intro p
    rw [← Submodule.range_liftQ _ (f p) (hle p)]
    exact Module.Finite.range _
  let V : Submodule ℂ W := ⨆ p : Fin N × Fin N', LinearMap.range (f (p.1.1, p.2.1))
  haveI : Module.Finite ℂ V := by
    haveI := fun p : Fin N × Fin N' => hfp (p.1.1, p.2.1)
    infer_instance
  have hbase : ∀ i j, i < N → j < N' → ∀ z ∈ Z, Λ (H ^ i * H' ^ j * z) ∈ V := by
    intro i j hi hj z hz
    refine Submodule.mem_iSup_of_mem (⟨i, hi⟩, ⟨j, hj⟩) ⟨⟨z, hz⟩, ?_⟩
    simp [f, mul_assoc]
  have main : ∀ n i j, i + j ≤ n → ∀ z ∈ Z, Λ (H ^ i * H' ^ j * z) ∈ V := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro i j hij z hz
    by_cases hi : N ≤ i
    · obtain ⟨ι, hι, s, hs, hsum⟩ := Submodule.mem_sup.1 hN
      have e : H ^ i * H' ^ j * z = H ^ (i - N) * (H' ^ j * (ι * z)) + H ^ (i - N) * H' ^ j * s * z := by
        rw [← pow_sub_mul_pow H hi, mul_assoc (H ^ (i - N)), (hc.pow_pow N j).eq, ← hsum]
        simp only [mul_add, add_mul, mul_assoc]
      rw [e, map_add, hΛ _ (pow_mul_mem_of_mul_mem hHI _ (pow_mul_mem_of_mul_mem hH'I _ (hIZ _ hι _ hz))), zero_add]
      clear e hsum
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, hk, zk, hzk, rfl⟩ := hx
        have e2 : H ^ (i - N) * H' ^ j * (H ^ k * zk) * z = H ^ (i - N + k) * H' ^ j * (zk * z) := by
          calc H ^ (i - N) * H' ^ j * (H ^ k * zk) * z = H ^ (i - N) * (H' ^ j * H ^ k) * (zk * z) := by
                simp only [mul_assoc]
            _ = H ^ (i - N) * (H ^ k * H' ^ j) * (zk * z) := by rw [(hc.pow_pow k j).eq]
            _ = _ := by rw [pow_add]; simp only [mul_assoc]
        rw [e2]
        exact ih (i - N + k + j) (by omega) _ _ le_rfl _ (Z.mul_mem hzk hz)
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul, map_add]; exact V.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, map_smul]; exact V.smul_mem c hx
    by_cases hj : N' ≤ j
    · obtain ⟨ι, hι, s, hs, hsum⟩ := Submodule.mem_sup.1 hN'
      have e : H ^ i * H' ^ j * z = H ^ i * (H' ^ (j - N') * (ι * z)) + H ^ i * H' ^ (j - N') * s * z := by
        rw [← pow_sub_mul_pow H' hj, ← hsum]
        simp only [mul_add, add_mul, mul_assoc]
      rw [e, map_add, hΛ _ (pow_mul_mem_of_mul_mem hHI _ (pow_mul_mem_of_mul_mem hH'I _ (hIZ _ hι _ hz))), zero_add]
      clear e hsum
      induction hs using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨k, hk, zk, hzk, rfl⟩ := hx
        have e2 : H ^ i * H' ^ (j - N') * (H' ^ k * zk) * z = H ^ i * H' ^ (j - N' + k) * (zk * z) := by
          rw [pow_add]; simp only [mul_assoc]
        rw [e2]
        exact ih (i + (j - N' + k)) (by omega) _ _ le_rfl _ (Z.mul_mem hzk hz)
      | zero => simp
      | add x y _ _ hx hy => rw [mul_add, add_mul, map_add]; exact V.add_mem hx hy
      | smul c x _ hx => rw [mul_smul_comm, smul_mul_assoc, map_smul]; exact V.smul_mem c hx
    exact hbase i j (by omega) (by omega) z hz
  apply Submodule.finiteDimensional_of_le (S₂ := V)
  rw [Submodule.span_le]
  rintro _ ⟨⟨i, j⟩, rfl⟩
  simpa using main (i + j) i j le_rfl 1 Z.one_mem

example : ∀ (A U W : Type) [Ring A] [Algebra ℂ A] [AddCommGroup U] [Module ℂ U] [AddCommGroup W] [Module ℂ W] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H H' : A) (κ : A →ₗ[ℂ] U) (Λ : A →ₗ[ℂ] W), Commute H H' → (∀ i ∈ I, H * i ∈ I) → (∀ i ∈ I, H' * i ∈ I) → (∀ i ∈ I, ∀ z ∈ Z, i * z ∈ I) → (∀ i ∈ I, Λ i = 0) → IsIntMod Z I H → IsIntMod Z I H' → FiniteDimensional ℂ ((Subalgebra.toSubmodule Z).map κ) → (∀ z ∈ Z, κ z = 0 → ∀ T, Λ (T * z) = 0) → FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun p : ℕ × ℕ => Λ (H ^ p.1 * H' ^ p.2))) :=
  finiteDimensional_span_pow_mul_pow

end GlobalTheory.TorFin
