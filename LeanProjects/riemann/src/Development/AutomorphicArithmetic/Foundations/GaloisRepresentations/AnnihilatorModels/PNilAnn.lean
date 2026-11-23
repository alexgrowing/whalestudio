import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

section
variable {F B : Type} [Field F] [AddCommGroup B] [Module F B]
  {L : Type} [Field L] [Algebra F L] {V : Type} [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]

private abbrev Phi (a : End L V) (b : End F B) : End L (V ⊗[F] B) := AlgebraTensorModule.map a b

end

private theorem commute_tensorMap_of_commute {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f₁ f₂ : Module.End L V} {g₁ g₂ : Module.End F B} (hf : Commute f₁ f₂) (hg : Commute g₁ g₂) :
    Commute (AlgebraTensorModule.map f₁ g₁ : Module.End L (V ⊗[F] B)) (AlgebraTensorModule.map f₂ g₂) := by
  unfold Commute SemiconjBy
  rw [← AlgebraTensorModule.map_mul, ← AlgebraTensorModule.map_mul, hf.eq, hg.eq]

private theorem tensorMap_pow {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    (f : Module.End L V) (g : Module.End F B) (k : ℕ) :
    (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) ^ k = AlgebraTensorModule.map (f ^ k) (g ^ k) := by
  induction k with
  | zero => simp only [pow_zero, AlgebraTensorModule.map_one]
  | succ k ih =>
    rw [pow_succ, ih, ← AlgebraTensorModule.map_mul, ← pow_succ, ← pow_succ]

private theorem isNilpotent_tensorMap_of_isNilpotent {F B L V : Type} [Field F] [AddCommGroup B] [Module F B] [Field L]
    [Algebra F L] [AddCommGroup V] [Module L V] [Module F V] [IsScalarTower F L V]
    {f : Module.End L V} (g : Module.End F B) (hf : IsNilpotent f) :
    IsNilpotent (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) := by
  have h : (AlgebraTensorModule.map f g : Module.End L (V ⊗[F] B)) =
      AlgebraTensorModule.map f 1 * AlgebraTensorModule.map 1 g := by
    rw [← AlgebraTensorModule.map_mul, mul_one, one_mul]
  rw [h]
  apply Commute.isNilpotent_mul_right (commute_tensorMap_of_commute (Commute.one_right f) (Commute.one_left g))
  obtain ⟨k, hk⟩ := hf
  refine ⟨k, ?_⟩
  rw [tensorMap_pow, hk, one_pow]
  apply TensorProduct.AlgebraTensorModule.ext
  intro v b
  simp

theorem UpperTheory.Gal.crystallineComparison.nilAnn_of :
    NilOfAnn := by
  intro F G B _ _ _ _ σ ψ hσψ L _ _ V _ _ _ _ ρ q n T θ hTρ hTT hnil hann
  let c : ℕ → ℤ := fun j => (-1) ^ j * (q : ℤ) ^ j.choose 2
  let P : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j) (ψ ^ (n - j))
  let E : Module.End L (V ⊗[F] B) :=
    ∑ j ∈ Finset.range (n + 1), c j • AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))
  have hQ : Polynomial.aeval (onPer ψ L V) (heckePol q n θ) = P - E := by
    rw [← Finset.sum_sub_distrib]
    simp only [heckePol, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    simp only [onPer, tensorMap_pow, map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow,
      Module.End.mul_apply, Module.algebraMap_end_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      AlgebraTensorModule.map_tmul, ← smul_sub, ← sub_tmul]
    simp [c, smul_tmul', sub_sub_cancel, smul_smul]
    rw [← Int.cast_smul_eq_zsmul L, smul_smul]
    congr 2
    push_cast
    ring
  have hP : ∀ x ∈ Dinv σ ρ, P x = 0 := by
    intro x hx
    simp only [P, LinearMap.sum_apply, LinearMap.smul_apply]
    exact hann x hx
  have hM : ∀ i j : ℕ, ∀ f : Module.End L V, Commute (T i) f →
      Commute (c i • AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (c j • AlgebraTensorModule.map f (ψ ^ (n - j))) := by
    intro i j f hf
    have h0 : Commute (AlgebraTensorModule.map (T i) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
        (AlgebraTensorModule.map f (ψ ^ (n - j))) :=
      commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
    exact (h0.smul_left (c i)).smul_right (c j)
  have hPE : Commute P E := by
    refine Commute.sum_left _ _ _ fun i _ => Commute.sum_right _ _ _ fun j _ => ?_
    exact hM i j _ ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j)))
  have hE : IsNilpotent E := by
    refine Commute.isNilpotent_sum (fun j hj => (isNilpotent_tensorMap_of_isNilpotent _ (hnil j ?_)).smul (c j)) ?_
    · exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    · intro i j _ _
      have hf : Commute (T i - θ i • 1) (T j - θ j • 1) := by
        refine ((hTT i j).sub_right ((Commute.one_right (T i)).smul_right (θ j))).sub_left ?_
        exact ((Commute.one_left (T j)).smul_left (θ i)).sub_right
          (((Commute.one_right _).smul_left (θ i)).smul_right (θ j))
      have h0 : Commute (AlgebraTensorModule.map (T i - θ i • 1) (ψ ^ (n - i)) : Module.End L (V ⊗[F] B))
          (AlgebraTensorModule.map (T j - θ j • 1) (ψ ^ (n - j))) :=
        commute_tensorMap_of_commute hf (Commute.pow_pow_self ψ _ _)
      exact (h0.smul_left (c i)).smul_right (c j)
  obtain ⟨N, hN⟩ := hE
  refine ⟨N, fun x hx => ?_⟩
  have key : ∀ (k : ℕ) (y : V ⊗[F] B), P y = 0 → ((P - E) ^ k) y = ((-E) ^ k) y := by
    intro k
    induction k with
    | zero => intro y _; simp
    | succ k ih =>
      intro y hy
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply]
      have h1 : (P - E) y = (-E) y := by simp [hy]
      rw [h1]
      apply ih
      rw [← Module.End.mul_apply, hPE.neg_right.eq, Module.End.mul_apply, hy, map_zero]
  rw [hQ, key N x (hP x hx), neg_pow, hN]
  simp
