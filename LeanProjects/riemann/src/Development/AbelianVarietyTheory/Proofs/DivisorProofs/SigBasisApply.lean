import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

namespace GlobalTheory.ScalarSigmaBasis

open GlobalTheory.UnitLemma

variable {K : UQ} (B : InvAlg K)

theorem sig_smul (r : K.E) (x : B.A) : B.σ (r • x) = K.c r • B.σ x := by
  rw [Algebra.smul_def, map_mul, B.σ_alg, ← Algebra.smul_def]

theorem sig_sum {ι : Type} (s : Finset ι) (f : ι → K.E) (v : ι → B.A) :
    B.σ (∑ i ∈ s, f i • v i) = ∑ i ∈ s, K.c (f i) • B.σ (v i) := by
  rw [map_sum]; simp only [sig_smul]

noncomputable def sigBasis {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) : Module.Basis (Fin n) K.E B.A :=
  Module.Basis.mk (v := fun i => B.σ (b i))
    (by
      rw [Fintype.linearIndependent_iff]
      intro f hf i
      have h1 : B.σ (∑ k, f k • B.σ (b k)) = 0 := by rw [hf, map_zero]
      rw [sig_sum] at h1
      simp only [B.σ_σ] at h1
      have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
      have : K.c (f i) = K.c 0 := by rw [h2, map_zero]
      exact K.c.injective this)
    (by
      intro x _
      have h := sig_sum B Finset.univ (fun k => b.repr (B.σ x) k) (fun k => b k)
      have hx : x = ∑ k, K.c (b.repr (B.σ x) k) • B.σ (b k) := by
        rw [← h, b.sum_repr, B.σ_σ]
      rw [hx]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

theorem sigBasis_apply {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (i : Fin n) :
    sigBasis B b i = B.σ (b i) := by
  simp [sigBasis]

theorem sigBasis_repr {n : ℕ} (b : Module.Basis (Fin n) K.E B.A) (z : B.A) (k : Fin n) :
    (sigBasis B b).repr (B.σ z) k = K.c (b.repr z k) := by
  have hz : B.σ z = ∑ i, K.c (b.repr z i) • sigBasis B b i := by
    conv_lhs => rw [← b.sum_repr z]
    rw [sig_sum]
    simp only [sigBasis_apply]
  rw [hz, Module.Basis.repr_sum_self]

theorem trace_sig (y : B.A) : Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  let b := Module.finBasis K.E B.A
  rw [Algebra.trace_eq_matrix_trace (sigBasis B b), Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag, Algebra.leftMulMatrix_eq_repr_mul, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sigBasis_apply, ← map_mul, sigBasis_repr]

theorem core (a : ℕ) (β : B.A) (hβ : B.σ β = β * ((-1 : B.A) ^ (a - 1) * B.g))
    (b : Module.Basis (Fin a) K.E B.A) (i j : Fin a) :
    K.c (B.herm β (b i) (b j)) = (-1 : K.E) ^ (a - 1) *
      ∑ k, B.herm β (b k) (b i) * LinearMap.toMatrix b b (LinearMap.mulLeft K.E B.g) k j := by
  have hg : B.g * b j = ∑ k, b.repr (B.g * b j) k • b k := (b.sum_repr _).symm
  have e1 : B.σ (β * b i * B.σ (b j)) =
      algebraMap K.E B.A ((-1 : K.E) ^ (a - 1)) * (β * (B.g * b j) * B.σ (b i)) := by
    rw [map_mul, map_mul, B.σ_σ, hβ]
    simp only [map_pow, map_neg, map_one]
    ring
  have e2 : β * (B.g * b j) * B.σ (b i) = ∑ k, b.repr (B.g * b j) k • (β * b k * B.σ (b i)) := by
    conv_lhs => rw [hg]
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_smul_comm, smul_mul_assoc]
  rw [InvAlg.herm, ← trace_sig, e1, e2, ← Algebra.smul_def, LinearMap.map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, mul_comm]
  rfl

theorem main : ∀ {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (L : Type) [inst : Field L] (e : GlobalTheory.UnitLemma.UQ.E K ≃+* L) (c : L →+* L), (∀ (x : GlobalTheory.UnitLemma.UQ.E K), (e : GlobalTheory.UnitLemma.UQ.E K → L) ((GlobalTheory.UnitLemma.UQ.c K : GlobalTheory.UnitLemma.UQ.E K → GlobalTheory.UnitLemma.UQ.E K) x) = (c : L → L) ((e : GlobalTheory.UnitLemma.UQ.E K → L) x)) → ∀ (a : ℕ) (β : GlobalTheory.UnitLemma.InvAlg.A B), (GlobalTheory.UnitLemma.InvAlg.σ B : GlobalTheory.UnitLemma.InvAlg.A B → GlobalTheory.UnitLemma.InvAlg.A B) β = β * ((-1 : GlobalTheory.UnitLemma.InvAlg.A B) ^ (a - (1 : ℕ)) * GlobalTheory.UnitLemma.InvAlg.g B) → ∀ (b : Module.Basis (Fin a) (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.A B)), Matrix.map (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) (⇑c : L → L) = (-1 : L) ^ (a - (1 : ℕ)) • (Matrix.transpose (Matrix.map ((Matrix.of : (Fin a → Fin a → GlobalTheory.UnitLemma.UQ.E K) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) fun (i j : Fin a) ↦ GlobalTheory.UnitLemma.InvAlg.herm B β ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) i) ((b : Fin a → GlobalTheory.UnitLemma.InvAlg.A B) j)) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) * Matrix.map ((LinearMap.toMatrix b b : (GlobalTheory.UnitLemma.InvAlg.A B →ₗ[GlobalTheory.UnitLemma.UQ.E K] GlobalTheory.UnitLemma.InvAlg.A B) → Matrix (Fin a) (Fin a) (GlobalTheory.UnitLemma.UQ.E K)) (LinearMap.mulLeft (GlobalTheory.UnitLemma.UQ.E K) (GlobalTheory.UnitLemma.InvAlg.g B))) (⇑e : GlobalTheory.UnitLemma.UQ.E K → L)) := by
  intro K B L _ e c hc a β hβ b
  ext i j
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.transpose_apply,
    smul_eq_mul]
  rw [← hc, core B a β hβ b i j]
  simp only [map_mul, map_sum, map_pow, map_neg, map_one]

end GlobalTheory.ScalarSigmaBasis
