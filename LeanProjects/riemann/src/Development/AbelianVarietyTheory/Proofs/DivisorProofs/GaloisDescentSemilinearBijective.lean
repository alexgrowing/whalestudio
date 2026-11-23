import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem semilinear_pow_smul {F F' V : Type} [Field F] [Field F'] [Algebra F F'] [AddCommGroup V]
    [Module F' V] [Module F V] (s : F' ≃ₐ[F] F') (T : Module.End F V)
    (hT : ∀ (c : F') (v : V), T (c • v) = s c • T v) (m : ℕ) (c : F') (v : V) :
    (T ^ m) (c • v) = (s ^ m) c • (T ^ m) v := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, ih, hT, AlgEquiv.mul_apply, Module.End.mul_apply]

theorem pow_apply_of_mem_ker_sub_one {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    (T : Module.End F V) (u : V) (hu : u ∈ LinearMap.ker (T - 1)) (m : ℕ) : (T ^ m) u = u := by
  have h1 : T u = u := by
    have h := LinearMap.mem_ker.mp hu
    rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, Module.End.mul_apply, h1, ih]

theorem algebraMap_trace_eq_sum_pow {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (x : F') :
    algebraMap F F' (Algebra.trace F F' x) = ∑ j : Fin (Module.finrank F F'), (s ^ (j : ℕ)) x := by
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  rw [trace_eq_sum_automorphisms]
  have hord : orderOf s = Module.finrank F F' := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hs, IsGalois.card_aut_eq_finrank]
  have hinj : Function.Injective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) := by
    intro i j hij
    simp only at hij
    rw [pow_inj_mod, hord, Nat.mod_eq_of_lt i.2, Nat.mod_eq_of_lt j.2] at hij
    exact Fin.ext hij
  have hbij : Function.Bijective (fun j : Fin (Module.finrank F F') => s ^ (j : ℕ)) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨hinj, by rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]⟩
  exact (Fintype.sum_bijective _ hbij _ _ (fun j => rfl)).symm

end GlobalTheory.Shin

namespace GlobalTheory.Shin

theorem galoisDescent_semilinear_bijective : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F'), (∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) → ∀ (V : Type) [AddCommGroup V] [Module F' V] [Module F V] [IsScalarTower F F' V] (T : Module.End F V), (∀ (c : F') (v : V), T (c • v) = s c • T v) → T ^ Module.finrank F F' = 1 → ∀ (ι : Type) [Fintype ι] (b : Module.Basis ι F F'), Function.Bijective (fun v : ι → LinearMap.ker (T - 1) => ∑ i, b i • (v i : V)) := by
  intro F F' _ _ _ _ s hs V _ _ _ _ T hT hTn ι _ b
  classical
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : FiniteDimensional F F' := Module.Finite.of_finite
  set n := Module.finrank F F' with hn
  have hnd := traceForm_nondegenerate F F'
  set d := (Algebra.traceForm F F').dualBasis hnd b with hd
  have hdb : ∀ i j, Algebra.trace F F' (d i * b j) = if j = i then 1 else 0 := fun i j => by
    have h := LinearMap.BilinForm.apply_dualBasis_left hnd b i j
    simpa [Algebra.traceForm_apply] using h
  have key1 : ∀ i j, ∑ k : Fin n, (s ^ (k : ℕ)) (d i) * (s ^ (k : ℕ)) (b j) =
      if i = j then 1 else 0 := by
    intro i j
    have h := algebraMap_trace_eq_sum_pow s hs (d i * b j)
    simp only [map_mul] at h
    rw [← h, hdb]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij, Ne.symm hij]
  have hTk : ∀ (k : ℕ) (c : F') (v : V), (T ^ k) (c • v) = (s ^ k) c • (T ^ k) v :=
    semilinear_pow_smul s T hT
  have hfix : ∀ (u : LinearMap.ker (T - 1)) (k : ℕ), (T ^ k) (u : V) = u :=
    fun u k => pow_apply_of_mem_ker_sub_one T u u.2 k
  have hn0 : 0 < n := Module.finrank_pos
  have hcard : Fintype.card ι = n := (Module.finrank_eq_card_basis b).symm
  let e : ι ≃ Fin n := Fintype.equivFinOfCardEq hcard
  let A : Matrix (Fin n) ι F' := fun k j => (s ^ (k : ℕ)) (b j)
  let B : Matrix ι (Fin n) F' := fun i k => (s ^ (k : ℕ)) (d i)
  have hBA : B * A = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    exact key1 i j
  have hAB : A * B = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).mpr hBA
  let k0 : Fin n := ⟨0, hn0⟩
  have key2 : ∀ l : Fin n, ∑ i, b i * (s ^ (l : ℕ)) (d i) = if k0 = l then 1 else 0 := by
    intro l
    have h := congrFun (congrFun hAB k0) l
    rw [Matrix.mul_apply, Matrix.one_apply] at h
    simpa [A, B, k0] using h
  constructor
  · intro v w hvw
    simp only at hvw
    have hk : ∀ k : ℕ, ∑ i, (s ^ k) (b i) • (v i : V) = ∑ i, (s ^ k) (b i) • (w i : V) := by
      intro k
      have h := congrArg (T ^ k) hvw
      simpa only [map_sum, hTk, hfix] using h
    have expand : ∀ (u : ι → LinearMap.ker (T - 1)) (j : ι), (u j : V) =
        ∑ k : Fin n, (s ^ (k : ℕ)) (d j) • ∑ i, (s ^ (k : ℕ)) (b i) • (u i : V) := by
      intro u j
      simp_rw [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_smul, key1]
      simp [ite_smul]
    funext j
    apply Subtype.ext
    rw [expand v j, expand w j]
    simp_rw [hk]
  · intro w
    let Q : V → V := fun u => ∑ k : Fin n, (T ^ (k : ℕ)) u
    have hQ : ∀ u, Q u ∈ LinearMap.ker (T - 1) := by
      intro u
      simp only [Q]
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, map_sum]
      rw [Fin.sum_univ_eq_sum_range (fun k => T ((T ^ k) u)),
        Fin.sum_univ_eq_sum_range (fun k => (T ^ k) u)]
      have hs1 : ∀ k : ℕ, T ((T ^ k) u) = (T ^ (k + 1)) u := fun k => by
        rw [pow_succ', Module.End.mul_apply]
      simp_rw [hs1]
      have h1 := Finset.sum_range_succ' (fun k => (T ^ k) u) n
      have h2 := Finset.sum_range_succ (fun k => (T ^ k) u) n
      rw [h2, hTn, pow_zero] at h1
      exact (add_right_cancel h1).symm
    refine ⟨fun i => ⟨Q (d i • w), hQ _⟩, ?_⟩
    simp only [Q, hTk, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul, key2]
    simp [ite_smul, k0]

end GlobalTheory.Shin
