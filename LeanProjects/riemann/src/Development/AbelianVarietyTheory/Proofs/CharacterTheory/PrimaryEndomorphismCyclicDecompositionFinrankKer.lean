import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL

theorem finrank_ker_lsmul_pow_quotient {F : Type} [Field F] (f : F[X]) (hf : f ≠ 0) (e j : ℕ) :
    Module.finrank F (LinearMap.ker
      ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)) =
      f.natDegree * min j e := by
  have hle : Ideal.span {f ^ e} ≤ Ideal.span {f ^ min j e} :=
    Ideal.span_singleton_le_span_singleton.mpr (pow_dvd_pow f (min_le_right j e))
  haveI : Module.Finite F (F[X] ⧸ Ideal.span {f ^ e}) :=
    (AdjoinRoot.powerBasis (pow_ne_zero e hf)).finite
  let π := (Ideal.Quotient.factorₐ F hle).toLinearMap
  have hπ : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact Ideal.Quotient.factor_surjective hle
  have hker : LinearMap.ker π = LinearMap.range
      ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h1 : π (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x := rfl
    have h2 : ∀ y : F[X],
        ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)
          (Ideal.Quotient.mk _ y) = Ideal.Quotient.mk _ (f ^ j * y) := fun y => rfl
    rw [LinearMap.mem_ker, h1, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton,
      LinearMap.mem_range]
    constructor
    · rintro ⟨c, rfl⟩
      rcases le_total j e with h | h
      · exact ⟨Ideal.Quotient.mk _ c, by rw [h2, min_eq_left h]⟩
      · refine ⟨0, ?_⟩
        rw [map_zero, min_eq_right h, eq_comm, Ideal.Quotient.eq_zero_iff_mem,
          Ideal.mem_span_singleton]
        exact dvd_mul_right _ _
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [h2, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
      have h3 : f ^ min j e ∣ f ^ j * y - x := (pow_dvd_pow f (min_le_right j e)).trans hy
      have h4 : f ^ min j e ∣ f ^ j * y := (pow_dvd_pow f (min_le_left j e)).mul_right y
      simpa using dvd_sub h4 h3
  have h1 := LinearMap.finrank_range_add_finrank_ker π
  have h2 := LinearMap.finrank_range_add_finrank_ker
    ((LinearMap.lsmul F[X] (F[X] ⧸ Ideal.span {f ^ e}) (f ^ j)).restrictScalars F)
  rw [hπ, hker, finrank_top, finrank_quotient_span_eq_natDegree, natDegree_pow] at h1
  rw [mul_comm]
  omega

def piDropTrivial {R : Type} [Ring R] {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)]
    [∀ i, Module R (M i)] (P : ι → Prop) [DecidablePred P] (h : ∀ i, ¬ P i → Subsingleton (M i)) :
    ((i : ι) → M i) ≃ₗ[R] ((i : {i // P i}) → M i) where
  toFun x i := x i
  invFun y i := if hi : P i then y ⟨i, hi⟩ else 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv x := by
    funext i
    by_cases hi : P i
    · simp [hi]
    · haveI := h i hi
      exact Subsingleton.elim _ _
  right_inv y := by
    funext i
    simp [i.2]

def kerAevalEquivPi {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] (g : Module.End F V)
    {ι : Type} (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module F (M i)]
    [∀ i, Module F[X] (M i)] [∀ i, IsScalarTower F F[X] (M i)]
    (φ : Module.AEval' g ≃ₗ[F[X]] ((i : ι) → M i)) (p : F[X]) :
    LinearMap.ker (aeval g p) ≃ₗ[F]
      ((i : ι) → LinearMap.ker ((LinearMap.lsmul F[X] (M i) p).restrictScalars F)) where
  toFun x i := ⟨φ (Module.AEval'.of g x) i, by
    have hx : aeval g p • (x : V) = 0 := x.2
    have : p • φ (Module.AEval'.of g x) = 0 := by
      rw [← map_smul, ← Module.AEval.of_aeval_smul, hx, map_zero, map_zero]
    exact congrFun this i⟩
  invFun y := ⟨(Module.AEval'.of g).symm (φ.symm fun i => y i), by
    have : p • (fun i => (y i : M i)) = 0 := funext fun i => (y i).2
    change aeval g p • (Module.AEval'.of g).symm (φ.symm fun i => (y i : M i)) = 0
    rw [← Module.AEval.of_symm_smul, ← map_smul, this, map_zero, map_zero]⟩
  map_add' x y := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g ((x : V) + y)) i =
      φ (Module.AEval'.of g x) i + φ (Module.AEval'.of g y) i
    rw [map_add, map_add, Pi.add_apply]
  map_smul' c x := by
    funext i
    apply Subtype.ext
    change φ (Module.AEval'.of g (c • (x : V))) i = c • φ (Module.AEval'.of g x) i
    rw [map_smul, LinearMapClass.map_smul_of_tower φ, Pi.smul_apply]
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    funext i
    apply Subtype.ext
    simp

theorem primary_structure : ∀ (F : Type) [Field F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (g : Module.End F V) (f : F[X]) (m : ℕ), Irreducible f → aeval g (f ^ m) = 0 → ∃ (d : ℕ) (e : Fin d → ℕ), (∀ i, 0 < e i) ∧ Nonempty (Module.AEval' g ≃ₗ[F[X]] ((i : Fin d) → F[X] ⧸ Ideal.span {f ^ e i})) ∧ ∀ j : ℕ, Module.finrank F (LinearMap.ker (aeval g (f ^ j))) = f.natDegree * ∑ i, min j (e i) := by
  intro F _ V _ _ _ g f m hf hm
  classical
  have hT : Module.IsTorsion' (Module.AEval' g) (Submonoid.powers f) := by
    rw [Submodule.isTorsion'_powers_iff]
    intro x
    refine ⟨m, ?_⟩
    apply (Module.AEval'.of g).symm.injective
    rw [Module.AEval.of_symm_smul, hm, zero_smul, map_zero]
  obtain ⟨d, k, ⟨φ⟩⟩ := Module.torsion_by_prime_power_decomposition hf hT
  let σ := Fintype.equivFin {i : Fin d // 0 < k i}
  let ψ : Module.AEval' g ≃ₗ[F[X]]
      ((i : Fin (Fintype.card {i : Fin d // 0 < k i})) → F[X] ⧸ Ideal.span {f ^ k (σ.symm i)}) :=
    φ ≪≫ₗ DirectSum.linearEquivFunOnFintype F[X] (Fin d) (fun i => F[X] ⧸ Ideal.span {f ^ k i}) ≪≫ₗ
      piDropTrivial (fun i => F[X] ⧸ Ideal.span {f ^ k i}) (fun i => 0 < k i) (fun i hi => by
        have : k i = 0 := by omega
        rw [Ideal.Quotient.subsingleton_iff, this, pow_zero, Ideal.span_singleton_one]) ≪≫ₗ
      LinearEquiv.piCongrLeft' F[X] (fun i : {i : Fin d // 0 < k i} => F[X] ⧸ Ideal.span {f ^ k i}) σ
  refine ⟨_, fun i => k (σ.symm i), fun i => (σ.symm i).2, ⟨ψ⟩, fun j => ?_⟩
  haveI : ∀ e : ℕ, Module.Finite F (F[X] ⧸ Ideal.span {f ^ e}) := fun e =>
    (AdjoinRoot.powerBasis (pow_ne_zero e hf.ne_zero)).finite
  rw [(kerAevalEquivPi g _ ψ (f ^ j)).finrank_eq, Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => finrank_ker_lsmul_pow_quotient f hf.ne_zero _ j

end GlobalTheory.CuspGL
