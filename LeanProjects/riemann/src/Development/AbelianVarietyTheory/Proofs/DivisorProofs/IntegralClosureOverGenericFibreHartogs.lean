import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFreeOver
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.ClosureHartogs

theorem closure_hart : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [Algebra A R] [IsNoetherianRing R],
    GlobalTheory.GoodEtale.Hart A R R →
    Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
      (τ : D →ₗ[GlobalTheory.LocAcyc.GenFib A R] GlobalTheory.LocAcyc.GenFib A R),
      (∀ c ∈ GlobalTheory.KeyOriginNoeth.closure A R D, ∃ r : R, algebraMap R _ r = τ c) →
    ∀ (a₀ : A), a₀ ≠ 0 → ∀ (n : ℕ) (x y : Fin n → D),
      (∀ i, y i ∈ GlobalTheory.KeyOriginNoeth.closure A R D) →
      (∀ d : D, ∑ i, x i * algebraMap _ D (τ (y i * d)) =
        GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) →
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    GlobalTheory.GoodEtale.Hart A R (GlobalTheory.KeyOriginNoeth.closure A R D) := by
  intro A R _ _ _ _ _ hHR hinj D _ _ τ hτC a₀ ha₀ n x y hy hid
  set F := GlobalTheory.LocAcyc.GenFib A R
  set C := GlobalTheory.KeyOriginNoeth.closure A R D
  letI : Algebra R D := (GlobalTheory.KeyOriginNoeth.baseHom A R D).toAlgebra
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
  have hbase : ∀ r : R, GlobalTheory.KeyOriginNoeth.baseHom A R D r = algebraMap F D (algebraMap R F r) :=
    fun r => rfl
  have hmemC : ∀ z : D, z ∈ C ↔ IsIntegral R z := fun z => Iff.rfl
  have hsmulC : ∀ (r : R) (c : C), ((r • c : C) : D) = GlobalTheory.KeyOriginNoeth.baseHom A R D r * c :=
    fun r c => rfl
  have hτm : ∀ (f : F) (w : D), τ (algebraMap F D f * w) = f * τ w := by
    intro f w; rw [← Algebra.smul_def, τ.map_smul, smul_eq_mul]

  have hunit : ∀ a : A, a ≠ 0 → IsUnit (algebraMap R F (algebraMap A R a)) := by
    intro a ha
    exact IsLocalization.map_units F
      (⟨algebraMap A R a, Algebra.mem_algebraMapSubmonoid_of_mem (⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩ :
        nonZeroDivisors A)⟩ : Algebra.algebraMapSubmonoid R (nonZeroDivisors A))

  let N : Submodule R D :=
    { carrier := {d | ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z)}
      add_mem' := by
        intro d₁ d₂ h₁ h₂ z hz
        obtain ⟨r₁, e₁⟩ := h₁ z hz
        obtain ⟨r₂, e₂⟩ := h₂ z hz
        exact ⟨r₁ + r₂, by rw [map_add, e₁, e₂, add_mul, map_add]⟩
      zero_mem' := by
        intro z _
        exact ⟨0, by simp⟩
      smul_mem' := by
        intro r d h z hz
        obtain ⟨r₁, e₁⟩ := h z hz
        refine ⟨r * r₁, ?_⟩
        rw [Algebra.smul_def, mul_assoc]
        change _ = τ (algebraMap F D (algebraMap R F r) * (d * z))
        rw [hτm, ← e₁, map_mul] }
  have hmemN : ∀ d, d ∈ N ↔ ∀ z ∈ C, ∃ r : R, algebraMap R F r = τ (d * z) := fun d => Iff.rfl
  have h1N : (1 : D) ∈ N := by
    intro z hz
    simpa using hτC z hz

  obtain ⟨c₀, hc₀⟩ := hunit a₀ ha₀
  let S : Submodule R D := Submodule.span R (Set.range fun i => algebraMap F D (↑c₀⁻¹ : F) * x i)
  have hNS : N ≤ S := by
    intro d hd
    have hr : ∀ i, ∃ r : R, algebraMap R F r = τ (y i * d) := by
      intro i
      obtain ⟨r, e⟩ := hd (y i) (hy i)
      exact ⟨r, by rw [e, mul_comm]⟩
    choose r hr using hr
    have hd' : d = ∑ i, r i • (algebraMap F D (↑c₀⁻¹ : F) * x i) := by
      have h := hid d
      have h2 : d = algebraMap F D (↑c₀⁻¹ : F) *
          (GlobalTheory.KeyOriginNoeth.baseHom A R D (algebraMap A R a₀) * d) := by
        rw [hbase, ← mul_assoc, ← map_mul, ← hc₀, Units.inv_mul, map_one, one_mul]
      rw [h2, ← h, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, ← hr i]
      change _ = algebraMap F D (algebraMap R F (r i)) * _
      ring
    rw [hd']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hSnoeth : IsNoetherian R S :=
    isNoetherian_of_fg_of_noetherian S (Submodule.fg_span (Set.finite_range _))

  intro a ha m hm
  obtain ⟨c, hc⟩ := hunit a ha
  set ξ : D := algebraMap F D (↑c⁻¹ : F) * (m : D) with hξ

  have hξN : ∀ d ∈ N, ξ * d ∈ N := by
    intro d hd z hz
    have hmz : (m : D) * z ∈ C := C.mul_mem m.2 hz
    obtain ⟨r₀, e₀⟩ := hd _ hmz
    have hdiv : ∃ r'' : R, r₀ = algebraMap A R a • r'' := by
      apply hHR a ha r₀
      intro p hp hph
      obtain ⟨u, hu, m', hm'⟩ := hm p hp hph
      have hm'z : (m' : D) * z ∈ C := C.mul_mem m'.2 hz
      obtain ⟨r', e'⟩ := hd _ hm'z
      refine ⟨u, hu, r', ?_⟩
      apply hinj
      have hv := congrArg Subtype.val hm'
      rw [hsmulC, hsmulC, hbase, hbase] at hv
      rw [smul_eq_mul, smul_eq_mul, map_mul, map_mul, e₀, e', ← hτm, ← hτm]
      congr 1
      linear_combination (d * z) * hv
    obtain ⟨r'', e''⟩ := hdiv
    refine ⟨r'', ?_⟩
    have : ξ * d * z = algebraMap F D (↑c⁻¹ : F) * (d * ((m : D) * z)) := by
      rw [hξ]; ring
    rw [this, hτm, ← e₀, e'', smul_eq_mul, map_mul, ← hc, ← mul_assoc, Units.inv_mul, one_mul]
  have hpow : ∀ k : ℕ, ξ ^ k ∈ N := by
    intro k
    induction k with
    | zero => simpa using h1N
    | succ k ih => rw [pow_succ']; exact hξN _ ih
  have hadj : Subalgebra.toSubmodule (Algebra.adjoin R {ξ}) ≤ S := by
    rw [Algebra.adjoin_eq_span]
    refine le_trans ?_ hNS
    rw [Submodule.span_le]
    intro w hw
    obtain ⟨k, rfl⟩ := Submonoid.mem_closure_singleton.mp hw
    exact hpow k
  have hfg : (Subalgebra.toSubmodule (Algebra.adjoin R {ξ})).FG :=
    isNoetherian_submodule.mp hSnoeth _ hadj
  have hξC : ξ ∈ C :=
    (hmemC ξ).mpr (IsIntegral.of_mem_of_fg _ hfg ξ (Algebra.self_mem_adjoin_singleton R ξ))
  refine ⟨⟨ξ, hξC⟩, Subtype.ext ?_⟩
  rw [hsmulC, hbase]
  change (m : D) = algebraMap F D (algebraMap R F (algebraMap A R a)) * ξ
  rw [hξ, ← mul_assoc, ← map_mul, ← hc, Units.mul_inv, map_one, one_mul]

end GlobalTheory.ClosureHartogs
