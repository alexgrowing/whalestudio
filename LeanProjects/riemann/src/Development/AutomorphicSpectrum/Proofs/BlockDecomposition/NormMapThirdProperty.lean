import Mathlib
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.Development
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnitOneAddJacobsonTensorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFiniteAlgebraJacobsonRadicalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModuleAdicCompleteStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorIdealMapInjectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormMapCongruenceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CyclicAlgebraHilbertNinetyStatement

open scoped TensorProduct
open IsLocalRing

namespace GlobalTheory.CompanionTheory.UnitNorm

noncomputable section

section Basics

variable {O O' R : Type} [CommRing O] [CommRing O'] [Algebra O O'] [CommRing R] [Algebra O R]

def tw (τ : O' ≃ₐ[O] O') (j : ℕ) : O' ⊗[O] R →ₐ[O] O' ⊗[O] R :=
  Algebra.TensorProduct.map ((τ ^ j : O' ≃ₐ[O] O').toAlgHom) (AlgHom.id O R)

def nrm (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (s : O' ⊗[O] R) : O' ⊗[O] R :=
  ∏ j ∈ Finset.range ℓ, tw τ j s

abbrev inc : R →ₐ[O] O' ⊗[O] R := Algebra.TensorProduct.includeRight

theorem nrm_mul (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (x y : O' ⊗[O] R) :
    nrm ℓ τ (x * y) = nrm ℓ τ x * nrm ℓ τ y := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_mul, Finset.prod_mul_distrib]

theorem nrm_one (ℓ : ℕ) (τ : O' ≃ₐ[O] O') : nrm ℓ τ (1 : O' ⊗[O] R) = 1 := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_one, Finset.prod_const_one]

theorem map_tw (τ : O' ≃ₐ[O] O') (j : ℕ) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (tw τ j s) = tw τ (j + 1) s := by
  induction s using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul x y =>
    simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, Algebra.TensorProduct.map_tmul, AlgEquiv.toAlgHom_eq_coe, AlgHom.coe_coe,
      AlgHom.id_apply, pow_succ', AlgEquiv.mul_apply]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem tw_period {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    tw τ ℓ s = tw τ 0 s := by
  simp only [GlobalTheory.CompanionTheory.UnitNorm.tw, hτ, pow_zero]

theorem nrm_fixed {ℓ : ℕ} {τ : O' ≃ₐ[O] O'} (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1) (s : O' ⊗[O] R) :
    Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) (nrm ℓ τ s) = nrm ℓ τ s := by
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod, GlobalTheory.CompanionTheory.UnitNorm.map_tw]
  rw [Finset.prod_range_succ, Finset.prod_range_succ', GlobalTheory.CompanionTheory.UnitNorm.tw_period hτ]

theorem map_inc_map (A : Ideal O) :
    Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) (Ideal.map (algebraMap O R) A) =
      Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ hx
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, ← AlgHom.commutes (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx)

theorem tw_mem (τ : O' ≃ₐ[O] O') (j : ℕ) (A : Ideal O) {x : O' ⊗[O] R}
    (hx : x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    tw τ j x ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  have h : Ideal.map (algebraMap O (O' ⊗[O] R)) A ≤
      Ideal.comap (GlobalTheory.CompanionTheory.UnitNorm.tw τ j) (Ideal.map (algebraMap O (O' ⊗[O] R)) A) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
    exact Ideal.mem_map_of_mem _ ha
  exact h hx

theorem nrm_sub_mem (ℓ : ℕ) (τ : O' ≃ₐ[O] O') (A : Ideal O) {x y : O' ⊗[O] R}
    (h : x - y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A) :
    nrm ℓ τ x - nrm ℓ τ y ∈ Ideal.map (algebraMap O (O' ⊗[O] R)) A := by
  rw [← Ideal.Quotient.eq]
  simp only [GlobalTheory.CompanionTheory.UnitNorm.nrm, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [Ideal.Quotient.eq, ← map_sub]
  exact GlobalTheory.CompanionTheory.UnitNorm.tw_mem τ j A h

theorem step [Module.Finite O O'] [Module.Free O O'] [Nontrivial O'] {ℓ : ℕ} {τ : O' ≃ₐ[O] O'}
    (hℓ : 0 < ℓ) (hτ : τ ^ ℓ = 1)
    (hfixS : ∀ s : O' ⊗[O] R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R) s = s →
      s ∈ Set.range (inc : R →ₐ[O] O' ⊗[O] R))
    (a : O')
    (hcong : ∀ m : ℕ, 1 ≤ m → ∀ r ∈ (⊥ : Ideal R).jacobson ^ m,
      nrm ℓ τ (1 + a ⊗ₜ[O] r) - (inc : R →ₐ[O] O' ⊗[O] R) (1 + r) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)))
    (u : R) (m : ℕ) (hm : 1 ≤ m) (P : (O' ⊗[O] R)ˣ)
    (h : (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P : O' ⊗[O] R) ∈
      Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) :
    ∃ P' : (O' ⊗[O] R)ˣ, (P' : O' ⊗[O] R) - (P : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) ∧
      (inc : R →ₐ[O] O' ⊗[O] R) u - nrm ℓ τ (P' : O' ⊗[O] R) ∈
        Ideal.map (inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
  have hfix_incR : ∀ x : R, Algebra.TensorProduct.map τ.toAlgHom (AlgHom.id O R)
      ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x) = (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) x := by
    intro x
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul,
      map_one, AlgHom.id_apply]
  obtain ⟨r, hr⟩ := hfixS ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R)) (by
    rw [map_sub, hfix_incR, GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ])
  obtain ⟨v, hv⟩ := hfixS (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R))
    (GlobalTheory.CompanionTheory.UnitNorm.nrm_fixed hℓ hτ _)
  have hrm : r ∈ (⊥ : Ideal R).jacobson ^ m := by
    have h' := h
    rw [← hr] at h'
    exact GlobalTheory.T.tensor_ideal_map_injective O O' R _ r h'
  have hvr : v * r ∈ (⊥ : Ideal R).jacobson ^ m := Ideal.mul_mem_left _ v hrm
  have hsplit : a ⊗ₜ[O] (v * r) = (a ⊗ₜ[O] (1 : R)) * (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (v * r) := by
    simp only [GlobalTheory.CompanionTheory.UnitNorm.inc, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, one_mul]
  have hmem : a ⊗ₜ[O] (v * r) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m) := by
    rw [hsplit]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hvr)
  have hJ : a ⊗ₜ[O] (v * r) ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (⊥ : Ideal R).jacobson :=
    Ideal.map_mono (Ideal.pow_le_self (by omega)) hmem
  have hU : IsUnit (1 + a ⊗ₜ[O] (v * r)) :=
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R _ hJ
  have hPP : GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ ((P⁻¹ : (O' ⊗[O] R)ˣ) : O' ⊗[O] R) = 1 := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, Units.mul_inv, GlobalTheory.CompanionTheory.UnitNorm.nrm_one]
  have hc' : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (m + 1)) := by
    have h'' := neg_mem (hcong m hm (v * r) hvr)
    rwa [neg_sub] at h''
  have key : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) u -
        GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r)) =
      GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R) *
        ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (1 + v * r) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (1 + a ⊗ₜ[O] (v * r))) := by
    rw [map_add, map_one, map_mul]
    linear_combination (-1 : O' ⊗[O] R) * hr +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r * GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P : O' ⊗[O] R))) * hv +
      (-((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) r)) * hPP
  refine ⟨P * hU.unit, ?_, ?_⟩
  · rw [Units.val_mul, IsUnit.unit_spec,
      show (P : O' ⊗[O] R) * (1 + a ⊗ₜ[O] (v * r)) - P = P * (a ⊗ₜ[O] (v * r)) by ring]
    exact Ideal.mul_mem_left _ _ hmem
  · rw [Units.val_mul, IsUnit.unit_spec, GlobalTheory.CompanionTheory.UnitNorm.nrm_mul, key]
    exact Ideal.mul_mem_left _ _ hc'

end Basics

theorem norm_units_surjective : PositivityTheory.Rg.Tf.Loc.N1 → PositivityTheory.Rg.Tf.Loc.N2 → PositivityTheory.Rg.Tf.Loc.N3 := by
  intro hInt hConj
  unfold PositivityTheory.Rg.Tf.Loc.N3
  intro O O' R _ _ _ _ _ _ _ _ _ _ _ _ ℓ τ hℓ hτ hfix hbasis r
  by_cases hO' : Nontrivial O'
  swap
  · haveI : Subsingleton O' := not_nontrivial_iff_subsingleton.mp hO'
    have h1 : (1 : O' ⊗[O] R) = 0 := by
      calc (1 : O' ⊗[O] R) = (1 : O') ⊗ₜ[O] (1 : R) := Algebra.TensorProduct.one_def
        _ = (0 : O') ⊗ₜ[O] (1 : R) := by rw [Subsingleton.elim (1 : O') 0]
        _ = 0 := by rw [TensorProduct.zero_tmul]
    haveI : Subsingleton (O' ⊗[O] R) := subsingleton_of_zero_eq_one h1.symm
    exact ⟨1, Subsingleton.elim _ _⟩
  haveI := hO'
  obtain ⟨hfixS, a, ha1, hcong⟩ := hConj O O' R ℓ τ hℓ hτ hfix hbasis
  obtain ⟨hle, N, hN⟩ := GlobalTheory.T.local_finite_algebra_jacobson_radical O R
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal O) (O' ⊗[O] R) :=
    GlobalTheory.T.finite_module_adic_complete O (O' ⊗[O] R)
  obtain ⟨P₁, hP₁⟩ :=
    GlobalTheory.T.cyclic_algebra_hilbert_ninety hInt O O' R ℓ τ hℓ hτ hfix hbasis ⟨a, ha1⟩ r
  have h2 : ∀ k : ℕ, Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ (N * k + 1)) ≤
      Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O ^ k) := by
    intro k
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map]
    refine Ideal.map_mono ?_
    rw [Ideal.map_pow]
    exact le_trans (Ideal.pow_le_pow_right (Nat.le_succ _))
      (by rw [pow_mul]; exact Ideal.pow_right_mono hN k)
  have h3 : Ideal.map (algebraMap O (O' ⊗[O] R)) (IsLocalRing.maximalIdeal O) ≤
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [← GlobalTheory.CompanionTheory.UnitNorm.map_inc_map, pow_one]
    exact Ideal.map_mono hle
  have h4 : ∀ x ∈ Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1),
      IsUnit (1 + x) := fun x hx =>
    GlobalTheory.T.isUnit_one_add_jacobson_tensor O O' R x (by rwa [pow_one] at hx)
  have h6 : (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R) - GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ (P₁ : O' ⊗[O] R) ∈
      Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ 1) := by
    rw [pow_one, ← neg_sub]
    exact neg_mem hP₁
  obtain ⟨L, hL⟩ := GlobalTheory.T.norm_map_congruence O (O' ⊗[O] R)
    (IsLocalRing.maximalIdeal O)
    (fun m => Ideal.map (GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) ((⊥ : Ideal R).jacobson ^ m)) N
    (GlobalTheory.CompanionTheory.UnitNorm.nrm ℓ τ) ((GlobalTheory.CompanionTheory.UnitNorm.inc : R →ₐ[O] O' ⊗[O] R) (r : R)) P₁
    (fun m => Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ m))) h2 h3 h4
    (fun k x y hxy => GlobalTheory.CompanionTheory.UnitNorm.nrm_sub_mem ℓ τ _ hxy) h6
    (fun m hm P hP => GlobalTheory.CompanionTheory.UnitNorm.step hℓ hτ hfixS a hcong (r : R) m hm P hP)
  exact ⟨L, hL⟩

end

end GlobalTheory.CompanionTheory.UnitNorm
