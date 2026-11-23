import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPthRootOfDerivationZeroStatement
open scoped BigOperators

namespace GlobalTheory.CubeFib

theorem exists_pow_eq_of_pderiv_eq_zero {k : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] {σ : Type} [DecidableEq σ] (F : MvPowerSeries σ k)
    (hF : ∀ i, MvPowerSeries.pderiv k i F = 0) : ∃ g : MvPowerSeries σ k, g ^ p = F := by
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  let g : MvPowerSeries σ k :=
    fun d => (frobeniusEquiv k p).symm (MvPowerSeries.coeff (p • d) F)
  have hg : ∀ d, MvPowerSeries.coeff d g =
      (frobeniusEquiv k p).symm (MvPowerSeries.coeff (p • d) F) := fun d => rfl
  refine ⟨g, ?_⟩
  rw [← MvPowerSeries.map_frobenius_expand p hp]
  ext n
  rw [MvPowerSeries.coeff_map]
  by_cases! h : ∀ i, p ∣ n i
  · obtain ⟨m, hm⟩ : ∃ m, p • m = n := ⟨n.mapRange (fun a ↦ a / p) (by simp),
      by ext i; simp [(Nat.mul_div_cancel' (h i))]⟩
    rw [← hm, MvPowerSeries.coeff_expand_smul, hg]
    exact (frobeniusEquiv k p).apply_symm_apply _
  · obtain ⟨i, hi⟩ := h
    rw [MvPowerSeries.coeff_expand_of_not_dvd p hp _ hi, map_zero]
    have hni : n i ≠ 0 := fun h0 => hi (h0 ▸ dvd_zero p)
    have hle : Finsupp.single i 1 ≤ n := by
      rw [Finsupp.single_le_iff]; omega
    have h1 := congrArg (MvPowerSeries.coeff (n - Finsupp.single i 1)) (hF i)
    rw [MvPowerSeries.coeff_pderiv, map_zero, tsub_add_cancel_of_le hle] at h1
    have h2 : (((n - Finsupp.single i 1 : σ →₀ ℕ) i : k) + 1) = (n i : k) := by
      rw [← Nat.cast_succ]; congr 1; simp; omega
    rw [h2] at h1
    rcases mul_eq_zero.mp h1 with h3 | h3
    · exact h3.symm
    · exact absurd ((CharP.cast_eq_zero_iff k p _).mp h3) hi

theorem derivation_mem_pow_smul_top {R A M : Type} [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module A M] [Module R M] (D : Derivation R A M) (I : Ideal A) (m : ℕ) :
    ∀ a ∈ I ^ (m + 1), D a ∈ (I ^ m • ⊤ : Submodule A M) := by
  induction m with
  | zero => intro a _; simp
  | succ m ih =>
    intro a ha
    rw [pow_succ] at ha
    refine Submodule.mul_induction_on ha ?_ ?_
    · intro x hx y hy
      rw [Derivation.leibniz]
      refine add_mem (Submodule.smul_mem_smul hx Submodule.mem_top) ?_
      rw [pow_succ', ← smul_eq_mul, Submodule.smul_assoc]
      exact Submodule.smul_mem_smul hy (ih x hx)
    · intro x y hx hy
      rw [map_add]; exact add_mem hx hy

theorem derivation_algebraMap_perfect {k K : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [Field K] [Algebra k K] (D : Derivation ℤ K K) (c : k) :
    D (algebraMap k K c) = 0 := by
  haveI : ExpChar k p := ExpChar.prime Fact.out
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI : CharP K p := charP_of_injective_algebraMap (algebraMap k K).injective p
  obtain ⟨b, rfl⟩ := (frobeniusEquiv k p).surjective c
  rw [frobeniusEquiv_apply, frobenius_def, map_pow, Derivation.leibniz_pow, nsmul_eq_mul,
    CharP.cast_eq_zero, zero_mul]

theorem derivation_eq_zero_of_kaehler {k A K : Type} [Field k] [PerfectField k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [CommRing A] [Algebra k A] [Field K] [Algebra k K] [Algebra A K]
    [IsScalarTower k A K] (f : A) (hd : KaehlerDifferential.D k A f = 0) (D : Derivation ℤ K K) :
    D (algebraMap A K f) = 0 := by
  let L : A →ₗ[k] K :=
    { toFun := fun a => D (algebraMap A K a)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun c a => by
        rw [Algebra.smul_def, map_mul, Derivation.leibniz,
          ← IsScalarTower.algebraMap_apply, derivation_algebraMap_perfect p D c, smul_zero,
          add_zero, RingHom.id_apply, Algebra.smul_def c, smul_eq_mul] }
  let D' : Derivation k A K := Derivation.mk' L (fun a b => by
    change D (algebraMap A K (a * b)) =
      a • D (algebraMap A K b) + b • D (algebraMap A K a)
    rw [map_mul, Derivation.leibniz, Algebra.smul_def a, Algebra.smul_def b, smul_eq_mul,
      smul_eq_mul])
  have h := D'.liftKaehlerDifferential_comp_D f
  rw [hd, map_zero] at h
  exact h.symm

theorem exists_pow_eq_fractionRing_of_pderiv_eq_zero : ∀ (k : Type) [Field k] [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [Algebra k A] [Algebra.EssFiniteType k A] (σ : Type) [Fintype σ] [DecidableEq σ] (j : A →ₐ[k] MvPowerSeries σ k), (∀ (m : ℕ) (a : A), j a ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ m ↔ a ∈ IsLocalRing.maximalIdeal A ^ m) → (∀ (m : ℕ) (s : MvPowerSeries σ k), ∃ a : A, j a - s ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ k)) ^ m) → ∀ f : A, (∀ i, MvPowerSeries.pderiv k i (j f) = 0) → ∃ h : FractionRing A, h ^ p = algebraMap A (FractionRing A) f := by
  intro k _ _ p _ _ A _ _ _ _ _ σ _ _ j hj hsurj f hf
  have hp : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : IsNoetherianRing A := Algebra.EssFiniteType.isNoetherianRing k A
  haveI : CharP (FractionRing A) p :=
    charP_of_injective_algebraMap (algebraMap k (FractionRing A)).injective p
  haveI : CharP A p := charP_of_injective_algebraMap (algebraMap k A).injective p
  haveI : CharP (MvPowerSeries σ k) p :=
    charP_of_injective_algebraMap (algebraMap k (MvPowerSeries σ k)).injective p
  obtain ⟨g, hg⟩ := exists_pow_eq_of_pderiv_eq_zero p (j f) hf
  have hd : KaehlerDifferential.D k A f = 0 := by
    have key := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := Ω[A⁄k])
      (IsLocalRing.maximalIdeal A) (IsLocalRing.maximalIdeal.isMaximal A).ne_top
    rw [← Submodule.mem_bot A, ← key, Submodule.mem_iInf]
    intro m
    obtain ⟨a, ha⟩ := hsurj (m + 1) g
    have h1 : a ^ p - f ∈ IsLocalRing.maximalIdeal A ^ (m + 1) := by
      rw [← hj, map_sub, map_pow, ← hg, ← sub_pow_char]
      exact Ideal.pow_mem_of_mem _ ha p (Nat.pos_of_ne_zero hp)
    have h2 := derivation_mem_pow_smul_top (KaehlerDifferential.D k A) _ m _ h1
    rw [map_sub, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero,
      zero_smul, zero_sub] at h2
    exact (neg_mem_iff).mp h2
  apply GlobalTheory.T.exists_pth_root_of_derivation_zero
  intro D
  exact derivation_eq_zero_of_kaehler p f hd D

end GlobalTheory.CubeFib
