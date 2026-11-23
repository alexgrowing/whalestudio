import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InnerProductRootPowerSumEqOfFrobeniusModEqStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumMobiusStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvertibleEndInnerProductRootPowerSumEqTorusSumStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.PrimitiveEndClassFunctionZeroOfCharpolyMassZeroStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfNotPrimaryStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEqui
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsPrimitiveEndClassFunctionInvariantSubspaceMobiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootPowerSumCharacterAdditiveAndXSubOnePow
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.EqZeroOfFinsumMulStarPowEqZero

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI

namespace GlobalTheory.CuspGL

theorem finsum_mem_mul_sub_sum {G : Type} [Finite G] (S : Set G) (c : ℂ) (φ : G → ℂ) (T : Finset ℕ)
    (a : ℕ → ℂ) (ψ : ℕ → G → ℂ) :
    ∑ᶠ g ∈ S, (c * φ g - ∑ k ∈ T, a k * ψ k g) = c * (∑ᶠ g ∈ S, φ g) - ∑ k ∈ T, a k * ∑ᶠ g ∈ S, ψ k g := by
  have hS : S.Finite := Set.toFinite S
  simp only [finsum_mem_eq_finite_toFinset_sum _ hS]
  rw [Finset.sum_sub_distrib, Finset.sum_comm]
  simp only [Finset.mul_sum]

theorem card_filter_mul_pow_modEq (q n i l : ℕ) (hq : 1 < q) (hn : 0 < n) (hi : i ≤ n) :
    ((Finset.range (q ^ n - 1)).filter (fun k => k * q ^ i ≡ l [MOD (q ^ n - 1)])).card = 1 := by
  set N := q ^ n - 1 with hN
  have hq1 : 1 ≤ q ^ n := Nat.one_le_pow _ _ (by omega)
  have hqn : q ≤ q ^ n := Nat.le_self_pow (by omega) q
  have hNpos : 0 < N := by omega
  have hcop : Nat.Coprime (q ^ i) N := by
    have h1 : Nat.Coprime (q ^ n) N := by
      rw [hN, Nat.coprime_self_sub_right hq1]
      exact Nat.coprime_one_right _
    exact (h1.coprime_dvd_left (dvd_pow_self q (by omega))).pow_left i
  have uniq : ∀ a b, a ∈ Finset.range N → b ∈ Finset.range N →
      a * q ^ i % N = b * q ^ i % N → a = b := by
    intro a b ha hb hab
    have hmod : a ≡ b [MOD N] := Nat.ModEq.cancel_right_of_coprime (Nat.Coprime.gcd_eq_one hcop.symm) hab
    have ha' := Nat.mod_eq_of_lt (Finset.mem_range.mp ha)
    have hb' := Nat.mod_eq_of_lt (Finset.mem_range.mp hb)
    unfold Nat.ModEq at hmod
    omega
  obtain ⟨k, hk, hkeq⟩ := Finset.surj_on_of_inj_on_of_card_le (s := Finset.range N) (t := Finset.range N)
    (fun k _ => k * q ^ i % N) (fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hNpos))
    (fun a b ha hb hab => uniq a b ha hb hab) le_rfl (l % N) (Finset.mem_range.mpr (Nat.mod_lt _ hNpos))
  rw [Finset.card_eq_one]
  refine ⟨k, ?_⟩
  ext k'
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hk', h'⟩
    have h'' : k' * q ^ i % N = l % N := h'
    exact uniq k' k hk' hk (h''.trans hkeq)
  · rintro rfl
    exact ⟨hk, hkeq.symm⟩

theorem sum_mul_card_filter_modEq (q n l : ℕ) (hq : 1 < q) (hn : 0 < n) (A : ℕ → ℂ)
    (hA : ∀ k i : ℕ, k * q ^ i ≡ l [MOD (q ^ n - 1)] → A k = A l) :
    ∑ k ∈ Finset.range (q ^ n - 1),
      A k * (((Finset.range n).filter (fun i => k * q ^ i ≡ l [MOD (q ^ n - 1)])).card : ℂ) = n * A l := by
  have key : ∀ i ∈ Finset.range n, ∑ k ∈ Finset.range (q ^ n - 1),
      (if k * q ^ i ≡ l [MOD (q ^ n - 1)] then A k else 0) = A l := by
    intro i hi
    rw [← Finset.sum_filter]
    obtain ⟨k, hk⟩ := Finset.card_eq_one.mp
      (card_filter_mul_pow_modEq q n i l hq hn (Finset.mem_range.mp hi).le)
    have hmem : k ∈ (Finset.range (q ^ n - 1)).filter (fun k => k * q ^ i ≡ l [MOD (q ^ n - 1)]) := by
      rw [hk]; exact Finset.mem_singleton_self k
    rw [hk, Finset.sum_singleton]
    exact hA k i (Finset.mem_filter.mp hmem).2
  calc ∑ k ∈ Finset.range (q ^ n - 1),
        A k * (((Finset.range n).filter (fun i => k * q ^ i ≡ l [MOD (q ^ n - 1)])).card : ℂ)
      = ∑ k ∈ Finset.range (q ^ n - 1), ∑ i ∈ Finset.range n,
          (if k * q ^ i ≡ l [MOD (q ^ n - 1)] then A k else 0) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
    _ = ∑ i ∈ Finset.range n, ∑ k ∈ Finset.range (q ^ n - 1),
          (if k * q ^ i ≡ l [MOD (q ^ n - 1)] then A k else 0) := Finset.sum_comm
    _ = ∑ i ∈ Finset.range n, A l := Finset.sum_congr rfl key
    _ = n * A l := by simp

theorem exists_minpoly_eq_of_irreducible (F : Type) [Field F] [Finite F] (f : F[X]) (hm : f.Monic)
    (hf : Irreducible f) (h0 : f.coeff 0 ≠ 0) (m : ℕ) :
    ∃ α : AlgebraicClosure F, α ^ (Nat.card F ^ (f.natDegree * m) - 1) = 1 ∧ minpoly F α = f := by
  obtain ⟨α, hα⟩ : ∃ α : AlgebraicClosure F, aeval α f = 0 :=
    IsAlgClosed.exists_aeval_eq_zero (AlgebraicClosure F) f (degree_pos_of_irreducible hf).ne'
  have hmin : minpoly F α = f := (minpoly.eq_of_irreducible_of_monic hf hα hm).symm
  refine ⟨α, ?_, hmin⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    apply h0
    have h := coeff_zero_eq_aeval_zero' (R := F) (A := AlgebraicClosure F) f
    rw [hα] at h
    exact (algebraMap F (AlgebraicClosure F)).injective (by rw [h, map_zero])
  have hint : IsIntegral F α := ⟨f, hm, by rwa [← aeval_def]⟩
  have : FiniteDimensional F (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) := Module.finite_of_finite F
  let _ : Fintype (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F))) = Nat.card F ^ f.natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := F),
      IntermediateField.adjoin.finrank hint, hmin]
  have hβ : (⟨α, IntermediateField.mem_adjoin_simple_self F α⟩ : (IntermediateField.adjoin F ({α} : Set (AlgebraicClosure F)))) ≠ 0 := by
    intro h; apply hα0; exact congrArg Subtype.val h
  have h1 := FiniteField.pow_card_sub_one_eq_one _ hβ
  rw [hcard] at h1
  have h2 : α ^ (Nat.card F ^ f.natDegree - 1) = 1 := by
    have := congrArg Subtype.val h1
    simpa using this
  obtain ⟨r, hr⟩ : Nat.card F ^ f.natDegree - 1 ∣ Nat.card F ^ (f.natDegree * m) - 1 := by
    exact Nat.pow_sub_one_dvd_pow_sub_one (Nat.card F) (dvd_mul_right _ _)
  rw [hr, pow_mul, h2, one_pow]

theorem eq_zero_of_ipGL_rootSum_eq_zero (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (φ : Module.End F V → ℂ)
    (hc : IsClassFn φ) (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V)
    (h : ∀ l, ipGL φ (fun g : Module.End F V => rootSum θ l (LinearMap.charpoly g)) = 0)
    (g : Module.End F V) (hg : IsUnit g) : φ g = 0 := by
  have hc0 := torus_fourier_injective F θ hθ (Module.finrank F V) hn
    (fun α => ((Module.finrank F V / (minpoly F α).natDegree : ℕ) : ℂ) *
      mass φ (minpoly F α ^ (Module.finrank F V / (minpoly F α).natDegree)))
    (fun l => by rw [← GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_eq_torusSum F V θ φ hc hp hn l]; exact h l)
  by_cases hex : ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m
  swap
  · exact GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow F V φ hc hp hn g hex
  obtain ⟨f, m, hfm, hfi, hm, hcp⟩ := hex
  apply GlobalTheory.T.primitiveEndClassFunction_zero_of_charpoly_mass_zero F V φ hc hp g
  have hdeg : f.natDegree * m = Module.finrank F V := by
    have := LinearMap.charpoly_natDegree g
    rw [hcp, natDegree_pow] at this
    rw [mul_comm]; exact this
  have hfdeg : 0 < f.natDegree := natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hfi)
  have h0 : f.coeff 0 ≠ 0 := by
    intro h0
    have hc0' : (LinearMap.charpoly g).coeff 0 = 0 := by
      rw [hcp, coeff_zero_eq_eval_zero, eval_pow, ← coeff_zero_eq_eval_zero, h0, zero_pow hm.ne']
    have hdet := LinearMap.det_eq_sign_charpoly_coeff g
    rw [hc0', mul_zero] at hdet
    have hu : IsUnit (LinearMap.det g) := LinearMap.isUnit_iff_isUnit_det g |>.mp hg
    rw [hdet] at hu
    exact not_isUnit_zero hu
  obtain ⟨α, hα1, hαmin⟩ := exists_minpoly_eq_of_irreducible F f hfm hfi h0 m
  rw [hdeg] at hα1
  have hcα := hc0 α hα1
  simp only [hαmin] at hcα
  have hdiv : Module.finrank F V / f.natDegree = m := by
    rw [← hdeg]; exact Nat.mul_div_cancel_left m hfdeg
  rw [hdiv] at hcα
  rw [hcp]
  exact (mul_eq_zero.mp hcα).resolve_left (Nat.cast_ne_zero.mpr hm.ne')

theorem expand_primitive (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (θ : AlgebraicClosure F →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure F, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) (φ : Module.End F V → ℂ)
    (hc : IsClassFn φ) (hp : IsPrimitive φ) (hn : 0 < Module.finrank F V)
    (g : Module.End F V) (hg : IsUnit g) :
    glCard F (Module.finrank F V) * (Module.finrank F V : ℂ) * φ g =
      ∑ k ∈ Finset.range (Nat.card F ^ Module.finrank F V - 1),
        ipGL φ (fun g : Module.End F V => rootSum θ k (LinearMap.charpoly g)) * psi (rootSum θ k) V g := by
  classical
  have : Finite (Module.End F V) := Module.finite_of_finite F
  set n := Module.finrank F V with hn_def
  set T := Finset.range (Nat.card F ^ n - 1) with hT
  set R : ℕ → Module.End F V → ℂ := fun k g => rootSum θ k (LinearMap.charpoly g) with hR
  set a : ℕ → ℂ := fun k => ipGL φ (R k) with ha
  set ψ : ℕ → Module.End F V → ℂ := fun k => psi (rootSum θ k) V with hψ
  set c : ℂ := glCard F n * (n : ℂ) with hc_def
  set D : Module.End F V → ℂ := fun x => c * φ x - ∑ k ∈ T, a k * ψ k x with hD
  have hDc : IsClassFn D := by
    intro e x
    simp only [hD, hψ]
    rw [hc e x]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [psi_conj F (rootSum θ k) V V e x]
  have hDp : IsPrimitive D := by
    intro A h1 h2 x hx
    have := finsum_mem_mul_sub_sum (nilRad A) c (fun y => φ (x + y)) T a (fun k y => ψ k (x + y))
    simp only [hD]
    rw [this, hp A h1 h2 x hx]
    have hz : ∀ k, ∑ᶠ y ∈ nilRad A, ψ k (x + y) = 0 := fun k =>
      GlobalTheory.T.isPrimitiveEndClassFunction_invariantSubspaceMobiusInverse F V (rootSum θ k) (rootSum_isAdditive_and_pow_X_sub_one F θ k).1 A h1 h2 x hx
    simp [hz]
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have horth : ∀ l, ipGL D (fun x : Module.End F V => rootSum θ l (LinearMap.charpoly x)) = 0 := by
    intro l
    have hexp : ∀ x, D x * star (R l x) = c * (φ x * star (R l x)) - ∑ k ∈ T, a k * (ψ k x * star (R l x)) := by
      intro x
      simp only [hD, sub_mul, Finset.sum_mul, mul_assoc]
    have hsum := finsum_mem_mul_sub_sum {x : Module.End F V | IsUnit x} c (fun x => φ x * star (R l x)) T a
      (fun k x => ψ k x * star (R l x))
    have h30342 : ∀ k, ipGL (ψ k) (R l) = glCard F n *
        (((Finset.range n).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)])).card : ℂ) :=
      fun k => GlobalTheory.T.invertibleEndInnerProduct_rootPowerSum_mobius F V θ hθ hn k l
    have hA : ∀ k i : ℕ, k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)] → a k = a l :=
      fun k i hki => GlobalTheory.T.innerProduct_rootPowerSum_eq_of_frobenius_modEq F V θ φ hc hp hn k l i hki
    have hmain := sum_mul_card_filter_modEq (Nat.card F) n l hq hn a hA
    show ∑ᶠ x ∈ {x : Module.End F V | IsUnit x}, D x * star (R l x) = 0
    simp only [hexp]
    rw [hsum]
    have e1 : ∑ᶠ x ∈ {x : Module.End F V | IsUnit x}, φ x * star (R l x) = a l := rfl
    have e2 : ∀ k, ∑ᶠ x ∈ {x : Module.End F V | IsUnit x}, ψ k x * star (R l x) = ipGL (ψ k) (R l) :=
      fun k => rfl
    simp only [e1, e2, h30342]
    have e3 : ∑ k ∈ T, a k * (glCard F n *
        (((Finset.range n).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)])).card : ℂ)) =
        glCard F n * ∑ k ∈ T, a k *
        (((Finset.range n).filter (fun i => k * Nat.card F ^ i ≡ l [MOD (Nat.card F ^ n - 1)])).card : ℂ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e3, hT, hmain, hc_def]
    ring
  have hz := eq_zero_of_ipGL_rootSum_eq_zero F V θ hθ D hDc hDp hn horth g hg
  simp only [hD] at hz
  exact sub_eq_zero.mp hz

end GlobalTheory.CuspGL
