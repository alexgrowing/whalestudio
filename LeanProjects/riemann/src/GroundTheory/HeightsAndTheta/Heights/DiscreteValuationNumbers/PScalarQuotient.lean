import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PDivCycleMul
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ScalarQuotient

section ClassNumbers

variable {K : Type*} [DecidableEq K] {ι : K → Type*}
variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem classNum_add {σ : Type*} (cls : σ → K → ℤ) (H₁ H₂ : MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (H₁ + H₂) Q W = classNum cls H₁ Q W + classNum cls H₂ Q W := by
  classical
  unfold classNum
  have ext : ∀ (H : MvPolynomial σ ℤ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      ∑ μ ∈ H.support, H.coeff μ * vNumL W (classList cls μ ++ Q) =
        ∑ μ ∈ s, H.coeff μ * vNumL W (classList cls μ ++ Q) := by
    intro H s hs
    refine Finset.sum_subset hs fun μ _ hμ => ?_
    rw [MvPolynomial.mem_support_iff, not_not] at hμ
    rw [hμ, zero_mul]
  rw [ext (H₁ + H₂) (H₁.support ∪ H₂.support) support_add,
    ext H₁ (H₁.support ∪ H₂.support) Finset.subset_union_left,
    ext H₂ (H₁.support ∪ H₂.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [coeff_add, add_mul]

def classNumHom {σ : Type*} (cls : σ → K → ℤ) (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    MvPolynomial σ ℤ →+ ℤ where
  toFun H := classNum cls H Q W
  map_zero' := by simp [classNum]
  map_add' H₁ H₂ := classNum_add cls H₁ H₂ Q W

theorem classNum_sum {σ τ : Type*} (cls : σ → K → ℤ) (s : Finset τ) (H : τ → MvPolynomial σ ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (∑ t ∈ s, H t) Q W = ∑ t ∈ s, classNum cls (H t) Q W :=
  map_sum (classNumHom cls Q W) H s

theorem classNum_monomial {σ : Type*} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) (c : ℤ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum cls (monomial μ c) Q W = c * vNumL W (classList cls μ ++ Q) := by
  classical
  unfold classNum
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [support_monomial, if_neg hc, Finset.sum_singleton, coeff_monomial, if_pos rfl]

omit [DecidableEq K] in

theorem classList_diag {N : ℕ} (x : Fin N → K → ℤ) (i : Fin N) (j l : ℕ) :
    classList (Sum.elim x x) (Finsupp.single (Sum.inl i) j + Finsupp.single (Sum.inr i) l) =
      classList x (Finsupp.single i (j + l)) := by
  unfold classList
  congr 1
  simp [Finsupp.toMultiset_add, Finsupp.toMultiset_single, Multiset.map_nsmul]

theorem classNum_psumExpansion_diag {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ) (i : Fin N)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    classNum (Sum.elim x x) (psumExpansion N k i) Q W =
      k * vNumL W (classList x (Finsupp.single i (k - 1)) ++ Q) := by
  unfold psumExpansion
  rw [classNum_sum]
  have key : ∀ j ∈ Finset.range k,
      classNum (Sum.elim x x) (X (Sum.inl i) ^ j * X (Sum.inr i) ^ (k - 1 - j)) Q W =
        vNumL W (classList x (Finsupp.single i (k - 1)) ++ Q) := by
    intro j hj
    have e : j + (k - 1 - j) = k - 1 := by
      have := Finset.mem_range.mp hj
      omega
    rw [X_pow_eq_monomial, X_pow_eq_monomial, monomial_mul, one_mul, classNum_monomial, one_mul,
      classList_diag, e]
  rw [Finset.sum_congr rfl key, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

theorem classNum_psum {N : ℕ} (x : Fin N → K → ℤ) (m : ℕ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    classNum x (psum (Fin N) ℤ m) Q W =
      ∑ i, vNumL W (classList x (Finsupp.single i m) ++ Q) := by
  unfold psum
  rw [classNum_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [X_pow_eq_monomial, classNum_monomial, one_mul]

theorem sum_classNum_psumExpansion_diag {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ)
    (Q : List (K → ℤ)) (W : Ideal (MRing ι O)) :
    ∑ i, classNum (Sum.elim x x) (psumExpansion N k i) Q W =
      k * classNum x (psum (Fin N) ℤ (k - 1)) Q W := by
  simp_rw [classNum_psumExpansion_diag, classNum_psum, Finset.mul_sum]

end ClassNumbers

section Divisors

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem divCycle_support_finite (P : Ideal (MRing ι O)) (f : MRing ι O) :
    (Function.support (divCycle P f)).Finite := by
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _ (P ⊔ Ideal.span {f})).subset ?_
  intro W hW
  rw [Function.mem_support] at hW
  unfold divCycle at hW
  split_ifs at hW with h
  · exact h.1
  · exact absurd rfl hW

omit [Fintype K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O] in

theorem divCycle_unit (P : Ideal (MRing ι O)) (u : Oˣ) : divCycle P (C (u : O)) = 0 := by
  funext W
  unfold divCycle
  rw [dif_neg]
  · rfl
  rintro ⟨h, -⟩
  have hW : W.IsPrime := h.1.1
  have : P ⊔ Ideal.span {(C (u : O) : MRing ι O)} = ⊤ := by
    rw [Ideal.span_singleton_eq_top.mpr (u.isUnit.map C), sup_top_eq]
  exact hW.ne_top (top_le_iff.mp (this ▸ h.1.2))

theorem divCycle_const (P : Ideal (MRing ι O)) [P.IsPrime]
    (hP : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P) {ϖ : O} (hϖ : ϖ ≠ 0) (u : Oˣ) (n : ℕ) :
    divCycle P (C ((u : O) * ϖ ^ n)) = fun W => (n : ℤ) * divCycle P (C ϖ) W := by
  induction n with
  | zero =>
    funext W
    simp [divCycle_unit]
  | succ n ih =>
    have hmul : (C ((u : O) * ϖ ^ (n + 1)) : MRing ι O) = C ((u : O) * ϖ ^ n) * C ϖ := by
      rw [← map_mul, pow_succ, mul_assoc]
    rw [hmul, DivCycleMul.proof O K ι P _ _ inferInstance
      (hP _ (mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ))) (hP _ hϖ), ih]
    funext W
    simp only [Pi.add_apply]
    push_cast
    ring

theorem ratDiv_const (P : Ideal (MRing ι O)) [P.IsPrime]
    (hP : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P) {ϖ : O} (hϖ : ϖ ≠ 0) (u : Oˣ) (n : ℕ) :
    ratDiv P (C ((u : O) * ϖ ^ n)) 1 = fun W => (n : ℤ) * divCycle P (C ϖ) W := by
  funext W
  unfold ratDiv
  rw [divCycle_const P hP hϖ u n, divCycle_one, sub_zero]

variable [DecidableEq K]

omit [Fintype K] [∀ k, Fintype (ι k)] [IsDomain O] [IsDiscreteValuationRing O] in

theorem isVerticalDivisor_const (P : Ideal (MRing ι O)) [P.IsPrime] (ϖ : O) (u : Oˣ) (n : ℕ)
    (hP : (C ((u : O) * ϖ ^ n) : MRing ι O) ∉ P) :
    IsVerticalDivisor P ϖ 0 (C ((u : O) * ϖ ^ n)) 1 := by
  refine IsVerticalDivisor.of_unit_off_special
    ⟨0, 0, isWeightedHomogeneous_C _ _, isWeightedHomogeneous_one _ _, by funext k; simp⟩ hP
    (Ideal.IsPrime.ne_top' ∘ (Ideal.eq_top_of_isUnit_mem _ · isUnit_one)) ?_
  intro W hW _ _ hϖW
  refine ⟨1, C ((u : O) * ϖ ^ n), (Ideal.ne_top_iff_one W).mp hW.ne_top, ?_, ?_⟩
  · rw [map_mul, map_pow]
    intro h
    rcases hW.mem_or_mem h with h1 | h1
    · exact hW.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (u.isUnit.map C))
    · exact hϖW (hW.mem_of_pow_mem _ h1)
  · rw [one_mul, mul_one, sub_self]
    exact Submodule.zero_mem _

theorem pairNum_const (P : Ideal (MRing ι O)) [P.IsPrime]
    (hP : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ P) {ϖ : O} (hϖ : ϖ ≠ 0) (u : Oˣ) (n : ℕ)
    {N : ℕ} (x : Fin N → K → ℤ) (k : ℕ) (Q : List (K → ℤ)) :
    pairNum P x x (fun _ => C ((u : O) * ϖ ^ n)) (fun _ => 1) (psumExpansion N k) Q =
      (k : ℤ) * n * cycEval (fun W => classNum x (psum (Fin N) ℤ (k - 1)) Q W)
        (divCycle P (C ϖ)) := by
  unfold pairNum cycEval
  simp only [ratDiv_const P hP hϖ u n]
  have hfin := divCycle_support_finite P (C ϖ)
  have sub : ∀ h : Ideal (MRing ι O) → ℤ, (∀ W, divCycle P (C ϖ) W = 0 → h W = 0) →
      ∑ᶠ W, h W = ∑ W ∈ hfin.toFinset, h W := by
    intro h hh
    refine finsum_eq_sum_of_support_subset h fun W hW => ?_
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    exact fun hD => hW (hh W hD)
  rw [sub _ (fun W hW => by simp [hW])]
  rw [Finset.sum_congr rfl (fun i _ => sub _ (fun W hW => by simp [hW]))]
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [← Finset.mul_sum, sum_classNum_psumExpansion_diag]
  ring

end Divisors

end ScalarQuotient

theorem ScalarQuotient.proof (hFI : FlagIndependence.Statement) : ScalarQuotient.Statement := by
  intro O _ _ _ ϖ hϖ Ω _ _ K _ _ ι _ y d hmod N E _ _ B B' n u hlat w w' x x' f g hpair k Gs hGs
    Q hQ
  have : (pointIdeal O y).IsPrime := hmod.multiProj.isPrime
  have hC : ∀ a : O, a ≠ 0 → (C a : MRing ι O) ∉ pointIdeal O y := by
    intro a ha hmem
    have h1 : a ∈ (pointIdeal O y).comap (C : O →+* MRing ι O) := hmem
    rw [hmod.noTorsion] at h1
    exact ha (Ideal.mem_bot.mp h1)
  have hγ : (u : O) * ϖ ^ n ≠ 0 := mul_ne_zero u.ne_zero (pow_ne_zero _ hϖ.ne_zero)
  have hγΩ : algebraMap O Ω ((u : O) * ϖ ^ n) ≠ 0 := by
    intro h0
    apply hC _ hγ
    change pointConeMap O y (C _) = 0
    rw [pointConeMap, aeval_C, MvPolynomial.algebraMap_apply, h0, map_zero]
  set γ : Ω := algebraMap O Ω ((u : O) * ϖ ^ n) with hγdef
  let w₂ : Module.Basis (Fin N) Ω E := w.unitsSMul fun _ => Units.mk0 γ hγΩ
  have hrep : ∀ (z : E) (j : Fin N), w₂.repr (γ • z) j = w.repr z j := by
    intro z j
    simp [w₂, Module.Basis.repr_unitsSMul, Units.smul_def, hγΩ]
  have hw₂ : ∀ i, w₂ i = γ • w i := by
    intro i
    simp [w₂, Module.Basis.unitsSMul_apply, Units.smul_def]
  have hpair₂ : IsFlagPair ϖ y B B' w w₂ x x (fun _ => C ((u : O) * ϖ ^ n)) (fun _ => 1) := by
    refine ⟨hpair.flag, ⟨fun c hc i => ?_⟩, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
    · rw [← hpair.flag.graded c hc i]
      ext s
      constructor
      · rintro ⟨v, hv, hz, rfl⟩
        obtain ⟨z₀, hz₀, rfl⟩ := (hlat c hc v).mp hv
        exact ⟨z₀, hz₀, fun j hj => by rw [← hrep]; exact hz j hj, (hrep z₀ i).symm⟩
      · rintro ⟨z₀, hz₀, hz, rfl⟩
        exact ⟨γ • z₀, (hlat c hc _).mpr ⟨z₀, hz₀, rfl⟩, fun j hj => by rw [hrep]; exact hz j hj,
          hrep z₀ i⟩
    · rw [hw₂, map_smul, Module.Basis.repr_self]
      simp [hij.ne]
    · rw [sub_self]
      exact ScalarQuotient.isVerticalDivisor_const _ ϖ u n (hC _ hγ)
    · rw [hw₂, map_smul, Module.Basis.repr_self]
      simp [hγdef]
  have hsame : SameGenericFibre ϖ B B' := by
    intro c hc
    refine ⟨fun v hv => ⟨n, ?_⟩, fun v hv => ⟨0, ?_⟩⟩
    · have h1 : γ • v ∈ B'.lat c := (hlat c hc _).mpr ⟨v, hv, rfl⟩
      have h2 := B'.stable c (algebraMap O Ω ((u⁻¹ : Oˣ) : O)) (Subalgebra.algebraMap_mem _ _) _ h1
      convert h2 using 1
      rw [hγdef, smul_smul, ← map_mul, ← mul_assoc, Units.inv_mul, one_mul, map_pow]
    · obtain ⟨z₀, hz₀, rfl⟩ := (hlat c hc v).mp hv
      rw [pow_zero, one_smul]
      exact B.stable c _ (Subalgebra.algebraMap_mem _ _) _ hz₀
  rw [hFI O ϖ hϖ Ω K ι y d hmod N E B B' hsame w w' w w₂ x x' x x f g _ _ hpair hpair₂ k
    (psum (Fin N) ℤ k) (isHomogeneous_psum N k) (psum_isSymmetric _ _ k) Gs (psumExpansion N k)
    hGs (isPairExpansion_psum N k) Q hQ]
  exact ScalarQuotient.pairNum_const _ hC hϖ.ne_zero u n x k Q

end

end GroundTheory.Heights₂.Heights.NumbersDVR
