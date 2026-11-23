import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonneAt
import ReciprocityTheory.DualLattices.ExistsPrimitiveRoot

noncomputable section

open CategoryTheory WittVector Ideal TensorProduct Coalgebra

namespace GlobalTheory.PrismModel

open GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

section Eps

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (span {(p : O)}) O]

private theorem zeta_add_pow_p_pow_eq_zeta (ε : PreTilt O p) (n k : ℕ) :
    zeta ε (n + k) ^ p ^ k = zeta ε n := by
  induction k with
  | zero => simp
  | succ k ih => rw [← add_assoc, pow_succ', pow_mul, zeta_succ_pow, ih]

theorem isPrimitiveSystem_of_one {ε : PreTilt O p} (h : IsPrimitiveRoot (zeta ε 1) p) :
    IsPrimitiveSystem ε := by
  intro n
  cases n with
  | zero =>
    rw [pow_zero, IsPrimitiveRoot.one_right_iff]
    have h0 := zeta_add_pow_p_pow_eq_zeta ε 0 1
    rw [zero_add, pow_one] at h0
    rw [← h0, h.pow_eq_one]
  | succ n =>
    have h1 : zeta ε (n + 1) ^ p ^ n = zeta ε 1 := by
      have h2 := zeta_add_pow_p_pow_eq_zeta ε 1 n
      rwa [add_comm 1 n] at h2
    rw [IsPrimitiveRoot.iff_orderOf]
    apply orderOf_eq_prime_pow
    · rw [h1]
      exact h.ne_one (Fact.out : p.Prime).one_lt
    · rw [pow_succ, pow_mul, h1, h.pow_eq_one]

theorem frobenius_mu (ε : PreTilt O p) :
    frobenius (Sandwich.mu ε) = frobenius (xi ε) * Sandwich.mu ε := by
  have key : frobenius (Sandwich.nu ε) = Sandwich.mu ε := by
    rw [Sandwich.nu, map_sub, map_one, frobenius_eq_map_frobenius, map_teichmuller, Sandwich.root,
      frobenius_apply_frobeniusEquiv_symm]
    rfl
  conv_lhs => rw [← xi_mul_nu ε]
  rw [map_mul, key]

theorem theta_xi [IsDomain O] {ε : PreTilt O p} (hε : IsPrimitiveSystem ε) :
    fontaineTheta O p (xi ε) = 0 := by
  have h1 := hε 1
  rw [pow_one] at h1
  rw [xi, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller]
  exact h1.geom_sum_eq_zero (Fact.out : p.Prime).one_lt

end Eps

theorem isIntegers_padicComplex (p : ℕ) [Fact p.Prime] : IsIntegers 𝓞_ℂ_[p] ℂ_[p] := by
  have hI := PadicComplexInt.integers p
  refine ⟨hI.hom_inj, fun x => ?_⟩
  rw [PadicComplex.norm_eq_norm]
  constructor
  · rintro ⟨a, rfl⟩
    exact Valued.toNormedField.norm_le_one_iff.2 (hI.map_le_one a)
  · intro hx
    exact hI.exists_of_le_one (Valued.toNormedField.norm_le_one_iff.1 hx)

theorem exists_system (p : ℕ) [Fact p.Prime] (C : Type) [NontriviallyNormedField C]
    [NormedAlgebra ℚ_[p] C] [IsAlgClosed C] (O : Type) [CommRing O] [Algebra O C]
    (H : IsIntegers O C) [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] :
    ∃ ε : PreTilt O p, IsPrimitiveSystem ε := by
  have : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra ℚ_[p]
  have : CharZero C := (RingHom.charZero_iff (algebraMap ℚ_[p] C).injective).mp inferInstance
  have hv : (NormedField.valuation (K := C)).Integers O :=
    { hom_inj := H.inj
      map_le_one := fun a => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm]
        exact (H.mem_iff _).1 ⟨a, rfl⟩
      exists_of_le_one := fun r hr => by
        rw [NormedField.valuation_apply, ← NNReal.coe_le_one, coe_nnnorm] at hr
        exact (H.mem_iff r).2 hr }
  obtain ⟨ε, hε⟩ := ReciprocityTheory.PGsh.exists_eps (p := p) C NormedField.valuation O hv
  exact ⟨ε, isPrimitiveSystem_of_one hε⟩

theorem at_padicComplex (h : PrismaticDieudonne) (p : ℕ) [Fact p.Prime] :
    ∃ (_ : Fact ¬IsUnit (p : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
      (ε : PreTilt 𝓞_ℂ_[p] p) (hε : IsPrimitiveSystem ε), PrismaticDieudonneAt hε := by
  have H := isIntegers_padicComplex p
  have i1 : Fact ¬IsUnit (p : 𝓞_ℂ_[p]) := ⟨IsIntegers.not_isUnit (p := p) H⟩
  have i2 : IsAdicComplete (span {(p : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p] := IsIntegers.isAdicComplete (p := p) H
  obtain ⟨ε, hε⟩ := exists_system p ℂ_[p] 𝓞_ℂ_[p] H
  exact ⟨i1, i2, ε, hε, h p ℂ_[p] 𝓞_ℂ_[p] H ε hε⟩

section Mu

variable {O A : Type} [CommRing O] [CommRing A] [Bialgebra O A]

private theorem lTensor_rid_one_tmul_eq_one_tmul_rid (s : A →ₗ[O] O) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A) (1 ⊗ₜ c) =
      1 ⊗ₜ TensorProduct.rid O A (s.lTensor A c) := by
  rw [LinearMap.lTensor_tmul]
  rfl

private theorem lTensor_rid_assoc_tmul_eq_smul (s : A →ₗ[O] O) (t : A ⊗[O] A) (y : A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (TensorProduct.assoc O A A A (t ⊗ₜ y)) = s y • t := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul u v => simp [TensorProduct.tmul_smul]
  | add t₁ t₂ h₁ h₂ => rw [TensorProduct.add_tmul, map_add, map_add, h₁, h₂, smul_add]

private theorem lTensor_rid_assoc_rTensor_comul_eq_comul_rid (s : A →ₗ[O] O) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (TensorProduct.assoc O A A A (comul.rTensor A c)) =
      comul (TensorProduct.rid O A (s.lTensor A c)) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [LinearMap.rTensor_tmul, lTensor_rid_assoc_tmul_eq_smul]
    simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]

private theorem lTensor_rid_assoc_lTensor_comul_eq_tmul_one (s : A →ₗ[O] O)
    (hs : ∀ a, TensorProduct.rid O A (s.lTensor A (comul a)) = s a • 1) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (comul.lTensor A c) = TensorProduct.rid O A (s.lTensor A c) ⊗ₜ 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul x y =>
    rw [LinearMap.lTensor_tmul, LinearMap.lTensor_tmul]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hs]
    simp [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂, TensorProduct.add_tmul]

private theorem lTensor_rid_flip_one_eq_self_of_apply_one (s : A →ₗ[O] O) (h1 : s 1 = 1) (c : A ⊗[O] A) :
    LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)
      (((TensorProduct.mk O A A).flip 1).lTensor A c) = c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [h1]
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]

theorem exists_cobOne_of_integral (s : A →ₗ[O] O) (h1 : s 1 = 1)
    (hs : ∀ a, TensorProduct.rid O A (s.lTensor A (comul a)) = s a • 1)
    {c : A ⊗[O] A} (hc : cobTwo O A c = 0) : ∃ b, cobOne O A b = c := by
  refine ⟨-(TensorProduct.rid O A (s.lTensor A c)), ?_⟩
  have key := congrArg (LinearMap.lTensor A ((TensorProduct.rid O A).toLinearMap ∘ₗ s.lTensor A)) hc
  rw [map_zero, cobTwo_apply, map_sub, map_add, map_sub, lTensor_rid_one_tmul_eq_one_tmul_rid, lTensor_rid_assoc_rTensor_comul_eq_comul_rid,
    lTensor_rid_assoc_lTensor_comul_eq_tmul_one s hs, lTensor_rid_flip_one_eq_self_of_apply_one s h1, sub_eq_zero] at key
  rw [map_neg, cobOne_apply]
  refine Eq.trans ?_ key
  abel

variable {p : ℕ} [Fact p.Prime]

private theorem coeff_zero_one_eq_one (n : ℕ) :
    (Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap :
      (PDivGroup.mu p O).A n →ₗ[O] O) 1 = 1 := by
  simp

private theorem coeff_zero_lTensor_comul_eq_smul_one (n : ℕ) (a : (PDivGroup.mu p O).A n) :
    TensorProduct.rid O _ ((Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap :
      (PDivGroup.mu p O).A n →ₗ[O] O).lTensor _ (comul a)) =
      (Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap :
      (PDivGroup.mu p O).A n →ₗ[O] O) a • 1 := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, add_smul]
  | single g r =>
    by_cases hg : g = 0
    · subst hg
      simp
      rw [AddMonoidAlgebra.one_def, AddMonoidAlgebra.smul_single', mul_one]
    · simp [hg]

theorem subsingleton_vecExt_mu [IsDomain O] (hp : (p : O) ≠ 0) :
    Subsingleton (PDivGroup.mu p O).VecExt := by
  have hb : ∀ c : (PDivGroup.mu p O).cocycles, ∀ n,
      ∃ b : (PDivGroup.mu p O).A n, cobOne O _ b = c.1 n := fun c n =>
    exists_cobOne_of_integral (A := (PDivGroup.mu p O).A n)
      (Finsupp.lapply (0 : ZMod (p ^ n)) ∘ₗ (AddMonoidAlgebra.coeffLinearEquiv O).toLinearMap)
      (coeff_zero_one_eq_one n) (coeff_zero_lTensor_comul_eq_smul_one n) (mem_symCocycles.1 (c.2 n).1).1
  have hsurj : ∀ c : (PDivGroup.mu p O).cocycles, c ∈ LinearMap.range (PDivGroup.mu p O).cob := by
    intro c
    choose b hb' using hb c
    have hres : ∀ n, (PDivGroup.mu p O).res n (b (n + 1)) = b n := by
      intro n
      rw [← sub_eq_zero]
      apply (PDivGroup.mu p O).eq_zero_of_cobOne_eq_zero hp n
      rw [map_sub, ← pullTwo_cobOne, hb', hb', (c.2 n).2, sub_self]
    exact ⟨⟨b, hres⟩, Subtype.ext (funext fun n => hb' n)⟩
  refine ⟨fun x y => ?_⟩
  induction x using Submodule.Quotient.induction_on with
  | H x =>
  induction y using Submodule.Quotient.induction_on with
  | H y =>
  exact (Submodule.Quotient.eq _).2 (hsurj _)

theorem rigExt_mu_bijective [IsDomain O] [IsAdicComplete (span {(p : O)}) O] (hp : (p : O) ≠ 0) :
    Function.Bijective
      ((PDivGroup.mu p O).rigOfOmega ∘ₗ LinearMap.toSpanSingleton O _ (dlogT p O)) := by
  have hd := toSpanSingleton_dlogT_bijective p O
  have := subsingleton_vecExt_mu hp
  refine ⟨((PDivGroup.mu p O).rigOfOmega_injective hp).comp hd.1, fun x => ?_⟩
  obtain ⟨w, hw⟩ := ((PDivGroup.mu p O).exact_rigOfOmega_rigToExt x).1 (Subsingleton.elim _ _)
  obtain ⟨a, rfl⟩ := hd.2 w
  exact ⟨a, hw⟩

end Mu

end GlobalTheory.PrismModel
