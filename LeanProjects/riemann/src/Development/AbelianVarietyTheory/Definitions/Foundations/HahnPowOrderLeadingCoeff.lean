import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl

noncomputable section

open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

open GlobalTheory.KZ

section Hahn

variable {Ω : Type} [Field Ω]

theorem hahn_pow_order_leadingCoeff (s : HahnSeries ℚ Ω) (hs : s ≠ 0) (n : ℕ) :
    (s ^ n).order = n • s.order ∧ (s ^ n).leadingCoeff = s.leadingCoeff ^ n := by
  refine ⟨HahnSeries.order_pow s n, ?_⟩
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, HahnSeries.leadingCoeff_mul, ih, pow_succ]

private theorem hahnSeries_algebraMap_mul_coeff (c : Ω) (x : HahnSeries ℚ Ω) (r : ℚ) :
    (algebraMap Ω (HahnSeries ℚ Ω) c * x).coeff r = c * x.coeff r := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem hahn_transcendental {s : HahnSeries ℚ Ω} (hs : s ≠ 0) (ho : s.order < 0) : Transcendental Ω s := by
  rintro ⟨P, hP, hPs⟩
  have hlead : P.coeff P.natDegree ≠ 0 := Polynomial.leadingCoeff_ne_zero.2 hP
  have hls : s.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.2 hs
  have key : (Polynomial.aeval s P).coeff (P.natDegree • s.order) =
      P.coeff P.natDegree * s.leadingCoeff ^ P.natDegree := by
    rw [Polynomial.aeval_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ, Finset.sum_eq_zero]
    · rw [zero_add]
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [← (hahn_pow_order_leadingCoeff s hs P.natDegree).1,
        ← HahnSeries.leadingCoeff_eq, (hahn_pow_order_leadingCoeff s hs P.natDegree).2]
    · intro k hk
      rw [Algebra.smul_def, hahnSeries_algebraMap_mul_coeff]
      rw [HahnSeries.coeff_eq_zero_of_lt_order, mul_zero]
      rw [(hahn_pow_order_leadingCoeff s hs k).1, nsmul_eq_mul, nsmul_eq_mul]
      exact mul_lt_mul_of_neg_right (by exact_mod_cast Finset.mem_range.1 hk) ho
  rw [hPs] at key
  exact mul_ne_zero hlead (pow_ne_zero _ hls) (by simpa using key.symm)

end Hahn

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem mem_lev_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (f : X.K) :
    f ∈ lev X Γ' ↔ ∀ γ ∈ Γ', X.sl (ofSL γ) f = f := by
  unfold lev
  simp only [Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (c : Ω) : algebraMap Ω X.K c ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => (X.sl (ofSL γ)).commutes c

theorem jK_mem_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : X.jK ∈ lev X Γ' := (mem_lev_iff X Γ' _).2 fun γ _ => X.j_inv γ

theorem mdl_le_lev (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : mdl X Γ' S ≤ lev X Γ' := by
  unfold mdl
  exact inf_le_left

theorem jK_transcendental (X : Tower Ω ε) : Transcendental Ω X.jK := by
  have h1 : (X.exp X.jK).coeff (-1) ≠ 0 := by rw [X.j_exp.1]; exact one_ne_zero
  have hne : X.exp X.jK ≠ 0 := fun h => h1 (by rw [h]; rfl)
  have hord : (X.exp X.jK).order < 0 :=
    lt_of_le_of_lt (HahnSeries.order_le_of_coeff_ne_zero h1) (by norm_num)
  exact fun h => hahn_transcendental hne hord (h.algHom X.exp)

def levConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Ω →+* lev X Γ' :=
  (algebraMap Ω X.K).codRestrict (lev X Γ') (algebraMap_mem_lev X Γ')

def jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Polynomial Ω →+* lev X Γ' :=
  Polynomial.eval₂RingHom (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩

theorem coe_jPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    ((jPoly X Γ' P : lev X Γ') : X.K) = Polynomial.aeval X.jK P := by
  change (lev X Γ').subtype (Polynomial.eval₂ (levConst X Γ') ⟨X.jK, jK_mem_lev X Γ'⟩ P) = _
  rw [Polynomial.hom_eval₂, Polynomial.aeval_def]
  rfl

theorem jPoly_injective (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Function.Injective (jPoly X Γ') := by
  refine (injective_iff_map_eq_zero _).2 fun P hP => ?_
  have h : Polynomial.aeval X.jK P = 0 := by
    rw [← coe_jPoly, hP]; rfl
  by_contra hne
  exact jK_transcendental X ⟨P, hne, h⟩

def jRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : RatFunc Ω →+* lev X Γ' :=
  RatFunc.liftRingHom (jPoly X Γ') (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective _ (jPoly_injective X Γ'))

theorem jRat_algebraMap (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (P : Polynomial Ω) :
    jRat X Γ' (algebraMap (Polynomial Ω) (RatFunc Ω) P) = jPoly X Γ' P := RatFunc.liftRingHom_algebraMap _ _ P

theorem exp_injective (X : Tower Ω ε) : Function.Injective X.exp := (X.exp : X.K →+* HahnSeries ℚ Ω).injective

theorem exp_algebraMap_coeff (X : Tower Ω ε) (c : Ω) (r : ℚ) :
    (X.exp (algebraMap Ω X.K c)).coeff r = if r = 0 then c else 0 := by
  rw [AlgHom.commutes, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply, HahnSeries.ofPowerSeries_C]
  change (HahnSeries.single (0 : ℚ) c).coeff r = _
  split_ifs with h
  · rw [h]
    exact HahnSeries.coeff_single_same _ _
  · exact HahnSeries.coeff_single_of_ne h

theorem gal_algebraMap (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) (c : Ω) :
    X.gal s (algebraMap Ω X.K c) = algebraMap Ω X.K (s c) := by
  apply exp_injective X
  ext r
  rw [X.gal_exp, exp_algebraMap_coeff, exp_algebraMap_coeff]
  split_ifs <;> simp

theorem gal_jK (X : Tower Ω ε) (s : Ω ≃ₐ[ℚ] Ω) : X.gal s X.jK = X.jK := by
  apply exp_injective X
  ext r
  obtain ⟨n, hn⟩ := X.j_exp.2.2 r
  rw [X.gal_exp, hn, map_intCast]

theorem mem_mdl_iff (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (f : X.K) :
    f ∈ mdl X Γ' S ↔ f ∈ lev X Γ' ∧ ∀ s ∈ S, X.gal s f = f := by
  unfold mdl
  simp only [Subfield.mem_inf, Subfield.mem_iInf, RingHom.mem_eqLocusField]
  rfl

theorem algebraMap_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (c : Ω)
    (hc : ∀ s ∈ S, s c = c) : algebraMap Ω X.K c ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨algebraMap_mem_lev X Γ' c, fun s hs => by rw [gal_algebraMap, hc s hs]⟩

theorem jK_mem_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : X.jK ∈ mdl X Γ' S := (mem_mdl_iff X Γ' S _).2 ⟨jK_mem_lev X Γ', fun s _ => gal_jK X s⟩

theorem coe_jRat_X (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : ((jRat X Γ' RatFunc.X : lev X Γ') : X.K) = X.jK := by
  rw [← RatFunc.algebraMap_X, jRat_algebraMap, coe_jPoly, Polynomial.aeval_X]

def algConst (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra Ω (lev X Γ') := (levConst X Γ').toAlgebra

def algPoly (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (Polynomial Ω) (lev X Γ') := (jPoly X Γ').toAlgebra

def algRat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) : Algebra (RatFunc Ω) (lev X Γ') := (jRat X Γ').toAlgebra

def algMdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) : Algebra (mdl X Γ' S) (lev X Γ') :=
  (Subfield.inclusion (mdl_le_lev X Γ' S)).toAlgebra

section Instances

attribute [local instance] algConst algPoly algRat algMdl

theorem isScalarTower_poly_rat (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    IsScalarTower (Polynomial Ω) (RatFunc Ω) (lev X Γ') := IsScalarTower.of_algebraMap_eq fun P => (jRat_algebraMap X Γ' P).symm

theorem isScalarTower_mdl (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) :
    IsScalarTower (mdl X Γ' S) (lev X Γ') X.K := IsScalarTower.of_algebraMap_eq fun _ => rfl

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    ((algebraMap (RatFunc Ω) (lev X Γ') RatFunc.X : lev X Γ') : X.K) = X.jK :=
  coe_jRat_X X Γ'

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (c : Ω) :
    ((algebraMap Ω (lev X Γ') c : lev X Γ') : X.K) = algebraMap Ω X.K c := rfl

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    ((algebraMap (RatFunc Ω) (lev X Γ') RatFunc.X⁻¹ : lev X Γ') : X.K) = X.jK⁻¹ := by
  rw [map_inv₀, Subfield.coe_inv]
  show ((jRat X Γ' RatFunc.X : lev X Γ') : X.K)⁻¹ = _
  rw [coe_jRat_X]

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)) (x : mdl X Γ' S) :
    ((algebraMap (mdl X Γ' S) (lev X Γ') x : lev X Γ') : X.K) = x := rfl

example (X : Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) :
    algebraMap (Polynomial Ω) (lev X Γ') (Polynomial.X ^ 2 - Polynomial.C 1) ≠ 0 := by
  rw [← map_zero (algebraMap (Polynomial Ω) (lev X Γ'))]
  intro h
  have := jPoly_injective X Γ' h
  have h2 := congrArg (Polynomial.natDegree) this
  rw [Polynomial.natDegree_X_pow_sub_C, Polynomial.natDegree_zero] at h2
  exact absurd h2 (by norm_num)

end Instances

end GlobalTheory.K4
