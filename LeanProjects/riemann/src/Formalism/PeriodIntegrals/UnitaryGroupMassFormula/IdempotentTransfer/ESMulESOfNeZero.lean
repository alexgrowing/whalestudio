import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.Tr

open PI.Dv

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

abbrev cf (T : GoodSet K G) (s : T.S) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)

def phiS (T : GoodSet K G) (s : T.S) : Module.End K (T.W s) →ₗ[K] MonoidAlgebra K G where
  toFun X := ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x
  map_add' X Y := by
    simp only [mul_add, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [mul_smul_comm, map_smul, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring_nf

lemma phiS_apply (T : GoodSet K G) (s : T.S) (X : Module.End K (T.W s)) :
    phiS T s X = ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x :=
  rfl

lemma phiS_one (T : GoodSet K G) (s : T.S) : phiS T s 1 = eS T s := by
  simp only [phiS_apply, mul_one, eS]

lemma of_mul_eS (T : GoodSet K G) (s : T.S) (y : G) :
    MonoidAlgebra.of K G y * eS T s = phiS T s (T.tau s y) := by
  rw [eS, phiS_apply, Finset.mul_sum]
  simp_rw [mul_smul_comm, ← map_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun x => ?_)
  have h : (y * x)⁻¹ * y = x⁻¹ := by group
  simp only [Equiv.coe_mulLeft, h, cf]

lemma eS_mul_of (T : GoodSet K G) (s : T.S) (y : G) :
    eS T s * MonoidAlgebra.of K G y = phiS T s (T.tau s y) := by
  rw [eS, phiS_apply, Finset.sum_mul]
  simp_rw [smul_mul_assoc, ← map_mul]
  refine Fintype.sum_equiv (Equiv.mulRight y) _ _ (fun x => ?_)
  have h : LinearMap.trace K (T.W s) (T.tau s ((x * y)⁻¹ * y)) =
      LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
    rw [show (x * y)⁻¹ * y = y⁻¹ * x⁻¹ * y by group, (T.tau s).map_mul, (T.tau s).map_mul,
      LinearMap.trace_mul_comm, ← mul_assoc, ← (T.tau s).map_mul, mul_inv_cancel, (T.tau s).map_one, one_mul]
  simp only [Equiv.coe_mulRight, h, cf]

lemma mul_eS (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    a * eS T s = phiS T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of y => rw [of_mul_eS, Representation.asAlgebraHom_of]
  | add x y hx hy => rw [add_mul, hx, hy, map_add, map_add]
  | smul r x hx => rw [smul_mul_assoc, hx, map_smul, map_smul]

lemma eS_mul (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) :
    eS T s * a = phiS T s ((T.tau s).asAlgebraHom a) := by
  induction a using MonoidAlgebra.induction_on with
  | of y => rw [eS_mul_of, Representation.asAlgebraHom_of]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, map_add]
  | smul r x hx => rw [mul_smul_comm, hx, map_smul, map_smul]

lemma eS_comm (T : GoodSet K G) (s : T.S) (a : MonoidAlgebra K G) : a * eS T s = eS T s * a := by
  rw [mul_eS, eS_mul]

lemma scalar_of_comm (T : GoodSet K G) (s : T.S) (Z : Module.End K (T.W s))
    (h : ∀ g, Z * T.tau s g = T.tau s g * Z) : ∃ c : K, Z = c • 1 := by
  have hall : ∀ a : MonoidAlgebra K G, Z * (T.tau s).asAlgebraHom a = (T.tau s).asAlgebraHom a * Z := by
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of y => rw [Representation.asAlgebraHom_of, h]
    | add x y hx hy => rw [map_add, mul_add, add_mul, hx, hy]
    | smul r x hx => rw [map_smul, mul_smul_comm, smul_mul_assoc, hx]
  have hc : Z ∈ Set.center (Module.End K (T.W s)) := by
    rw [Semigroup.mem_center_iff]
    intro Y
    obtain ⟨a, rfl⟩ := T.irr s Y
    exact (hall a).symm
  obtain ⟨α, hα, hZ⟩ := Module.End.mem_center_iff.mp hc
  refine ⟨α, ?_⟩
  ext x
  rw [hZ]
  simp

lemma tau_eS_scalar (T : GoodSet K G) (s t : T.S) : ∃ c : K, (T.tau t).asAlgebraHom (eS T s) = c • 1 := by
  apply scalar_of_comm
  intro g
  rw [← Representation.asAlgebraHom_of, ← map_mul, ← map_mul, eS_comm]

lemma finrank_pos' (T : GoodSet K G) (s : T.S) : 0 < Module.finrank K (T.W s) := Module.finrank_pos

lemma tau_eS (T : GoodSet K G) (s : T.S) : (T.tau s).asAlgebraHom (eS T s) = 1 := by
  obtain ⟨c, hc⟩ := tau_eS_scalar T s s

  have hcomp : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) = c • LinearMap.id := by
    ext1 X
    obtain ⟨a, rfl⟩ := T.irr s X
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, ← mul_eS, map_mul, hc,
      LinearMap.smul_apply, LinearMap.id_apply, mul_smul_comm, mul_one]
  have hsum : ((T.tau s).asAlgebraHom.toLinearMap ∘ₗ phiS T s) =
      ∑ x : G, cf T s • ((LinearMap.trace K (T.W s) ∘ₗ LinearMap.mulLeft K (T.tau s x⁻¹)).smulRight
        (T.tau s x)) := by
    ext1 X
    rw [LinearMap.sum_apply]
    simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply, phiS_apply, map_sum,
      map_smul, Representation.asAlgebraHom_of]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [smul_smul]
  have htr := congrArg (LinearMap.trace K (Module.End K (T.W s))) hsum
  rw [hcomp, map_sum] at htr
  simp only [map_smul, LinearMap.trace_smulRight, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.mulLeft_apply, ← map_mul, inv_mul_cancel, map_one, LinearMap.trace_one, LinearMap.trace_id,
    Module.finrank_linearMap, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at htr
  have hd : ((Module.finrank K (T.W s) : ℕ) : K) ≠ 0 := by
    exact_mod_cast (finrank_pos' T s).ne'
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc1 : c = 1 := by
    simp only [cf, Nat.cast_mul] at htr
    field_simp at htr
    exact htr
  rw [hc, hc1, one_smul]

lemma eS_idem (T : GoodSet K G) (s : T.S) : eS T s * eS T s = eS T s := by
  rw [mul_eS, tau_eS, phiS_one]

lemma eS_ne_zero (T : GoodSet K G) (s : T.S) : eS T s ≠ 0 := by
  intro h
  have := tau_eS T s
  rw [h, map_zero] at this
  exact zero_ne_one this

lemma eS_mul_eS_smul (T : GoodSet K G) (s t : T.S) : ∃ c : K, eS T s * eS T t = c • eS T t := by
  obtain ⟨c, hc⟩ := tau_eS_scalar T s t
  exact ⟨c, by rw [mul_eS, hc, map_smul, phiS_one]⟩

lemma eS_mul_eS_of_ne_zero (T : GoodSet K G) (s t : T.S) (h : eS T s * eS T t ≠ 0) :
    eS T s * eS T t = eS T t := by
  obtain ⟨c, hc⟩ := eS_mul_eS_smul T s t
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_smul] at hc; exact h hc
  have h2 : eS T s * (eS T s * eS T t) = eS T s * eS T t := by rw [← mul_assoc, eS_idem]
  rw [hc, mul_smul_comm, hc, smul_smul] at h2
  have h3 : (c * c - c) • eS T t = 0 := by rw [sub_smul, h2, sub_self]
  rcases smul_eq_zero.mp h3 with h4 | h4
  · have : c = 1 := by
      have : c * (c - 1) = 0 := by linear_combination h4
      rcases mul_eq_zero.mp this with h5 | h5
      · exact absurd h5 hc0
      · linear_combination h5
    rw [hc, this, one_smul]
  · exact absurd h4 (eS_ne_zero T t)

lemma eS_apply (T : GoodSet K G) (s : T.S) (x : G) :
    (eS T s).coeff x = cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹) := by
  classical
  rw [eS, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single x]
  · simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, cf]
  · intro y _ hy; simp [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, hy]
  · simp

lemma eS_orth (T : GoodSet K G) (s t : T.S) (hst : s ≠ t) : eS T s * eS T t = 0 := by
  by_contra h
  have h1 := eS_mul_eS_of_ne_zero T s t h
  have h' : eS T t * eS T s ≠ 0 := by rw [← eS_comm]; exact h
  have h2 := eS_mul_eS_of_ne_zero T t s h'
  have heq : eS T s = eS T t := by rw [← h2, ← eS_comm, h1]
  apply hst
  apply T.inj
  have hG : ((Fintype.card G : ℕ) : K) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h1' := congrArg (fun f => MonoidAlgebra.coeff f 1) heq
  simp only [eS_apply, inv_one, map_one, LinearMap.trace_one, cf] at h1'
  have hd : Module.finrank K (T.W s) = Module.finrank K (T.W t) := by
    field_simp at h1'
    have : ((Module.finrank K (T.W s) : ℕ) : K) ^ 2 = ((Module.finrank K (T.W t) : ℕ) : K) ^ 2 := by
      linear_combination h1'
    have h2' : Module.finrank K (T.W s) ^ 2 = Module.finrank K (T.W t) ^ 2 := by exact_mod_cast this
    exact Nat.pow_left_injective (by norm_num) h2'
  change (fun g => LinearMap.trace K (T.W s) (T.tau s g)) = (fun g => LinearMap.trace K (T.W t) (T.tau t g))
  funext g
  have hx := congrArg (fun f => MonoidAlgebra.coeff f g⁻¹) heq
  simp only [eS_apply, inv_inv, cf, hd] at hx
  have hd0 : ((Module.finrank K (T.W t) : ℕ) : K) ≠ 0 := by exact_mod_cast (finrank_pos' T t).ne'
  have hne : ((Module.finrank K (T.W t) : ℕ) : K) / ((Fintype.card G : ℕ) : K) ≠ 0 := div_ne_zero hd0 hG
  exact mul_left_cancel₀ hne hx

lemma eG_idem (T : GoodSet K G) : eG T * eG T = eG T := by
  classical
  rw [eG, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single t]
  · exact eS_idem T t
  · intro s _ hs; exact eS_orth T s t hs
  · simp

lemma eG_comm (T : GoodSet K G) (a : MonoidAlgebra K G) : a * eG T = eG T * a := by
  rw [eG, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => eS_comm T s a

lemma trace_mul_eS (T : GoodSet K G) (s : T.S) {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K G V) :
    ∃ c : K, ∀ a : MonoidAlgebra K G,
      LinearMap.trace K V (ρ.asAlgebraHom (a * eS T s)) = c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a) := by
  set Z : Module.End K (T.W s) := ∑ x : G, (cf T s * LinearMap.trace K V (ρ x)) • T.tau s x⁻¹ with hZ
  have hcomm : ∀ g, Z * T.tau s g = T.tau s g * Z := by
    intro g
    rw [hZ, Finset.sum_mul, Finset.mul_sum]
    simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
    refine (Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ (fun x => ?_)).symm
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
    have h1 : LinearMap.trace K V (ρ (g * x * g⁻¹)) = LinearMap.trace K V (ρ x) := by
      rw [ρ.map_mul, ρ.map_mul, LinearMap.trace_mul_comm, ← mul_assoc, ← ρ.map_mul, inv_mul_cancel,
        ρ.map_one, one_mul]
    have h2 : (g * x * g⁻¹)⁻¹ * g = g * x⁻¹ := by group
    rw [h1, h2]
  obtain ⟨c, hc⟩ := scalar_of_comm T s Z hcomm
  refine ⟨c, fun a => ?_⟩
  rw [mul_eS, phiS_apply, map_sum, map_sum]
  simp only [map_smul, Representation.asAlgebraHom_of, smul_eq_mul]
  have : LinearMap.trace K (T.W s) (Z * (T.tau s).asAlgebraHom a) =
      c * LinearMap.trace K (T.W s) ((T.tau s).asAlgebraHom a) := by
    rw [hc, smul_mul_assoc, one_mul, map_smul, smul_eq_mul]
  rw [← this, hZ, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_mul_assoc, map_smul, smul_eq_mul]
  ring

end PI.Dv.Tr
