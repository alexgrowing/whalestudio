import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.RK

open MonoidAlgebra

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

lemma mul_eS (T : GoodSet K G) (s : T.S) (z : MonoidAlgebra K G) :
    z * eS T s = ∑ g : G, (((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
      LinearMap.trace K (T.W s) (T.tau s g⁻¹ * (T.tau s).asAlgebraHom z)) •
        MonoidAlgebra.of K G g := by
  induction z using MonoidAlgebra.induction_on with
  | of y =>
    rw [Representation.asAlgebraHom_of, eS, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft y) _ _ fun x => ?_
    rw [mul_smul_comm, ← map_mul (MonoidAlgebra.of K G), ← map_mul (T.tau s)]
    simp only [Equiv.coe_mulLeft, mul_inv_rev, inv_mul_cancel_right]
  | add x y hx hy =>
    rw [add_mul, hx, hy, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_add, mul_add, map_add, mul_add, add_smul]
  | smul r x hx =>
    rw [smul_mul_assoc, hx, Finset.smul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, mul_smul_comm, map_smul, smul_smul, smul_eq_mul]
    congr 1
    ring

lemma end_simple {W : Type} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (E : Module.End K W) (hE : E ≠ 0) :
    ∃ (n : ℕ) (A B : Fin n → Module.End K W), ∑ i, A i * E * B i = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, E v ≠ 0 := by
    by_contra h
    push Not at h
    exact hE (LinearMap.ext h)
  have hex : ¬ ∀ φ : Module.Dual K W, φ (E v) = 0 := fun h =>
    hv ((Module.forall_dual_apply_eq_zero_iff K _).mp h)
  push Not at hex
  obtain ⟨f0, hf0⟩ := hex
  let f : Module.Dual K W := (f0 (E v))⁻¹ • f0
  have hf : f (E v) = 1 := by simp [f, hf0]
  let b := Module.finBasis K W
  refine ⟨Module.finrank K W, fun i => f.smulRight (b i), fun i => (b.coord i).smulRight v, ?_⟩
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.sum_apply, Module.End.one_apply]
  conv_rhs => rw [← b.sum_repr x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.smulRight_apply,
    LinearMap.smulRight_apply, map_smul, map_smul, hf, smul_eq_mul, mul_one, Module.Basis.coord_apply]

theorem eG_mem (T : GoodSet K G) (P : Pair K G) (h : ∀ s, (T.tau s).asAlgebraHom (eps P) ≠ 0) :
    eG T ∈ AddSubgroup.closure {w | ∃ a b : MonoidAlgebra K G, w = a * eps P * b} := by
  refine AddSubgroup.sum_mem _ fun s _ => ?_
  obtain ⟨n, A, B, hAB⟩ := end_simple _ (h s)
  choose a ha using fun i => T.irr s (A i)
  choose b hb using fun i => T.irr s (B i)
  have hτ : (T.tau s).asAlgebraHom (∑ i, a i * eps P * b i) = (T.tau s).asAlgebraHom 1 := by
    rw [map_one, map_sum]
    simp only [map_mul, ha, hb]
    exact hAB
  have e1 := mul_eS T s (∑ i, a i * eps P * b i)
  have e2 := mul_eS T s 1
  rw [one_mul] at e2
  have key : (∑ i, a i * eps P * b i) * eS T s = eS T s := by
    rw [e1, e2, hτ]
  rw [← key, Finset.sum_mul]
  refine AddSubgroup.sum_mem _ fun i _ => AddSubgroup.subset_closure ?_
  exact ⟨a i, b i * eS T s, mul_assoc _ _ _⟩

lemma tau_eps_ne (T : GoodSet K G) (P : Pair K G) (h : M1 T P) (s : T.S) :
    (T.tau s).asAlgebraHom (eps P) ≠ 0 := by
  intro h0
  have h1 : nS T P s = 1 := h s
  unfold nS at h1
  rw [Submodule.finrank_eq_zero.mpr (by rw [h0]; exact LinearMap.range_zero)] at h1
  exact zero_ne_one h1

end PI.Dv.RK
