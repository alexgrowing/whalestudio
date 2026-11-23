import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermHyperbolic
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsotropicBasisNonorthogonalTwoVectorsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryTransvectionSubmonoidNormalDetOneStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.QuasiReflectionEqMulTransvectionsOfHyperbolicPlaStatement

open NumberField IsDedekindDomain Matrix GlobalTheory.UTrans GlobalTheory.AdLat
open scoped TensorProduct

namespace GlobalTheory.UTrans.Chain

theorem eventually_quad_ne {E : Type} [Field E] [CharZero E] (a b c : E) (ha : a ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, a + (t : E) * b + (t : E) ^ 2 * c ≠ 0 := by
  classical
  set p : Polynomial E := Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 with hp
  have hp0 : p ≠ 0 := by
    intro h
    have h0 := congrArg (fun q : Polynomial E => q.coeff 0) h
    simp [p] at h0
    exact ha h0
  rw [Filter.eventually_cofinite]
  refine (Set.Finite.preimage (fun _ _ _ _ h => Rat.cast_injective h)
    (Finset.finite_toSet p.roots.toFinset)).subset ?_
  intro t ht
  simp only [Set.mem_setOf_eq, not_not] at ht
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  rw [Polynomial.mem_roots hp0]
  show Polynomial.eval (t : E) p = 0
  simp only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  linear_combination ht

variable {E : Type} [Field E] [CharZero E] {n : ℕ}

theorem hf_line_left (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G (x + t • w) z = hf σ G x z + t * hf σ G w z := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem hf_line_right (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E) (t : E) :
    hf σ G z (x + t • w) = hf σ G z x + σ t * hf σ G z w := by
  simp only [hf, Finset.mul_sum, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem eventually_aniso (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w : Fin n → E)
    (hx : hf σ G x x ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) (x + (t : E) • w) ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x x) (hf σ G w x + hf σ G x w) (hf σ G w w) hx]
    with t ht
  have hσ : σ (t : E) = t := map_ratCast σ t
  rw [hf_line_left, hf_line_right, hf_line_right, hσ]
  intro h
  apply ht
  linear_combination h

theorem eventually_pair (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (x w z : Fin n → E)
    (hx : hf σ G x z ≠ 0) :
    ∀ᶠ t : ℚ in Filter.cofinite, hf σ G (x + (t : E) • w) z ≠ 0 := by
  filter_upwards [eventually_quad_ne (hf σ G x z) (hf σ G w z) 0 hx] with t ht
  rw [hf_line_left]
  intro h
  apply ht
  linear_combination h

theorem eventually_chain (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHerm σ G)
    {ι : Type} (z : ι → Fin n → E) (l : ι → E) (x : Fin n → E) (u : E) (hx : hf σ G x x ≠ 0)
    (hu : u * σ u = 1) (hz : ∀ i, hf σ G (z i) (z i) = 0) (hxz : ∀ i, hf σ G x (z i) ≠ 0)
    (S : Finset ι) :
    ∀ᶠ t : ℚ in Filter.cofinite, ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) =
      m * tv σ G (x + (t : E) • ∑ i ∈ S, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ S, l i • z i) (x + (t : E) • ∑ i ∈ S, l i • z i)) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine Filter.Eventually.of_forall fun t => ⟨1, (TvGen σ G).one_mem, ?_⟩
    simp
  | @insert j S hj ih =>
    have hpair := eventually_pair σ G x (∑ i ∈ S, l i • z i) (z j) (hxz j)
    have ha1 := eventually_aniso σ G x (∑ i ∈ S, l i • z i) hx
    have ha2 := eventually_aniso σ G x (∑ i ∈ insert j S, l i • z i) hx
    filter_upwards [ih, hpair, ha1, ha2] with t hih h1 h2 h3
    obtain ⟨m, hm, hmeq⟩ := hih
    have hsplit : x + (t : E) • ∑ i ∈ insert j S, l i • z i =
        (x + (t : E) • ∑ i ∈ S, l i • z i) + ((t : E) * l j) • z j := by
      rw [Finset.sum_insert hj, smul_add, mul_smul]
      abel
    rw [hsplit] at h3 ⊢
    obtain ⟨m', hm', hm'eq⟩ :=
      GlobalTheory.T.quasiReflection_eq_mul_transvections_of_hyperbolicPlane E n σ G hG _ (z j) ((t : E) * l j) u (hz j) h1 h2 h3 hu
    exact ⟨m * m', (TvGen σ G).mul_mem hm hm', by rw [hmeq, hm'eq, mul_assoc]⟩

end GlobalTheory.UTrans.Chain

theorem GlobalTheory.UTrans.quasiReflection_eq_tvGen_mul : ∀ (E : Type) [Field E] [CharZero E] (n : ℕ) (σ : E →+* E) (G : Matrix (Fin n) (Fin n) E), IsHerm σ G → (∃ z : Fin n → E, z ≠ 0 ∧ hf σ G z z = 0) → ∀ (x y : Fin n → E) (u : E), hf σ G x x ≠ 0 → hf σ G y y ≠ 0 → u * σ u = 1 → ∃ m ∈ TvGen σ G, tv σ G x ((u - 1) / hf σ G x x) = m * tv σ G y ((u - 1) / hf σ G y y) := by
  intro E _ _ n σ G hG hiso x y u hx hy hu
  classical
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (by simp [hf])
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (by simp [hf])
  obtain ⟨z, hli, hzp⟩ := GlobalTheory.T.exists_isotropic_basis_nonorthogonal_two_vectors E n σ G hG hiso x y hx0 hy0
  have : Nonempty (Fin n) := by
    by_contra hne
    exact hx0 (funext fun i => (hne ⟨i⟩).elim)
  have hspan : Submodule.span E (Set.range z) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank (by simp)
  have hmem : y - x ∈ Submodule.span E (Set.range z) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨l, hl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hmem
  have hz : ∀ i, hf σ G (z i) (z i) = 0 := fun i => (hzp i).1
  have hxz : ∀ i, hf σ G x (z i) ≠ 0 := fun i => (hzp i).2.1
  have hyz : ∀ i, hf σ G y (z i) ≠ 0 := fun i => (hzp i).2.2
  have h1 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z l x u hx hu hz hxz Finset.univ
  have h2 := GlobalTheory.UTrans.Chain.eventually_chain σ G hG z (fun i => -l i) y u hy hu hz hyz
    Finset.univ
  have hT : Filter.Tendsto (fun t : ℚ => 1 - t) Filter.cofinite Filter.cofinite :=
    (sub_right_injective : Function.Injective fun t : ℚ => 1 - t).tendsto_cofinite
  obtain ⟨t, ⟨m1, hm1, e1⟩, ⟨m2, hm2, e2⟩⟩ := (h1.and (hT.eventually h2)).exists
  have hv : y + (((1 - t : ℚ)) : E) • ∑ i ∈ Finset.univ, (-l i) • z i =
      x + (t : E) • ∑ i ∈ Finset.univ, l i • z i := by
    simp only [neg_smul, Finset.sum_neg_distrib, hl]
    push_cast
    module
  have e2' : tv σ G y ((u - 1) / hf σ G y y) =
      m2 * tv σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
        ((u - 1) / hf σ G (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)
          (x + (t : E) • ∑ i ∈ Finset.univ, l i • z i)) := by
    rw [← hv]
    exact e2
  obtain ⟨-, hdet, hinv, -⟩ := (GlobalTheory.T.unitaryTransvectionSubmonoid_normal_det_one E n σ G hG).2 m2 hm2
  have hunit : IsUnit m2.det := by
    rw [hdet]
    exact isUnit_one
  refine ⟨m1 * m2⁻¹, (TvGen σ G).mul_mem hm1 hinv, ?_⟩
  rw [e1, e2', mul_assoc m1, ← mul_assoc m2⁻¹, Matrix.nonsing_inv_mul _ hunit, one_mul]
