import Mathlib.RingTheory.PowerSeries.WeierstrassPreparation
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.EqZeroOfForallMemCoeffFiltration

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.WeierD

open PowerSeries Formalism.MainNotions.N.FrobeniusPowerSeries.WeierS

variable {O : Type*} [CommRing O] [IsLocalRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O]

noncomputable def wd (g : O⟦X⟧) : ℕ := (g.map (IsLocalRing.residue O)).order.toNat

theorem constantCoeff_mem {g : O⟦X⟧} (hD : 1 ≤ wd g) :
    constantCoeff g ∈ IsLocalRing.maximalIdeal O := by
  have h0 : coeff 0 (g.map (IsLocalRing.residue O)) = 0 :=
    coeff_of_lt_order_toNat 0 (by unfold wd at hD; omega)
  rwa [coeff_map, coeff_zero_eq_constantCoeff_apply, IsLocalRing.residue_eq_zero_iff] at h0

noncomputable def poly {D : ℕ} (a : Fin D → O) : Polynomial O :=
  ∑ i : Fin D, Polynomial.C (a i) * Polynomial.X ^ (i : ℕ)

theorem coeff_poly {D : ℕ} (a : Fin D → O) (n : ℕ) :
    (poly a).coeff n = if h : n < D then a ⟨n, h⟩ else 0 := by
  simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨n, h⟩ (fun j _ hj => if_neg (fun e => hj (Fin.ext e.symm)))
      (by simp)]
    simp
  · exact Finset.sum_eq_zero fun j _ => if_neg (by have := j.2; omega)

theorem coe_poly {D : ℕ} (a : Fin D → O) :
    ((poly a : Polynomial O) : O⟦X⟧) = ∑ i : Fin D, C (a i) * X ^ (i : ℕ) := by
  ext n
  simp only [Polynomial.coeff_coe, poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow,
    map_sum, PowerSeries.coeff_C_mul_X_pow]

theorem degree_poly_lt {D : ℕ} (a : Fin D → O) : (poly a).degree < D :=
  Polynomial.degree_sum_fin_lt a

theorem poly_of_degree {D : ℕ} {p : Polynomial O} (hp : p.degree < D) :
    poly (fun i : Fin D => p.coeff i) = p := by
  ext n
  rw [coeff_poly]
  split_ifs with h
  · rfl
  · exact (Polynomial.coeff_eq_zero_of_degree_lt
      (lt_of_lt_of_le hp (by exact_mod_cast (not_lt.mp h)))).symm

theorem h_C (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (a : O) : h (C a) = C a := by
  simpa [PowerSeries.algebraMap_apply] using h.commutes a

theorem sum_split {D : ℕ} (h : O⟦X⟧ →ₐ[O] O⟦X⟧) {g : O⟦X⟧} (hX : h X = g)
    (c : Fin D → O⟦X⟧) :
    ∑ i : Fin D, X ^ (i : ℕ) * h (c i) =
      ((poly fun i => constantCoeff (c i) : Polynomial O) : O⟦X⟧) +
        g * ∑ i : Fin D, X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i)) := by
  rw [coe_poly, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_lhs => rw [eq_X_mul_shift_add_const (c i)]
  rw [map_add, map_mul, hX, h_C]
  ring

variable {g : O⟦X⟧} (hg : g.map (IsLocalRing.residue O) ≠ 0)
include hg

theorem coeff_eq_zero_of_sum_eq_zero (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) :
    ∀ n, ∀ c : Fin (wd g) → O⟦X⟧, ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0 → ∀ i, coeff n (c i) = 0 := by
  have HW := IsWeierstrassDivisor.of_map_ne_zero hg
  have step : ∀ c : Fin (wd g) → O⟦X⟧, ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0 →
      (∀ i, constantCoeff (c i) = 0) ∧
        ∑ i : Fin (wd g), X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i)) = 0 := by
    intro c hc
    rw [sum_split h hX] at hc
    have h2 : g * (∑ i : Fin (wd g), X ^ (i : ℕ) * h (mk fun p => coeff (p + 1) (c i))) =
        ((-poly fun i => constantCoeff (c i) : Polynomial O) : O⟦X⟧) := by
      rw [Polynomial.coe_neg]
      exact eq_neg_of_add_eq_zero_right hc
    obtain ⟨hq, hr⟩ := HW.eq_zero_of_mul_eq
      (by rw [Polynomial.degree_neg]; exact degree_poly_lt (D := wd g) _) h2
    refine ⟨fun i => ?_, hq⟩
    have := congrArg (fun p => Polynomial.coeff p i) (neg_eq_zero.mp hr)
    simpa [coeff_poly] using this
  intro n
  induction n with
  | zero =>
    intro c hc i
    rw [coeff_zero_eq_constantCoeff_apply]
    exact (step c hc).1 i
  | succ n ih =>
    intro c hc i
    have := ih _ (step c hc).2 i
    rwa [coeff_mk] at this

theorem eq_zero_of_sum_eq_zero (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (c : Fin (wd g) → O⟦X⟧)
    (hc : ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = 0) : c = 0 :=
  funext fun i => PowerSeries.ext fun n => by
    simpa using coeff_eq_zero_of_sum_eq_zero hg h hX n c hc i

theorem decomp_unique (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (c c' : Fin (wd g) → O⟦X⟧)
    (hc : ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) = ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c' i)) : c = c' := by
  have := eq_zero_of_sum_eq_zero hg h hX (c - c') (by
    simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib, hc, sub_self])
  exact sub_eq_zero.mp this

theorem injective (hD : 1 ≤ wd g) (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) :
    Function.Injective h := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have := eq_zero_of_sum_eq_zero hg h hX (fun i => if (i : ℕ) = 0 then a else 0) (by
    rw [Finset.sum_eq_single ⟨0, hD⟩ (fun j _ hj => by
      rw [if_neg (fun e => hj (Fin.ext e)), map_zero, mul_zero]) (by simp)]
    simp [ha])
  simpa using congrFun this ⟨0, hD⟩

omit hg in

noncomputable def cf (g : O⟦X⟧) (f : O⟦X⟧) (i : ℕ) : O⟦X⟧ :=
  mk fun n => ((fun q => q /ʷ g)^[n] f %ʷ g).coeff i

omit hg in
theorem constantCoeff_cf (f : O⟦X⟧) (i : ℕ) : constantCoeff (cf g f i) = (f %ʷ g).coeff i := by
  rw [← coeff_zero_eq_constantCoeff_apply, cf, coeff_mk, Function.iterate_zero_apply]

omit hg in
theorem shift_cf (f : O⟦X⟧) (i : ℕ) :
    (mk fun p => coeff (p + 1) (cf g f i)) = cf g (f /ʷ g) i := by
  ext n
  simp only [cf, coeff_mk, Function.iterate_succ_apply]

theorem exists_decomp (hD : 1 ≤ wd g) (h : O⟦X⟧ →ₐ[O] O⟦X⟧) (hX : h X = g) (f : O⟦X⟧) :
    ∃ c : Fin (wd g) → O⟦X⟧, f = ∑ i : Fin (wd g), X ^ (i : ℕ) * h (c i) := by
  have hg0 := constantCoeff_mem hD
  let E : O⟦X⟧ → O⟦X⟧ := fun f => f - ∑ i : Fin (wd g), X ^ (i : ℕ) * h (cf g f i)
  have hE : ∀ f, E f = g * E (f /ʷ g) := by
    intro f
    have hs := sum_split h hX (fun i : Fin (wd g) => cf g f i)
    simp only [constantCoeff_cf, shift_cf] at hs
    rw [poly_of_degree (D := wd g) (degree_weierstrassMod_lt f g)] at hs
    have hf := eq_mul_weierstrassDiv_add_weierstrassMod f hg
    simp only [E]
    rw [hs]
    linear_combination hf
  have hmem : ∀ N f, E f ∈ Ideal.span {g ^ N} := by
    intro N
    induction N with
    | zero => intro f; simp
    | succ N ih =>
      intro f
      rw [hE, Ideal.mem_span_singleton, pow_succ']
      exact mul_dvd_mul_left g (Ideal.mem_span_singleton.mp (ih _))
  have h0 : E f = 0 := eq_zero_of_forall_mem_coeffFiltration fun N =>
    (Ideal.span_singleton_le_iff_mem _).mpr (pow_mem_coeffFiltration hg0 N) (hmem N f)
  exact ⟨fun i => cf g f i, sub_eq_zero.mp h0⟩

end Formalism.MainNotions.N.FrobeniusPowerSeries.WeierD
