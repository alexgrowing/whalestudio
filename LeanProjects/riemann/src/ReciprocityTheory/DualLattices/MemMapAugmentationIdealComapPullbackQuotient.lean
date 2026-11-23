import ReciprocityTheory.DualLattices.ExistsFamilyValuationDetEqOne

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {N : Type} [AddCommGroup N] [Fintype N] [DecidableEq N]

theorem apply_add_of_mem_map_pullbackQuotient (K : AddSubgroup N) (M : Submodule R (N ⧸ K → C)) {h : N → C}
    (hh : h ∈ M.map (pullQ (R := R) K)) (x : N) (k : K) : h (x + k) = h x := by
  obtain ⟨u, -, rfl⟩ := hh
  simp only [pullQ, LinearMap.funLeft_apply]
  rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff _).mpr k.2, add_zero]

theorem pullbackQuotient_apply_out (K : AddSubgroup N) {h : N → C} (hinv : ∀ x (k : K), h (x + k) = h x) :
    pullQ (R := R) K (fun q => h q.out) = h := by
  funext x
  simp only [pullQ, LinearMap.funLeft_apply]
  have e : (((QuotientAddGroup.mk x : N ⧸ K).out : N) : N ⧸ K) = (x : N ⧸ K) := by
    exact Quotient.out_eq _
  have hk := QuotientAddGroup.eq.mp e
  calc h (QuotientAddGroup.mk x : N ⧸ K).out
      = h ((QuotientAddGroup.mk x : N ⧸ K).out + ((⟨_, hk⟩ : K) : N)) := (hinv _ _).symm
    _ = h x := by congr 1; simp

theorem mem_map_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) :
    h ∈ (AA.carrier.comap (pullQ (R := R) K)).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
  exact hh

theorem mem_map_augmentationIdeal_comap_pullbackQuotient (AA : HopfOrder (C := C) R N) (K : AddSubgroup N) {h : N → C}
    (hh : h ∈ AA.carrier) (hinv : ∀ x (k : K), h (x + k) = h x) (h0 : h 0 = 0) :
    h ∈ (augIdeal (AA.carrier.comap (pullQ (R := R) K))).map (pullQ (R := R) K) := by
  refine Submodule.mem_map.mpr ⟨fun q => h q.out, ?_, pullbackQuotient_apply_out (R := R) K hinv⟩
  simp only [augIdeal, Submodule.mem_inf]
  refine ⟨?_, ?_⟩
  · rw [Submodule.mem_comap, pullbackQuotient_apply_out (R := R) K hinv]
    exact hh
  · have h1 := congrFun (pullbackQuotient_apply_out (R := R) K hinv) 0
    simp only [pullQ, LinearMap.funLeft_apply, QuotientAddGroup.mk_zero] at h1
    simp only [LinearMap.mem_ker, LinearMap.proj_apply]
    rw [h1, h0]

section family

variable (hv : v.Integers R) (AA : HopfOrder (C := C) R N) (K : AddSubgroup N)
  [DecidablePred (· ∈ K)] (β : Matrix K K C) (hβ : IsUnit β.det)
  (hAK : AA.carrier.map (resK (R := R) K) = Submodule.span R (Set.range fun j k => β k j))
  (f : K → N → C) (hf : ∀ j, f j ∈ AA.carrier) (hdet : ∀ x, v (h3mm K β f x).det = 1)

include hβ hdet in
theorem eq_zero_of_sum_mul_coset_eq_zero (x : N) (c : K → C) (h : ∀ k : K, ∑ j, c j * f j (x + k) = 0) : c = 0 := by
  have hM : (h3mm K β f x).det ≠ 0 := by
    intro h0
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hw : β *ᵥ (c ᵥ* h3mm K β f x) = 0 := by
    funext k
    rw [Pi.zero_apply, ← h k]
    have e : ∀ j, f j (x + k) = ∑ l, β k l * h3mm K β f x j l := fun j => by
      rw [cosetCoordinates_expand K β hβ (f j) x k]
      rfl
    simp only [e]
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hw0 : c ᵥ* h3mm K β f x = 0 := by
    have := congrArg (β⁻¹ *ᵥ ·) hw
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul β hβ] using this
  by_contra hc
  exact hM (Matrix.exists_vecMul_eq_zero_iff.mp ⟨c, hc, hw0⟩)

include hv hβ hAK hf hdet in
theorem exists_coset_invariant_coefficients {g : N → C} (hg : g ∈ AA.carrier) :
    ∃ b : K → N → C, (∀ j, b j ∈ AA.carrier) ∧ (∀ j x (k : K), b j (x + k) = b j x) ∧
      g = ∑ j, b j * f j := by
  have hDne : ∀ x, (h3mm K β f x).det ≠ 0 := fun x h0 => by
    have := hdet x
    rw [h0, map_zero] at this
    exact zero_ne_one this
  have hFu : ∀ x, IsUnit (h3mm K β f x).det := fun x =>
    isUnit_iff_ne_zero.mpr (hDne x)
  obtain ⟨b, hb⟩ : ∃ b : K → N → C, b = fun j x =>
      (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j := ⟨_, rfl⟩
  have hbx : ∀ j x, b j x = (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j :=
    fun j x => by rw [hb]
  let Fm : Matrix K K (N → C) := Matrix.of fun i j => fun x => h3co K β (f i) x j
  have hFm : ∀ i j, Fm i j ∈ AA.carrier := fun i j =>
    cosetCoordinates_mem AA K β hβ hAK (hf i) j
  have hDA := det_mem_and_adjugate_mem AA Fm hFm
  have hD : (fun x => (h3mm K β f x).det) ∈ AA.carrier := hDA.1
  have hAdj : ∀ l j, (fun x => (h3mm K β f x).adjugate l j) ∈ AA.carrier :=
    hDA.2
  obtain ⟨P, hP, hA⟩ := AA.lat
  have hDinv : (fun x => (h3mm K β f x).det)⁻¹ ∈ AA.carrier :=
    inv_mem_of_valuation_eq_one hv AA.carrier P hP hA AA.one_mem AA.mul_mem _ hD hdet
  have hG : ∀ l, (fun x => h3co K β g x l) ∈ AA.carrier := fun l =>
    cosetCoordinates_mem AA K β hβ hAK hg l
  refine ⟨b, ?_, ?_, ?_⟩
  · intro j
    have key : b j = (∑ l, (fun x => h3co K β g x l) *
        (fun x => (h3mm K β f x).adjugate l j)) *
        (fun x => (h3mm K β f x).det)⁻¹ := by
      funext x
      rw [hbx, Matrix.inv_def]
      simp only [Pi.mul_apply, Finset.sum_apply, Pi.inv_apply, Matrix.vecMul, dotProduct,
        Matrix.smul_apply, smul_eq_mul, Finset.sum_mul, Ring.inverse_eq_inv]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [key]
    exact AA.mul_mem _ _ (Submodule.sum_mem _ fun l _ => AA.mul_mem _ _ (hG l) (hAdj l j)) hDinv
  · intro j x k
    have hT : IsUnit (h3T K β k).det := by
      refine isUnit_iff_ne_zero.mpr fun h0 => hDne (x + k) ?_
      rw [cosetCoordinateMatrix_add K β hβ f x k, Matrix.det_mul, h0, mul_zero]
    rw [hbx, hbx, cosetCoordinates_add K β hβ g x k, cosetCoordinateMatrix_add K β hβ f x k,
      Matrix.mul_inv_rev, Matrix.vecMul_vecMul, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hT, Matrix.one_mul]
  · funext x
    have e1 := cosetCoordinates_expand K β hβ g x 0
    have e2 := fun j => cosetCoordinates_expand K β hβ (f j) x 0
    rw [show ((0 : K) : N) = 0 from rfl, add_zero] at e1
    simp only [show ((0 : K) : N) = 0 from rfl, add_zero] at e2
    have hv' : (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) ᵥ*
        h3mm K β f x = h3co K β g x := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (hFu x), Matrix.vecMul_one]
    have hw : ∀ l, ∑ j, (h3co K β g x ᵥ* (h3mm K β f x)⁻¹) j *
        h3co K β (f j) x l = h3co K β g x l := fun l => by
      have := congrFun hv' l
      exact this
    rw [Finset.sum_apply]
    simp only [Pi.mul_apply, hbx, e2]
    rw [e1]
    generalize h3co K β g x ᵥ* (h3mm K β f x)⁻¹ = w at hw ⊢
    simp only [← hw]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

end family

end ReciprocityTheory.PGsh.L2
