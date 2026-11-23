import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift

set_option autoImplicit false

namespace GlobalTheory.DI

variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem delta_add (c c' : Finset ι → E) : delta (c + c') = delta c + delta c' := by
  funext t
  simp only [delta, Pi.add_apply, smul_add, Finset.sum_add_distrib]

theorem delta_sub (c c' : Finset ι → E) : delta (c - c') = delta c - delta c' := by
  funext t
  simp only [delta, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib]

theorem delta_delta (c : Finset ι → E) : delta (delta c) = 0 := by
  funext t
  let f : ι × ι → E := fun q =>
    (cubeSign t q.1 * cubeSign (t.erase q.1) q.2) • c ((t.erase q.1).erase q.2)
  have h1 : delta (delta c) t = ∑ q ∈ t.offDiag, f q := by
    show ∑ i ∈ t, cubeSign t i • delta c (t.erase i) = _
    rw [Finset.sum_finset_product t.offDiag t (fun i => t.erase i)
      (fun q => by simp only [Finset.mem_offDiag, Finset.mem_erase]; tauto)]
    refine Finset.sum_congr rfl fun i _ => ?_
    show cubeSign t i • ∑ j ∈ t.erase i, cubeSign (t.erase i) j • c ((t.erase i).erase j) = _
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [f, smul_smul]
  rw [h1, Pi.zero_apply]
  refine Finset.sum_involution (fun q _ => q.swap) (fun q hq => ?_) (fun q hq _ h => ?_)
    (fun q hq => ?_) (fun q _ => rfl)
  · rw [Finset.mem_offDiag] at hq
    simp only [f, Prod.fst_swap, Prod.snd_swap]
    rw [cubeSign_mul_erase hq.1 hq.2.1 hq.2.2, Finset.erase_right_comm (a := q.1) (b := q.2),
      neg_smul, neg_add_cancel]
  · rw [Finset.mem_offDiag] at hq
    exact hq.2.2 (congrArg Prod.snd h)
  · rw [Finset.mem_offDiag] at hq ⊢
    exact ⟨hq.2.1, hq.1, hq.2.2.symm⟩

theorem Dtot_add (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c + c') = Dtot d c + Dtot d c' := by
  funext t
  simp only [Dtot, delta_add, Pi.add_apply, map_add, smul_add]
  abel

theorem Dtot_sub (d : E →+ E) (c c' : Finset ι → E) : Dtot d (c - c') = Dtot d c - Dtot d c' := by
  funext t
  simp only [Dtot, delta_sub, Pi.sub_apply, map_sub, smul_sub]
  abel

theorem Dtot_Dtot (d : E →+ E) (hd : ∀ x, d (d x) = 0) (c : Finset ι → E) :
    Dtot d (Dtot d c) = 0 := by
  funext t
  have hDt : ∀ s, Dtot d c s = delta c s + (-1 : ℤ) ^ s.card • d (c s) := fun s => rfl
  have e1 : delta (Dtot d c) t = delta (delta c) t +
      ∑ i ∈ t, cubeSign t i • ((-1 : ℤ) ^ (t.erase i).card • d (c (t.erase i))) := by
    show ∑ i ∈ t, cubeSign t i • Dtot d c (t.erase i) = delta (delta c) t + _
    simp only [hDt, smul_add, Finset.sum_add_distrib]
    rfl
  have e2 : d (delta c t) = ∑ i ∈ t, cubeSign t i • d (c (t.erase i)) := by
    show d (∑ i ∈ t, cubeSign t i • c (t.erase i)) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul d _ _
  show delta (Dtot d c) t + (-1 : ℤ) ^ t.card • d (Dtot d c t) = 0
  rw [e1, delta_delta, hDt, map_add, map_zsmul, hd, smul_zero, add_zero, e2, Finset.smul_sum,
    Pi.zero_apply, zero_add, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hc : (-1 : ℤ) ^ (t.erase i).card = -(-1 : ℤ) ^ t.card := by
    rw [← Finset.card_erase_add_one hi, pow_succ]; ring
  rw [hc, neg_smul, smul_neg, smul_comm, neg_add_cancel]

theorem delta_Dtot_props : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E),
    (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧
    (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧
    (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧
    (∀ c : Finset ι → E, delta (delta c) = 0) ∧
    ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) :=
  fun d => ⟨delta_add, delta_sub, Dtot_add d, Dtot_sub d, delta_delta, fun hd => Dtot_Dtot d hd⟩

end GlobalTheory.DI
