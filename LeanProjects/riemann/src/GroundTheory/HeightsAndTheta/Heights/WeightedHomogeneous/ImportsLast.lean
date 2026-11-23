import Mathlib
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.Statements
import GroundTheory.HeightsAndTheta.Heights.WeightedHomogeneous.SectionInjectivityHypothesesProjectiveLine
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close

theorem LatticePacking.intersectionNumber_baseChange : LatticePacking.Statement := by
  intro Λ _ _ _ nrm B hB0 htri hhom hsep
  set R := Module.finrank ℤ Λ
  let b := Module.finBasis ℤ Λ
  set m : ℕ := ⌊2 * Real.exp B⌋₊ + 1 with hm
  have hm0 : m ≠ 0 := Nat.succ_ne_zero _
  have : NeZero m := ⟨hm0⟩
  have hmgt : 2 * Real.exp B < m := by
    rw [hm]; push_cast; exact Nat.lt_floor_add_one _
  have hexp1 : 1 ≤ Real.exp B := Real.one_le_exp hB0
  have hmle : (m : ℝ) ≤ 5 * Real.exp B := by
    rw [hm]; push_cast
    have := Nat.floor_le (show 0 ≤ 2 * Real.exp B by positivity)
    linarith
  have hneg : ∀ y, nrm (-y) = nrm y := fun y ↦ by
    have := hhom (-1) y; simpa using this

  let f : Λ → (Fin R → ZMod m) := fun x i ↦ ((b.repr x i : ℤ) : ZMod m)
  have hinj : Set.InjOn f {x | nrm x ≤ 1} := by
    intro x hx y hy hxy
    by_contra hne
    have hdvd : ∀ i, (m : ℤ) ∣ b.repr (x - y) i := fun i ↦ by
      have h := congrFun hxy i
      simp only [f] at h
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
      rw [map_sub, Finsupp.sub_apply]
      have h' := dvd_neg.mpr h
      rwa [neg_sub] at h'
    let z : Λ := ∑ i, (b.repr (x - y) i / m) • b i
    have hz : (m : ℤ) • z = x - y := by
      conv_rhs => rw [← b.sum_repr (x - y)]
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [smul_smul, Int.mul_ediv_cancel' (hdvd i)]
    have hz0 : z ≠ 0 := by
      rintro h0
      rw [h0, smul_zero] at hz
      exact hne (sub_eq_zero.mp hz.symm)
    have h1 : nrm (x - y) ≤ 2 := by
      have := htri x (-y)
      rw [hneg, ← sub_eq_add_neg] at this
      have hx' : nrm x ≤ 1 := hx
      have hy' : nrm y ≤ 1 := hy
      linarith
    have h2 : nrm (x - y) = m * nrm z := by
      rw [← hz, hhom]; push_cast; rw [abs_of_nonneg (by positivity)]
    have h3 := hsep z hz0
    have h4 : 2 < (m : ℝ) * Real.exp (-B) := by
      rw [Real.exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (Real.exp_pos B)]
      exact hmgt
    have : (m : ℝ) * Real.exp (-B) ≤ m * nrm z :=
      mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg m)
    linarith
  have hfin : {x | nrm x ≤ 1}.Finite :=
    Set.Finite.of_finite_image (Set.toFinite _) hinj
  refine ⟨hfin, ?_⟩
  have hcard : {x | nrm x ≤ 1}.ncard ≤ m ^ R := by
    have := Set.ncard_le_ncard_of_injOn f (t := Set.univ) (fun _ _ ↦ Set.mem_univ _) hinj
      (Set.toFinite _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card,
      Fintype.card_fin] at this
    exact this
  calc (({x | nrm x ≤ 1}.ncard : ℕ) : ℝ) ≤ ((m ^ R : ℕ) : ℝ) := by exact_mod_cast hcard
    _ = (m : ℝ) ^ R := by push_cast; rfl
    _ ≤ (Real.exp B * 5) ^ R := pow_le_pow_left₀ (Nat.cast_nonneg m) (by linarith) R
    _ = Real.exp (R * (B + Real.log 5)) := by
      rw [Real.exp_nat_mul, Real.exp_add, Real.exp_log (by norm_num)]

theorem LatticePacking.equiv :
    GroundTheory.Heights₂.Heights.LatticePacking.Statement ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close.LatticePacking.Statement := by
  refine ⟨fun _ ↦ LatticePacking.intersectionNumber_baseChange, fun hB ↦ ?_⟩
  intro V _ _ L hL B hB0 hsep
  have : Module.Finite ℤ L := Module.Finite.iff_fg.mpr hL
  have : Module.IsTorsionFree ℤ V := Module.IsTorsionFree.trans_faithfulSMul ℤ ℝ V
  have : Module.Free ℤ L := inferInstance
  obtain ⟨hfin, hcard⟩ := hB L (fun x ↦ ‖(x : V)‖) B hB0 (fun x y ↦ norm_add_le _ _)
    (fun k x ↦ by
      change ‖((k • x : L) : V)‖ = _
      rw [Submodule.coe_smul, norm_zsmul ℝ k (x : V), Real.norm_eq_abs])
    (fun x hx ↦ hsep x x.2 fun h ↦ hx (Subtype.ext h))
  have himg : {x : V | x ∈ L ∧ ‖x‖ ≤ 1} = Subtype.val '' {x : L | ‖(x : V)‖ ≤ 1} := by
    ext x
    constructor
    · rintro ⟨hx, hn⟩; exact ⟨⟨x, hx⟩, hn, rfl⟩
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.2, hy⟩
  rw [himg, Set.ncard_image_of_injective _ Subtype.val_injective]
  exact ⟨hfin.image _, hcard⟩

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
