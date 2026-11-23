import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound

noncomputable section

namespace GlobalTheory.DatumEigen

variable {k : Type} [Field k] [ValuativeRel k]

theorem val_det_sub_lt {m : Type} [Fintype m] [DecidableEq m] {M N : Matrix m m k}
    (hM : ∀ i j, M i j ∈ 𝒪[k]) (hN : ∀ i j, N i j ∈ 𝒪[k]) (h : ∀ i j, valuation k (M i j - N i j) < 1) :
    valuation k (M.det - N.det) < 1 := by
  have key : ∀ x : 𝒪[k], IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
    intro x
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
    exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix m m 𝒪[k] := fun i j => ⟨N i j, hN i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  have eN : N = (algebraMap 𝒪[k] k).mapMatrix N' := rfl
  have hres : (IsLocalRing.residue 𝒪[k]).mapMatrix M' = (IsLocalRing.residue 𝒪[k]).mapMatrix N' := by
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, key]
    exact h i j
  rw [eM, eN, ← RingHom.map_det, ← RingHom.map_det, ← map_sub, ← key, map_sub, RingHom.map_det,
    RingHom.map_det, hres, sub_self]

theorem val_mul_lt {a b : k} (ha : valuation k a ≤ 1) (hb : valuation k b < 1) : valuation k (a * b) < 1 := by
  rw [map_mul]
  exact (mul_le_of_le_one_left' ha).trans_lt hb

theorem det_int {m : Type} [Fintype m] [DecidableEq m] {M : Matrix m m k} (hM : ∀ i j, M i j ∈ 𝒪[k]) :
    M.det ∈ 𝒪[k] := by
  let M' : Matrix m m 𝒪[k] := fun i j => ⟨M i j, hM i j⟩
  have eM : M = (algebraMap 𝒪[k] k).mapMatrix M' := rfl
  rw [eM, ← RingHom.map_det]
  exact (M'.det).2

theorem eq_one_of_mul {a b : ValueGroupWithZero k} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  by_contra hlt
  replace hlt := not_le.1 hlt
  have : a * b < 1 := (mul_le_of_le_one_right' hb).trans_lt hlt
  exact this.ne h

theorem tame_eq {ξ : kˣ →* ℂˣ} (hξ : IsTame ξ) {a b : kˣ} (hb : valuation k (b : k) = 1)
    (h : valuation k ((a : k) - b) < 1) : ξ a = ξ b := by
  have hb0 : (b : k) ≠ 0 := b.ne_zero
  have h1 : ξ (a * b⁻¹) = 1 := by
    apply hξ
    have e : ((a * b⁻¹ : kˣ) : k) - 1 = ((a : k) - b) * (b : k)⁻¹ := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [e, map_mul, map_inv₀, hb, inv_one, mul_one]
    exact h
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1

variable [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Blocks

variable {A D E : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

theorem int_of_mem {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) (i l : A ⊕ D) : j.val i l ∈ 𝒪[k] :=
  ((GlobalTheory.SplitFlip.mem_KO_iff j).1 (mem_parahoric.1 hj).1).1 i l

theorem det_cong {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k (j.val.det - j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  rw [← det_fromBlocks_zero₂₁ j.val.toBlocks₁₁ j.val.toBlocks₁₂ j.val.toBlocks₂₂]
  refine val_det_sub_lt hJ ?_ ?_
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hJ]
  · rintro (i | i) (l | l) <;> simp [toBlocks₁₁, toBlocks₁₂, toBlocks₂₂, hl]

theorem val_det_blocks {j : GL (A ⊕ D) k} (hj : j ∈ parahoric k A D) :
    valuation k j.val.toBlocks₁₁.det = 1 ∧ valuation k j.val.toBlocks₂₂.det = 1 := by
  have hJ := int_of_mem hj
  have h1 : valuation k j.val.det = 1 := by
    have := nabs_det_of_mem_KO (mem_parahoric.1 hj).1
    rwa [nabs_eq_one_iff] at this
  have h2 := Valuation.map_eq_of_sub_lt _ (show valuation k (j.val.toBlocks₁₁.det * j.val.toBlocks₂₂.det
      - j.val.det) < valuation k j.val.det by
    rw [h1, ← Valuation.map_neg, neg_sub]; exact det_cong hj)
  rw [h1, map_mul] at h2
  have i11 : valuation k j.val.toBlocks₁₁.det ≤ 1 := det_int fun i l => hJ _ _
  have i22 : valuation k j.val.toBlocks₂₂.det ≤ 1 := det_int fun i l => hJ _ _
  exact ⟨eq_one_of_mul i11 i22 h2, eq_one_of_mul i22 i11 (by rw [mul_comm]; exact h2)⟩

omit [Fintype E] [DecidableEq E] in

theorem inSupp_mul {x : Matrix (A ⊕ E) (A ⊕ D) k} (hx : InSupp x) {j : GL (A ⊕ D) k}
    (hj : j ∈ parahoric k A D) : InSupp (x * j.val) ∧
      valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
  have hJ := int_of_mem hj
  have hl := (mem_parahoric.1 hj).2
  obtain ⟨hxi, hxd, hxl⟩ := hx
  have hprod : ∀ i l, (x * j.val) i l ∈ 𝒪[k] := fun i l => by
    rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hxi i m) (hJ m l)
  have hcong : valuation k ((x * j.val).toBlocks₁₁.det - x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) < 1 := by
    rw [← det_mul]
    refine val_det_sub_lt (fun i l => hprod _ _) (fun i l => ?_) (fun i l => ?_)
    · rw [mul_apply]; exact sum_mem fun m _ => mul_mem (hxi _ _) (hJ _ _)
    · simp only [toBlocks₁₁, of_apply, mul_apply, Fintype.sum_sum_type, add_sub_cancel_left]
      exact Valuation.map_sum_lt _ one_ne_zero fun m _ => val_mul_lt (hxi _ _) (hl _ _)
  have hd1 : valuation k (x.toBlocks₁₁.det * j.val.toBlocks₁₁.det) = 1 := by
    rw [map_mul, hxd, one_mul, (val_det_blocks hj).1]
  refine ⟨⟨hprod, ?_, ?_⟩, hcong⟩
  · rw [← hd1]
    refine Valuation.map_eq_of_sub_lt _ ?_
    rw [hd1]; exact hcong
  · intro e a
    rw [mul_apply, Fintype.sum_sum_type]
    refine Valuation.map_add_lt _ (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
      (Valuation.map_sum_lt _ one_ne_zero fun m _ => ?_)
    · rw [mul_comm]; exact val_mul_lt (hJ _ _) (hxl _ _)
    · exact val_mul_lt (hxi _ _) (hl _ _)

end Blocks

theorem om_datum : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D E : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]
    (ξ μ₀ : kˣ →* ℂˣ), IsTame ξ → IsUnram μ₀ →
    ∀ j ∈ parahoric k A D, ∀ d : kˣ, (d : k) = (j : Matrix (A ⊕ D) (A ⊕ D) k).toBlocks₂₂.det →
    om (μ₀ * ξ) j (1 : GL (A ⊕ E) k) (datum ξ : Matrix (A ⊕ E) (A ⊕ D) k → ℂ) = fun x => (ξ d : ℂ) * datum ξ x := by
  intro k _ _ _ _ A D E _ _ _ _ _ _ ξ μ₀ hξ hμ j hj d hd
  funext x
  have hK := (mem_parahoric.1 hj).1
  have hdetv : valuation k (GeneralLinearGroup.det j : k) = 1 := (nabs_eq_one_iff _).1 (nabs_det_of_mem_KO hK)
  have hμj : μ₀ (GeneralLinearGroup.det j) = 1 := hμ _ hdetv
  simp only [om, nabs_det_of_mem_KO hK, MonoidHom.mul_apply, hμj, one_mul, map_one, mul_one, inv_one,
    Units.val_one, Real.one_rpow, Complex.ofReal_one]
  rw [show nabs k 1 = 1 by simp [nabs], Real.one_rpow, Complex.ofReal_one, mul_one, Matrix.one_mul]
  unfold datum
  obtain ⟨h11, h22⟩ := val_det_blocks hj
  by_cases hx : InSupp x
  · obtain ⟨hs, hc⟩ := inSupp_mul hx hj
    have n11 : j.val.toBlocks₁₁.det ≠ 0 := fun h0 => by rw [h0, map_zero] at h11; exact zero_ne_one h11
    set u : kˣ := Units.mk0 _ n11 with hu
    have hdv : valuation k (d : k) = 1 := by rw [hd]; exact h22
    have t1 : ξ (GeneralLinearGroup.det j) = ξ (u * d) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, hdv, mul_one]; exact h11) ?_
      rw [Units.val_mul, hd, GeneralLinearGroup.val_det_apply]
      exact det_cong hj
    have t2 : ξ (Units.mk0 _ hs.det_ne) = ξ (Units.mk0 _ hx.det_ne * u) := by
      refine tame_eq hξ (by rw [Units.val_mul, map_mul, Units.val_mk0, hx.2.1, one_mul]; exact h11) ?_
      rw [Units.val_mul, Units.val_mk0, Units.val_mk0]
      exact hc
    rw [dif_pos hs, dif_pos hx, t1, t2, map_mul, map_mul]
    simp only [Units.val_mul, _root_.mul_inv_rev, Units.val_inv_eq_inv_val]
    have a1 : (ξ u : ℂ) ≠ 0 := Units.ne_zero _
    field_simp
  · have hs : ¬ InSupp (x * j.val) := fun hs => by
      have := (inSupp_mul hs (inv_mem hj)).1
      rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at this
      exact hx this
    rw [dif_neg hs, dif_neg hx, mul_zero, mul_zero]

end GlobalTheory.DatumEigen
