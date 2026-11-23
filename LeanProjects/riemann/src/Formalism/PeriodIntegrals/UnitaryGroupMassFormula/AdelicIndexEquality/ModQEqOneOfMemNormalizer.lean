import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

section Delta

variable {G : Type} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / (A.relIndex B : ℚ)

theorem idxRatio_eq_of_le (A B D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)
    (hA : D.relIndex A ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / (D.relIndex B : ℚ) := by
  have h1 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = D.relIndex A :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_left)
  have h2 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = D.relIndex B :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_right)
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hc0 : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply hA
    rw [← h1, h0, zero_mul]
  have hc : (D.relIndex (A ⊓ B) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  unfold idxRatio
  rw [← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hc]

theorem relIndex_inf_three_ne_zero {A B C L : Subgroup G} (hA : A.relIndex L ≠ 0)
    (hB : B.relIndex L ≠ 0) (hC : C.relIndex L ≠ 0) : (A ⊓ B ⊓ C).relIndex L ≠ 0 := by
  exact Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero hA hB) hC

theorem relIndex_self_ne_zero (A : Subgroup G) : A.relIndex A ≠ 0 := by
  rw [Subgroup.relIndex_self]
  exact one_ne_zero

theorem idxRatio_mul (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by
  have hDA := relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC
  have hDB := relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC
  rw [idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hDA,
    idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB,
    idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hDA,
    div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex A : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hDB)]

private theorem relIndex_map_of_injective (X Y : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]

theorem idxRatio_map (A B : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  unfold idxRatio
  rw [relIndex_map_of_injective _ _ f hf, relIndex_map_of_injective _ _ f hf]

theorem map_conj_mul' (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one' (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem relIndex_conj_conj_ne_zero (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    (K.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have h1 : K.map (MulAut.conj x).toMonoidHom =
      (K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [map_conj_mul', mul_inv_cancel_left]
  rw [h1, relIndex_map_of_injective _ _ _ (by intro a b h; simpa using h)]
  exact hK (y⁻¹ * x)

theorem relIndex_conj_right_ne_zero (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by
  have h := relIndex_conj_conj_ne_zero K hK 1 a
  rwa [map_conj_one'] at h

theorem dIdx_inv_eq (K : Subgroup G) (x : G) :
    dIdx K x⁻¹ = K.relIndex (K.map (MulAut.conj x).toMonoidHom) := by
  unfold dIdx
  rw [← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h),
    map_conj_mul', mul_inv_cancel, map_conj_one']

theorem modQ_eq_idxRatio (K : Subgroup G) (x : G) :
    modQ K x = idxRatio K (K.map (MulAut.conj x).toMonoidHom) := by
  unfold modQ idxRatio
  rw [dIdx_inv_eq]
  rfl

theorem dIdx_one (K : Subgroup G) : dIdx K 1 = 1 := by
  unfold dIdx
  rw [map_conj_one', Subgroup.relIndex_self]

theorem modQ_one (K : Subgroup G) : modQ K 1 = 1 := by
  unfold modQ
  simp [dIdx_one]

theorem modQ_inv (K : Subgroup G) (x : G) : modQ K x⁻¹ = (modQ K x)⁻¹ := by
  unfold modQ
  rw [inv_inv, inv_div]

theorem modQ_pos (K : Subgroup G) (hK : Commensurated K) (x : G) : 0 < modQ K x := by
  unfold modQ
  exact div_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x))) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hK x⁻¹)))

theorem modQ_mul (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (x * y) = modQ K x * modQ K y := by
  rw [modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio,
    ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom
      (by intro a b h; simpa using h), map_conj_mul']
  exact (idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom)
    (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x)
    (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm

theorem modQ_pow (K : Subgroup G) (hK : Commensurated K) (x : G) (m : ℕ) :
    modQ K (x ^ m) = (modQ K x) ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, modQ_one]
  | succ m ih => rw [pow_succ, modQ_mul K hK, ih, pow_succ]

theorem modQ_conj (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (y * x * y⁻¹) = modQ K x := by
  rw [modQ_mul K hK, modQ_mul K hK, modQ_inv]
  have hy := (modQ_pos K hK y).ne'
  rw [mul_comm (modQ K y) (modQ K x), mul_assoc, mul_inv_cancel₀ hy, mul_one]

theorem modQ_eq_one_of_map_eq (K : Subgroup G) (x : G)
    (h : K.map (MulAut.conj x).toMonoidHom = K) : modQ K x = 1 := by
  rw [modQ_eq_idxRatio, h]
  unfold idxRatio
  simp [Subgroup.relIndex_self]

theorem map_conj_of_mem_normalizer (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj x).toMonoidHom = K := by
  have hx' : ∀ h, h ∈ K ↔ x * h * x⁻¹ ∈ K := by
    intro h
    have h2 := Subgroup.mem_normalizer_iff.mp hx h
    simpa using h2
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact (hx' k).mp hk
  · intro hy
    refine ⟨x⁻¹ * y * x, (hx' _).mpr ?_, by group⟩
    convert hy using 1
    group

theorem modQ_eq_one_of_mem_normalizer (K : Subgroup G) {x : G} (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    modQ K x = 1 := by
  exact modQ_eq_one_of_map_eq K x (map_conj_of_mem_normalizer K hx)

theorem modQ_eq_one_of_mem (K : Subgroup G) {k : G} (hk : k ∈ K) : modQ K k = 1 := by
  apply modQ_eq_one_of_mem_normalizer
  rw [Subgroup.mem_normalizer_iff]
  intro h
  try simp only [SetLike.mem_coe]
  constructor
  · intro hh
    exact K.mul_mem (K.mul_mem hk hh) (K.inv_mem hk)
  · intro hh
    have h2 := K.mul_mem (K.mul_mem (K.inv_mem hk) hh) hk
    simpa [mul_assoc] using h2

theorem modQ_eq_one_of_pow (K : Subgroup G) (hK : Commensurated K) (x : G) {m : ℕ} (hm : m ≠ 0)
    (h : modQ K (x ^ m) = 1) : modQ K x = 1 := by
  rw [modQ_pow K hK] at h
  exact (pow_eq_one_iff_of_nonneg (modQ_pos K hK x).le hm).mp h

theorem modQ_eq_one_of_pow_normalizer (K : Subgroup G) (hK : Commensurated K) (x : G) {m : ℕ}
    (hm : m ≠ 0) (h : x ^ m ∈ Subgroup.normalizer (K : Set G)) : modQ K x = 1 := by
  exact modQ_eq_one_of_pow K hK x hm (modQ_eq_one_of_mem_normalizer K h)

theorem modQ_eq_one_closure (K : Subgroup G) (hK : Commensurated K) (S : Set G)
    (hS : ∀ s ∈ S, modQ K s = 1) : ∀ x ∈ Subgroup.closure S, modQ K x = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact hS s hs
  | one => exact modQ_one K
  | mul a b _ _ ha hb => rw [modQ_mul K hK, ha, hb, one_mul]
  | inv a _ ha => rw [modQ_inv, ha, inv_one]

theorem dIdx_eq_of_modQ (K : Subgroup G) (hK : Commensurated K) (x : G) (h : modQ K x = 1) :
    dIdx K x = dIdx K x⁻¹ := by
  unfold modQ at h
  have h2 : ((dIdx K x⁻¹ : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (hK x⁻¹)
  rw [div_eq_one_iff_eq h2] at h
  exact_mod_cast h

end Delta

theorem indexEq_of_modQ_eq_one (hK : KComm)
    (h : ∀ (I : Formalism.MainNotions.S.AutInst) (x : I.Gf), modQ (PI.AdIndexEq.Ksub I) x = 1) :
    PI.AdIndexEq.IndexEq := by
  unfold PI.AdIndexEq.IndexEq
  intro I x
  exact dIdx_eq_of_modQ (PI.AdIndexEq.Ksub I) (hK I) x (h I x)

end PI.UnitaryGroupMassFormula.AdIndexEq
