import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.MemXspIff

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

section om

variable {k r : ℕ}

lemma mv_sum {ι : Type*} (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Finset ι)
    (v : ι → Fin (2 * r + k + 1) → ℂ) : M *ᵥ (∑ i ∈ s, v i) = ∑ i ∈ s, M *ᵥ v i := by
  first
  | exact Matrix.mulVec_sum M s v
  | simpa using map_sum (Matrix.mulVecLin M) v s
  | (induction s using Finset.cons_induction with
     | empty => simp
     | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, Matrix.mulVec_add, ih])

lemma hm_sum_l {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (∑ i ∈ s, c i • v i) w = ∑ i ∈ s, c i * herm (Hpk k r) (v i) w := by
  unfold herm
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.sum_cons]
    rw [Matrix.mulVec_add, ← ih]
    simp [Matrix.mulVec_smul]

lemma hm_sum_r {ι : Type*} (s : Finset ι) (c : ι → ℂ) (v : ι → Fin (2 * r + k + 1) → ℂ)
    (w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) w (∑ i ∈ s, c i • v i) = ∑ i ∈ s, star (c i) * herm (Hpk k r) w (v i) := by
  unfold herm
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp only [Finset.sum_cons, star_add]
    rw [← ih]
    simp [star_smul]

lemma herm_bvec_eI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (eI k r a)) = v (esI k r a) := by
  have ha := a.isLt
  have key : ∀ j, Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
    intro j
    by_cases hj : j = esI k r a
    · subst hj
      rw [if_pos rfl]
      simp only [Hpk, eI, esI, Fin.val_mk]
      have h3 : ¬ r ≤ (a : ℕ) := by omega
      simp only [h3, false_and, if_false]
      split_ifs <;> first | rfl | (exfalso; omega) | omega
    · rw [if_neg hj]
      have hj' : (j : ℕ) ≠ (esI k r a : ℕ) := fun h => hj (Fin.ext h)
      simp only [Hpk, eI, esI, Fin.val_mk] at hj' ⊢
      have h3 : ¬ r ≤ (a : ℕ) := by omega
      simp only [h3, false_and, if_false]
      split_ifs <;> first | rfl | (exfalso; omega) | omega
  unfold herm bvec
  have hs : star (Pi.single (eI k r a) (1 : ℂ) : Fin (2 * r + k + 1) → ℂ) = Pi.single (eI k r a) 1 := by
    ext i
    by_cases h : i = eI k r a <;> simp [Pi.single_apply, h]
  rw [hs]
  simp [key, Matrix.mulVec, dotProduct, Pi.single_apply]

lemma fvec_lt (z : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    fvec k r z ⟨a.val, by omega⟩ = bvec (eI k r a) := by
  unfold fvec
  first
  | exact dif_pos a.isLt
  | simp
  | rfl

lemma wb_N {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : PI.UnitaryGroupMassFormula.GsFr.wbPart k r (n *ᵥ v) = PI.UnitaryGroupMassFormula.GsFr.wbPart k r v := by
  simp only [Formalism.QuantumDeterminants.Nset, Set.mem_setOf_eq] at hn
  obtain ⟨-, h1, h2⟩ := hn
  funext i
  unfold wbPart
  split_ifs with hi
  · rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single i]
    · rw [h2 i i hi.1 hi.2 hi.1, if_pos rfl, one_mul]
    · intro j _ hji
      by_cases hj1 : j.val < r
      · have hle : (⟨j.val, hj1⟩ : Fin r).val ≤ i.val := by
          show j.val ≤ i.val
          omega
        have hc := h1 ⟨j.val, hj1⟩ i hle
        have he : eI k r ⟨j.val, hj1⟩ = j := Fin.ext rfl
        rw [he] at hc
        rw [hc, if_neg (fun h => hji h.symm), zero_mul]
      · by_cases hj2 : j.val ≤ r + k
        · rw [h2 i j (by omega) hj2 hi.1, if_neg (fun h => hji h.symm), zero_mul]
        · have hjl := j.isLt
          have hes : j = esI k r ⟨2 * r + k - j.val, by omega⟩ :=
            Fin.ext (by simp only [esI, Fin.val_mk]; omega)
          rw [hes, hv, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rfl

lemma prW_N {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ}
    (hv : ∀ a : Fin r, v (esI k r a) = 0) : prW k r z (n *ᵥ v) = prW k r z v := by
  unfold prW
  rw [wb_N hn hv]

lemma adj_col (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (a : Fin (r + 1)) (ha : a ≠ Fin.last r) :
    ∑ b, Z.adjugate b (Fin.last r) * Z a b = 0 := by
  have h := congrFun (congrFun (Matrix.mul_adjugate Z) a) (Fin.last r)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne ha, smul_zero] at h
  rw [← h]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma adj_row (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ) (b : Fin (r + 1)) (hb : b ≠ Fin.last r) :
    ∑ a, Z.adjugate (Fin.last r) a * Z a b = 0 := by
  have h := congrFun (congrFun (Matrix.adjugate_mul Z) (Fin.last r)) b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply_ne (Ne.symm hb), smul_zero] at h
  exact h

lemma xcof_esI (z z' : Fin (2 * r + k + 1) → ℂ) (y : B.Mat k r) (a : Fin r) :
    xcof k r z z' y (esI k r a) = 0 := by
  unfold xcof
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hrow : ∀ b, (y *ᵥ fvec k r z' b) (esI k r a) = Zhat k r z z' y ⟨a.val, by omega⟩ b := by
    intro b
    rw [← herm_bvec_eI (y *ᵥ fvec k r z' b) a, ← fvec_lt z a]
    rfl
  simp only [hrow]
  exact adj_col _ _ (by rw [Ne, Fin.ext_iff, Fin.val_last]; exact Nat.ne_of_lt a.isLt)

lemma unitri_det {m : ℕ} {U : Matrix (Fin m) (Fin m) ℂ} (hU : U ∈ C2.UTset m) : U.det = 1 := by
  have hU' : (∀ i j : Fin m, j < i → U i j = 0) ∧ ∀ i, U i i = 1 := hU
  obtain ⟨h1, h2⟩ := hU'
  rw [Matrix.det_of_upperTriangular (fun i j hij => h1 i j hij)]
  simp [h2]

lemma adj_of_inv {m : ℕ} {U V : Matrix (Fin m) (Fin m) ℂ} (hd : U.det = 1) (hVU : U * V = 1) :
    U.adjugate = V := by
  calc U.adjugate = U.adjugate * (U * V) := by rw [hVU, Matrix.mul_one]
    _ = (U.adjugate * U) * V := by rw [Matrix.mul_assoc]
    _ = V := by rw [Matrix.adjugate_mul, hd, one_smul, Matrix.one_mul]

lemma zhat_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (y : B.Mat k r) :
    Zhat k r z z' (n * y * n') = (C2.uMap k r z n⁻¹)ᴴ * Zhat k r z z' y * C2.uMap k r z' n' := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hni := Nc.inv_mem n hn
  have h := Formalism.FourierDecayAlt.P.zhat_equivalence k r z z' hz hz' n⁻¹ ⟨1, one_mem_UW z, n⁻¹, hni, (one_mul _).symm⟩
    n' ⟨1, one_mem_UW z', n', hn', (one_mul _).symm⟩ y
  rwa [Matrix.nonsing_inv_nonsing_inv n (Nc.unit n hn)] at h

lemma uMap_inv {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) {n : B.Mat k r} (hn : n ∈ Nset k r) :
    C2.uMap k r z n * C2.uMap k r z n⁻¹ = 1 ∧ C2.uMap k r z n⁻¹ * C2.uMap k r z n = 1 := by
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hni := Nc.inv_mem n hn
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hS : n ∈ Sset k r z := ⟨1, one_mem_UW z, n, hn, (one_mul _).symm⟩
  have hSi : n⁻¹ ∈ Sset k r z := ⟨1, one_mem_UW z, n⁻¹, hni, (one_mul _).symm⟩
  have h1 : C2.uMap k r z 1 = 1 := hF.2 1 (one_mem_UW z)
  constructor
  · rw [← (hF.1 n hS).2.2 n⁻¹ hSi, Matrix.mul_nonsing_inv _ (Nc.unit n hn), h1]
  · rw [← (hF.1 n⁻¹ hSi).2.2 n hS, Matrix.nonsing_inv_mul _ (Nc.unit n hn), h1]

lemma key_alg {U' Zt Z Vm : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ} (hU'adj : U' * U'.adjugate = 1)
    (hadj : Zt.adjugate = U'.adjugate * (Z.adjugate * Vmᴴ)) (hV : Vm ∈ C2.UTset (r + 1)) (c : Fin (r + 1)) :
    ∑ b, U' c b * Zt.adjugate b (Fin.last r) = Z.adjugate c (Fin.last r) := by
  have hV' : (∀ i j : Fin (r + 1), j < i → Vm i j = 0) ∧ ∀ i, Vm i i = 1 := hV
  obtain ⟨hV1, hV2⟩ := hV'
  have h1 : ∑ b, U' c b * Zt.adjugate b (Fin.last r) = (U' * Zt.adjugate) c (Fin.last r) :=
    (Matrix.mul_apply).symm
  rw [h1, hadj, ← Matrix.mul_assoc, hU'adj, Matrix.one_mul, Matrix.mul_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · simp [Matrix.conjTranspose_apply, hV2]
  · intro d _ hd
    have hlt : d < Fin.last r := lt_of_le_of_ne (Fin.le_last d) hd
    simp [Matrix.conjTranspose_apply, hV1 _ _ hlt]
  · intro h
    exact absurd (Finset.mem_univ _) h

lemma regroup (M : B.Mat k r) (A C : Fin (r + 1) → ℂ) (U' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ)
    (f : Fin (r + 1) → Fin (2 * r + k + 1) → ℂ) (h : ∀ c, ∑ b, U' c b * A b = C c) :
    ∑ b, A b • (M *ᵥ ∑ c, U' c b • f c) = M *ᵥ ∑ c, C c • f c := by
  calc ∑ b, A b • (M *ᵥ ∑ c, U' c b • f c) = ∑ b, ∑ c, (U' c b * A b) • (M *ᵥ f c) := by
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [mv_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mulVec_smul, smul_smul, mul_comm (A b) (U' c b)]
    _ = ∑ c, ∑ b, (U' c b * A b) • (M *ᵥ f c) := Finset.sum_comm
    _ = ∑ c, C c • (M *ᵥ f c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← Finset.sum_smul, h c]
    _ = M *ᵥ ∑ c, C c • f c := by
        rw [mv_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Matrix.mulVec_smul]

theorem xcof_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hz' : C2.StdZ k r z') {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) (y : B.Mat k r) :
    xcof k r z z' (n * y * n') = n *ᵥ xcof k r z z' y := by
  have hF' := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z' hz'
  have hF := Formalism.FourierDecayAlt.P.unipotent_map_frame k r z hz
  have hS : n ∈ Sset k r z := ⟨1, one_mem_UW z, n, hn, (one_mul _).symm⟩
  have hS' : n' ∈ Sset k r z' := ⟨1, one_mem_UW z', n', hn', (one_mul _).symm⟩
  have hV := (hF.1 n hS).2.1
  have hU' := (hF'.1 n' hS').2.1
  have hVU := (uMap_inv hz hn).1
  have hdU : ((C2.uMap k r z n⁻¹)ᴴ).det = 1 := by
    rw [Matrix.det_conjTranspose]
    have : (C2.uMap k r z n⁻¹).det * (C2.uMap k r z n).det = 1 := by
      rw [← Matrix.det_mul, (uMap_inv hz hn).2, Matrix.det_one]
    rw [unitri_det hV, mul_one] at this
    rw [this, star_one]
  have hadjU : ((C2.uMap k r z n⁻¹)ᴴ).adjugate = (C2.uMap k r z n)ᴴ :=
    adj_of_inv hdU (by rw [← Matrix.conjTranspose_mul, hVU, Matrix.conjTranspose_one])
  have hU'adj : C2.uMap k r z' n' * (C2.uMap k r z' n').adjugate = 1 := by
    rw [Matrix.mul_adjugate, unitri_det hU', one_smul]
  have hadj : (Zhat k r z z' (n * y * n')).adjugate =
      (C2.uMap k r z' n').adjugate * ((Zhat k r z z' y).adjugate * (C2.uMap k r z n)ᴴ) := by
    rw [zhat_N hz hz' hn hn' y, Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib, hadjU]
  have hfr : ∀ b, n' *ᵥ fvec k r z' b = ∑ c, C2.uMap k r z' n' c b • fvec k r z' c := (hF'.1 n' hS').1
  unfold xcof
  have e1 : ∀ b, (n * y * n') *ᵥ fvec k r z' b = (n * y) *ᵥ ∑ c, C2.uMap k r z' n' c b • fvec k r z' c := by
    intro b; rw [← hfr b, mulVec_mulVec]
  simp only [e1]
  rw [regroup (n * y) _ _ _ _ (key_alg hU'adj hadj hV), ← mulVec_mulVec, mv_sum y]
  simp only [mulVec_smul]

theorem satOm : SatOm := by
  intro k r z z' hk hr hz hz' y hy hG n hn n' hn'
  unfold omW
  rw [xcof_N hz hz' hn hn' y, prW_N hn (xcof_esI z z' y)]

end om

end PI.UnitaryGroupMassFormula.GsFr
