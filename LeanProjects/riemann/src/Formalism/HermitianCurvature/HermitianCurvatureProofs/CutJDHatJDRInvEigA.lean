import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDRInvDefs
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet

open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutMP.InvEigA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

variable {k r : ℕ}

def e0A (k r : ℕ) (p : Fin (r + k + 1)) : Fin (2 * r + k + 1) := ⟨p.val, by have := p.isLt; omega⟩

theorem anisotropic_index_injective : Function.Injective (e0A k r) := fun a b h => by
  simp only [e0A, Fin.ext_iff] at h; exact Fin.ext h

theorem sum_embA {a b : ℕ} (f : Fin a → Fin b) (hf : Function.Injective f) (G : Fin b → ℂ)
    (hG : ∀ q, (∀ p, f p ≠ q) → G q = 0) : ∑ p, G (f p) = ∑ q, G q := by
  classical
  calc ∑ p, G (f p) = ∑ q ∈ Finset.univ.map ⟨f, hf⟩, G q := by rw [Finset.sum_map]; rfl
    _ = ∑ q, G q := Finset.sum_subset (Finset.subset_univ _) (fun q _ hq => hG q (fun p hp => hq (by
        simp only [Finset.mem_map, Finset.mem_univ, true_and]; exact ⟨p, hp⟩)))

theorem hermitian_form_column_vanishes (j y : Fin (2 * r + k + 1)) (hj : j.val ≤ r + k) (hy : y.val < r) : Hpk k r y j = 0 := by
  unfold Hpk
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_esI_left (a : Fin r) (x : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) x = if x = eI k r a then 1 else 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem hpk_esI_right (a : Fin r) (y : Fin (2 * r + k + 1)) :
    Hpk k r y (esI k r a) = if y = eI k r a then 1 else 0 := by
  have ha := a.isLt
  unfold Hpk
  simp only [esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

variable {z' : Fin (2 * r + k + 1) → ℂ} {w m : B.Mat k r}

theorem w_colA (hw : w ∈ UWset k r z') (q : Fin (2 * r + k + 1)) (hq : q.val < r) (y : Fin (2 * r + k + 1)) :
    w y q = if y = q then 1 else 0 := by
  have h1 := congrFun (hw.2.1 ⟨q.val, hq⟩).1 y
  have e : eI k r ⟨q.val, hq⟩ = q := Fin.ext rfl
  rw [e] at h1
  simpa [bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using h1

theorem m_colA (hm : m ∈ Nset k r) (q i : Fin (2 * r + k + 1)) (hq : q.val < r) (hi : q.val ≤ i.val) :
    m i q = if i = q then 1 else 0 := by
  have := hm.2.1 ⟨q.val, hq⟩ i hi
  have e : eI k r ⟨q.val, hq⟩ = q := Fin.ext rfl
  rwa [e] at this

theorem mw_colXA (hw : w ∈ UWset k r z') (i q : Fin (2 * r + k + 1)) (hq : q.val < r) : (m * w) i q = m i q := by
  rw [Matrix.mul_apply]
  simp only [w_colA hw q hq, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem mw_XA (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (i q : Fin (2 * r + k + 1)) (hi : r ≤ i.val)
    (hq : q.val < r) : (m * w) i q = 0 := by
  rw [mw_colXA hw i q hq, m_colA hm q i hq (by omega), if_neg]
  intro h; subst h; omega

theorem mw_zA (hz' : inWb k r z') (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (i : Fin (2 * r + k + 1))
    (hi : r ≤ i.val) : ((m * w) *ᵥ z') i = z' i := by
  rw [← Matrix.mulVec_mulVec, hw.2.2]
  have e : ∀ j, m i j * z' j = (if i = j then 1 else 0) * z' j := by
    intro j
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [hm.2.2 i j hj.1 hj.2 hi]
    · rw [hz' j (by omega), mul_zero, mul_zero]
  simp only [Matrix.mulVec, dotProduct, e, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem mw_GV (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) : m * w ∈ B.GV k r := WeylGroupFacts.uh_mul hm.1 hw.1

theorem charpoly_eq_of_isIso (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) :
    (m * w)⁻¹ = Hpk k r * (m * w)ᴴ * Hpk k r := Formalism.FourierDecayAlt.P.PBG.inv_GV (mw_GV hw hm)

theorem P_row (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    ((m * w)⁻¹) (esI k r a) j = ∑ y, star ((m * w) y (eI k r a)) * Hpk k r y j := by
  rw [charpoly_eq_of_isIso hw hm, Matrix.mul_apply]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [Matrix.mul_apply]
  simp only [hpk_esI_left, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Matrix.conjTranspose_apply]

theorem esI_of (i : Fin (2 * r + k + 1)) (hi : r + k < i.val) :
    esI k r ⟨2 * r + k - i.val, by have := i.isLt; omega⟩ = i := by
  ext; simp [esI]; omega

theorem inverse_product_block_zero (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (i j : Fin (2 * r + k + 1)) (hi : r + k < i.val)
    (hj : j.val ≤ r + k) : ((m * w)⁻¹) i j = 0 := by
  rw [← esI_of i hi, P_row hw hm]
  refine Finset.sum_eq_zero (fun y _ => ?_)
  by_cases hy : y.val < r
  · rw [hermitian_form_column_vanishes j y hj hy, mul_zero]
  · rw [mw_XA hw hm y _ (by omega) (by simp [eI]; omega), star_zero, zero_mul]

theorem P_XX (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (a b : Fin r) :
    ((m * w)⁻¹) (esI k r a) (esI k r b) = star ((m * w) (eI k r b) (eI k r a)) := by
  rw [P_row hw hm]
  simp only [hpk_esI_right, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem det_inverse_product_block (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) :
    ((m * w)⁻¹).det = (((m * w)⁻¹).submatrix (e0A k r) (e0A k r)).det := by
  classical
  set P := (m * w)⁻¹ with hP
  rw [Matrix.twoBlockTriangular_det P (fun i : Fin (2 * r + k + 1) => i.val ≤ r + k)
    (fun i hi j hj => inverse_product_block_zero hw hm i j (by omega) hj)]
  have e1 : (P.toSquareBlockProp fun i : Fin (2 * r + k + 1) => i.val ≤ r + k).det =
      (P.submatrix (e0A k r) (e0A k r)).det := by
    let e : Fin (r + k + 1) ≃ {i : Fin (2 * r + k + 1) // i.val ≤ r + k} :=
      { toFun := fun p => ⟨e0A k r p, by simp [e0A]; omega⟩
        invFun := fun i => ⟨i.1.val, by have := i.2; omega⟩
        left_inv := fun p => by ext; simp [e0A]
        right_inv := fun i => by ext; simp [e0A] }
    rw [← Matrix.det_submatrix_equiv_self e]
    rfl
  have e2 : (P.toSquareBlockProp fun i : Fin (2 * r + k + 1) => ¬ i.val ≤ r + k).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one (fun i _ => ?_)
      obtain ⟨i, hi⟩ := i
      have hi' : r + k < i.val := by omega
      show P i i = 1
      rw [← esI_of i hi', hP, P_XX hw hm, mw_colXA hw _ _ (by simp [eI]; omega),
        m_colA hm _ _ (by simp [eI]; omega) le_rfl, if_pos rfl, star_one]
    · intro i j hij
      obtain ⟨i, hi⟩ := i
      obtain ⟨j, hj⟩ := j
      have hi' : r + k < i.val := by omega
      have hj' : r + k < j.val := by omega
      have hlt : j.val < i.val := hij
      show P i j = 0
      rw [← esI_of i hi', ← esI_of j hj', hP, P_XX hw hm, mw_colXA hw _ _ (by simp [eI]; omega),
        m_colA hm _ _ (by simp [eI]; omega) (by simp [eI]; omega), if_neg (by simp [eI, Fin.ext_iff]; omega),
        star_zero]
  rw [e1, e2, mul_one]

theorem herm_bvec (z' : Fin (2 * r + k + 1) → ℂ) (x : Fin (2 * r + k + 1)) :
    herm (Hpk k r) (bvec x) z' = (star z' ᵥ* Hpk k r) x := by
  simp only [herm, bvec, Matrix.mulVec, dotProduct, Matrix.vecMul, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem zeta_full (hz' : inWb k r z') (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) (j : Fin (2 * r + k + 1))
    (hj : j.val ≤ r + k) : ((star z' ᵥ* Hpk k r) ᵥ* (m * w)⁻¹) j = (star z' ᵥ* Hpk k r) j := by
  rw [charpoly_eq_of_isIso hw hm, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Formalism.FourierDecayAlt.P.Qx2.hpk_sq',
    Matrix.one_mul, ← Matrix.vecMul_vecMul, ← Matrix.star_mulVec]
  simp only [Matrix.vecMul, dotProduct]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  by_cases hl : l.val < r
  · rw [hermitian_form_column_vanishes j l hj hl, mul_zero, mul_zero]
  · rw [Pi.star_apply, Pi.star_apply, mw_zA hz' hw hm l (by omega)]

theorem zeta_fix (hz' : inWb k r z') (hw : w ∈ UWset k r z') (hm : m ∈ Nset k r) :
    (fun p => herm (Hpk k r) (bvec (e0A k r p)) z') ᵥ* (((m * w)⁻¹).submatrix (e0A k r) (e0A k r)) =
      fun p => herm (Hpk k r) (bvec (e0A k r p)) z' := by
  funext q
  have hq : (e0A k r q).val ≤ r + k := by simp [e0A]; omega
  rw [herm_bvec, ← zeta_full hz' hw hm _ hq]
  simp only [Matrix.vecMul, dotProduct, Matrix.submatrix_apply, herm_bvec]
  refine sum_embA (e0A k r) anisotropic_index_injective (fun x => (star z' ᵥ* Hpk k r) x * ((m * w)⁻¹) x (e0A k r q)) (fun x hx => ?_)
  have : r + k < x.val := by
    by_contra hc
    exact hx ⟨x.val, by omega⟩ (Fin.ext (by simp [e0A]))
  show (star z' ᵥ* Hpk k r) x * ((m * w)⁻¹) x (e0A k r q) = 0
  rw [inverse_product_block_zero hw hm x _ this hq, mul_zero]

end Formalism.FourierDecayAlt.P.CutMP.InvEigA
