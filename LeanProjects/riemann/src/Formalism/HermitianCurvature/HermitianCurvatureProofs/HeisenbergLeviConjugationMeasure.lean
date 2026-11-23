import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.B2x5

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section Herm

variable {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ)

lemma herm_add_left (u u' v : ι → ℂ) : herm H (u + u') v = herm H u v + herm H u' v := by
  simp only [herm, mulVec_add, dotProduct_add]

lemma herm_sub_left (u u' v : ι → ℂ) : herm H (u - u') v = herm H u v - herm H u' v := by
  simp only [herm, mulVec_sub, dotProduct_sub]

lemma herm_smul_left (c : ℂ) (u v : ι → ℂ) : herm H (c • u) v = c * herm H u v := by
  simp only [herm, mulVec_smul, dotProduct_smul, smul_eq_mul]

lemma herm_neg_left (u v : ι → ℂ) : herm H (-u) v = -herm H u v := by
  simp only [herm, mulVec_neg, dotProduct_neg]

lemma herm_add_right (u v v' : ι → ℂ) : herm H u (v + v') = herm H u v + herm H u v' := by
  simp only [herm, star_add, add_dotProduct]

lemma herm_neg_right (u v : ι → ℂ) : herm H u (-v) = -herm H u v := by
  simp only [herm, star_neg, neg_dotProduct]

lemma herm_zero_right (u : ι → ℂ) : herm H u 0 = 0 := by
  simp [herm]

lemma herm_conj (hH : Hᴴ = H) (u v : ι → ℂ) : conj (herm H u v) = herm H v u := by
  have h : ∀ i j, star (H i j) = H j i := fun i j => by
    have := congrFun (congrFun hH j) i
    rwa [conjTranspose_apply] at this
  simp only [herm, dotProduct, mulVec, Pi.star_apply, starRingEnd_apply, star_sum, star_mul', star_star, h,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma herm_UH [DecidableEq ι] {g : Matrix ι ι ℂ} (hg : g ∈ UH H) (u v : ι → ℂ) :
    herm H (g *ᵥ u) (g *ᵥ v) = herm H u v := by
  have hg' : gᴴ * H * g = H := hg
  simp only [herm]
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hg']

end Herm

lemma mat_ext {m : ℕ} {A B : Matrix (Fin m) (Fin m) ℂ} (h : ∀ u, A *ᵥ u = B *ᵥ u) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [mulVec, dotProduct, Pi.single_apply] using this

def i0 (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := eI k (1 + r') (a0 r')

def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := esI k (1 + r') (a0 r')

def res (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : Fin (2 * r' + k + 1) → ℂ := fun j => u (levPos k 1 r' j)

lemma first_index_val (k r' : ℕ) : (i0 k r').val = 0 := rfl

lemma iL_val (k r' : ℕ) : (iL k r').val = 2 * r' + k + 2 := by
  show 2 * (1 + r') + k - 0 = 2 * r' + k + 2
  omega

lemma lev_val (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : (levPos k 1 r' j).val = j.val + 1 := rfl

lemma sum_split (k r' : ℕ) (f : Fin (2 * (1 + r') + k + 1) → ℂ) :
    ∑ p, f p = f (i0 k r') + ∑ j, f (levPos k 1 r' j) + f (iL k r') := by
  have hinj : Function.Injective (levPos k 1 r') := fun a b h => by
    have := congrArg Fin.val h
    rw [lev_val, lev_val] at this
    exact Fin.ext (by omega)
  have h1 : i0 k r' ∉ insert (iL k r') (Finset.univ.image (levPos k 1 r')) := by
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_or, not_exists]
    refine ⟨fun h => ?_, fun j h => ?_⟩
    · have := congrArg Fin.val h
      rw [first_index_val, iL_val] at this
      omega
    · have := congrArg Fin.val h
      rw [first_index_val, lev_val] at this
      omega
  have h2 : iL k r' ∉ Finset.univ.image (levPos k 1 r') := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro j h
    have := congrArg Fin.val h
    rw [iL_val, lev_val] at this
    have := j.isLt
    omega
  have huniv : (Finset.univ : Finset (Fin (2 * (1 + r') + k + 1))) =
      insert (i0 k r') (insert (iL k r') (Finset.univ.image (levPos k 1 r'))) := by
    ext p
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_image, true_and, true_iff]
    have hp := p.isLt
    by_cases h0 : p.val = 0
    · exact Or.inl (Fin.ext h0)
    by_cases hL : p.val = 2 * r' + k + 2
    · exact Or.inr (Or.inl (Fin.ext (by rw [hL, iL_val])))
    · refine Or.inr (Or.inr ⟨⟨p.val - 1, by omega⟩, Fin.ext ?_⟩)
      rw [lev_val]
      show p.val - 1 + 1 = p.val
      omega
  rw [huniv, Finset.sum_insert h1, Finset.sum_insert h2,
    Finset.sum_image (by intro a _ b _ h; exact hinj h)]
  ring

lemma idx_cases (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) :
    p = i0 k r' ∨ (∃ j, p = levPos k 1 r' j) ∨ p = iL k r' := by
  have hp := p.isLt
  by_cases h0 : p.val = 0
  · exact Or.inl (Fin.ext h0)
  by_cases hL : p.val = 2 * r' + k + 2
  · exact Or.inr (Or.inr (Fin.ext (by rw [hL, iL_val])))
  · refine Or.inr (Or.inl ⟨⟨p.val - 1, by omega⟩, Fin.ext ?_⟩)
    rw [lev_val]
    show p.val = p.val - 1 + 1
    omega

lemma vec_ext (k r' : ℕ) {u v : Fin (2 * (1 + r') + k + 1) → ℂ} (h0 : u (i0 k r') = v (i0 k r'))
    (h1 : res k r' u = res k r' v) (h2 : u (iL k r') = v (iL k r')) : u = v := by
  funext p
  rcases idx_cases k r' p with h | ⟨j, h⟩ | h
  · subst h; exact h0
  · subst h; exact congrFun h1 j
  · subst h; exact h2

lemma hermitian_form_first_basis (k r' : ℕ) (q : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (i0 k r') q = if q = iL k r' then 1 else 0 := by
  have hq := q.isLt
  simp only [Hpk, first_index_val, iL_val, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma H_iL (k r' : ℕ) (q : Fin (2 * (1 + r') + k + 1)) :
    Hpk k (1 + r') (iL k r') q = if q = i0 k r' then 1 else 0 := by
  have hq := q.isLt
  simp only [Hpk, first_index_val, iL_val, Fin.ext_iff]
  split_ifs <;> first | rfl | omega

lemma hermitian_levi_entry_zero (k r' : ℕ) (i : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (levPos k 1 r' i) (i0 k r') = 0 := by
  have hi := i.isLt
  simp only [Hpk, first_index_val, lev_val, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (simp_all [Fin.ext_iff] <;> omega)

lemma H_lev_iL (k r' : ℕ) (i : Fin (2 * r' + k + 1)) : Hpk k (1 + r') (levPos k 1 r' i) (iL k r') = 0 := by
  have hi := i.isLt
  simp only [Hpk, iL_val, lev_val, Fin.ext_iff]
  split_ifs <;> first | rfl | omega | (simp_all [Fin.ext_iff] <;> omega)

lemma H_lev_lev (k r' : ℕ) (i j : Fin (2 * r' + k + 1)) :
    Hpk k (1 + r') (levPos k 1 r' i) (levPos k 1 r' j) = Hpk k r' i j := by
  have hi := i.isLt
  have hj := j.isLt
  have hij : levPos k 1 r' i = levPos k 1 r' j ↔ i = j := by
    rw [Fin.ext_iff, Fin.ext_iff, lev_val, lev_val]
    exact ⟨fun h => by omega, fun h => by omega⟩
  have e1 : ((levPos k 1 r' i).val < 1 + r' ∧
      (levPos k 1 r' i).val + (levPos k 1 r' j).val = 2 * (1 + r') + k) ↔
      (i.val < r' ∧ i.val + j.val = 2 * r' + k) := by
    rw [lev_val, lev_val]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩, fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩⟩
  have e2 : ((levPos k 1 r' j).val < 1 + r' ∧
      (levPos k 1 r' i).val + (levPos k 1 r' j).val = 2 * (1 + r') + k) ↔
      (j.val < r' ∧ i.val + j.val = 2 * r' + k) := by
    rw [lev_val, lev_val]
    exact ⟨fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩, fun ⟨h1, h2⟩ => ⟨by omega, by omega⟩⟩
  have e3 : (1 + r' ≤ (levPos k 1 r' i).val ∧ (levPos k 1 r' i).val ≤ 1 + r' + k ∧
      levPos k 1 r' i = levPos k 1 r' j) ↔ (r' ≤ i.val ∧ i.val ≤ r' + k ∧ i = j) := by
    rw [hij, lev_val]
    exact ⟨fun ⟨h1, h2, h3⟩ => ⟨by omega, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨by omega, by omega, h3⟩⟩
  have e4 : (levPos k 1 r' i).val = 1 + r' + k ↔ i.val = r' + k := by
    rw [lev_val]
    exact ⟨fun h => by omega, fun h => by omega⟩
  exact if_congr e1 rfl (if_congr e2 rfl (if_congr e3 (if_congr e4 rfl rfl) rfl))

lemma hermitian_matrix_mul_first (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : (Hpk k (1 + r') *ᵥ u) (i0 k r') = u (iL k r') := by
  simp [mulVec, dotProduct, hermitian_form_first_basis]

lemma Hmul_iL (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : (Hpk k (1 + r') *ᵥ u) (iL k r') = u (i0 k r') := by
  simp [mulVec, dotProduct, H_iL]

lemma Hmul_res (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    res k r' (Hpk k (1 + r') *ᵥ u) = Hpk k r' *ᵥ res k r' u := by
  funext j
  simp only [res, mulVec, dotProduct]
  rw [sum_split k r']
  simp [hermitian_levi_entry_zero, H_lev_iL, H_lev_lev]

lemma herm_split (k r' : ℕ) (u v : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u v =
      conj (v (i0 k r')) * u (iL k r') + herm (Hpk k r') (res k r' u) (res k r' v) + conj (v (iL k r')) * u (i0 k r') := by
  have hres : ∀ j, (Hpk k (1 + r') *ᵥ u) (levPos k 1 r' j) = (Hpk k r' *ᵥ res k r' u) j :=
    fun j => congrFun (Hmul_res k r' u) j
  simp only [herm, dotProduct]
  rw [sum_split k r']
  simp only [Pi.star_apply, hermitian_matrix_mul_first, Hmul_iL, hres, starRingEnd_apply, res]
  try ring

lemma last_ne_first_index (k r' : ℕ) : iL k r' ≠ i0 k r' := by
  intro h
  have := congrArg Fin.val h
  rw [iL_val, first_index_val] at this
  omega

lemma levi_position_ne_first (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : levPos k 1 r' j ≠ i0 k r' := by
  intro h
  have := congrArg Fin.val h
  rw [lev_val, first_index_val] at this
  omega

lemma lev_ne_iL (k r' : ℕ) (j : Fin (2 * r' + k + 1)) : levPos k 1 r' j ≠ iL k r' := by
  intro h
  have := congrArg Fin.val h
  rw [lev_val, iL_val] at this
  have := j.isLt
  omega

lemma e0_eq (k r' : ℕ) : e0 k r' = Pi.single (i0 k r') 1 := rfl

lemma dual_base_vector_eq_single (k r' : ℕ) : es0 k r' = Pi.single (iL k r') 1 := rfl

lemma base_vector_first_one (k r' : ℕ) : e0 k r' (i0 k r') = 1 := by
  rw [e0_eq, Pi.single_eq_same]

lemma base_vector_last_zero (k r' : ℕ) : e0 k r' (iL k r') = 0 := by
  rw [e0_eq, Pi.single_eq_of_ne (last_ne_first_index k r')]

lemma restriction_base_vector_zero (k r' : ℕ) : res k r' (e0 k r') = 0 := by
  funext j
  show e0 k r' (levPos k 1 r' j) = 0
  rw [e0_eq, Pi.single_eq_of_ne (levi_position_ne_first k r' j)]

lemma dual_base_vector_first_zero (k r' : ℕ) : es0 k r' (i0 k r') = 0 := by
  rw [dual_base_vector_eq_single, Pi.single_eq_of_ne (last_ne_first_index k r').symm]

lemma dual_base_vector_last_one (k r' : ℕ) : es0 k r' (iL k r') = 1 := by
  rw [dual_base_vector_eq_single, Pi.single_eq_same]

lemma restriction_dual_base_vector_zero (k r' : ℕ) : res k r' (es0 k r') = 0 := by
  funext j
  show es0 k r' (levPos k 1 r' j) = 0
  rw [dual_base_vector_eq_single, Pi.single_eq_of_ne (lev_ne_iL k r' j)]

lemma lifted_vector_first (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (i0 k r') = 0 := by
  simp only [liftVec]
  split_ifs with h
  · have := h.1
    rw [first_index_val] at this
    omega
  · rfl

lemma lift_iL (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : liftVec k 1 r' y (iL k r') = 0 := by
  simp only [liftVec]
  split_ifs with h
  · have := h.2
    rw [iL_val] at this
    omega
  · rfl

lemma res_lift (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) : res k r' (liftVec k 1 r' y) = y := by
  funext j
  show liftVec k 1 r' y (levPos k 1 r' j) = y j
  have hj := j.isLt
  simp only [liftVec]
  split_ifs with h
  · congr 1
  · exfalso
    apply h
    rw [lev_val]
    constructor <;> omega

lemma res_add (k r' : ℕ) (u v : Fin (2 * (1 + r') + k + 1) → ℂ) : res k r' (u + v) = res k r' u + res k r' v := rfl

lemma res_sub (k r' : ℕ) (u v : Fin (2 * (1 + r') + k + 1) → ℂ) : res k r' (u - v) = res k r' u - res k r' v := rfl

lemma res_smul (k r' : ℕ) (c : ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) : res k r' (c • u) = c • res k r' u := rfl

lemma lift_add (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) :
    liftVec k 1 r' (y + y') = liftVec k 1 r' y + liftVec k 1 r' y' := by
  funext p
  simp only [liftVec, Pi.add_apply]
  split_ifs <;> simp

lemma lift_zero (k r' : ℕ) : liftVec k 1 r' (0 : Fin (2 * r' + k + 1) → ℂ) = 0 := by
  funext p
  simp only [liftVec]
  split_ifs <;> rfl

lemma hermitian_first_basis_right (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (e0 k r') = u (iL k r') := by
  rw [herm_split, base_vector_first_one, base_vector_last_zero, restriction_base_vector_zero, herm_zero_right]
  simp

lemma herm_lift_right (k r' : ℕ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (y : Fin (2 * r' + k + 1) → ℂ) :
    herm (Hpk k (1 + r')) u (liftVec k 1 r' y) = herm (Hpk k r') (res k r' u) y := by
  rw [herm_split, lifted_vector_first, lift_iL, res_lift]
  simp

lemma herm_sum {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (u v : Fin m → ℂ) :
    ∑ j, herm H (bvec j) v * u j = herm H u v := by
  simp only [herm, bvec, dotProduct, mulVec, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.star_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma heis_act (k r' : ℕ) (v u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' v b *ᵥ u = u - herm (Hpk k (1 + r')) u v • e0 k r' + herm (Hpk k (1 + r')) u (e0 k r') • (v + b • e0 k r') := by
  have key : ∀ (w c : Fin (2 * (1 + r') + k + 1) → ℂ), vecMulVec w c *ᵥ u = (∑ j, c j * u j) • w := by
    intro w c
    funext i
    simp only [mulVec, dotProduct, vecMulVec, of_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_mul,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp only [heisG, sub_mulVec, add_mulVec, one_mulVec, key, herm_sum]

lemma heis_act' (k r' : ℕ) (y : Fin (2 * r' + k + 1) → ℂ) (u : Fin (2 * (1 + r') + k + 1) → ℂ) (b : ℂ) :
    heisG k r' (liftVec k 1 r' y) b *ᵥ u =
      u - herm (Hpk k r') (res k r' u) y • e0 k r' + u (iL k r') • (liftVec k 1 r' y + b • e0 k r') := by
  rw [heis_act, herm_lift_right, hermitian_first_basis_right]

lemma heisG_mul (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) (b b' : ℂ) :
    heisG k r' (liftVec k 1 r' y) b * heisG k r' (liftVec k 1 r' y') b' =
      heisG k r' (liftVec k 1 r' (y + y')) (b + b' - herm (Hpk k r') y' y) := by
  apply mat_ext
  intro w
  rw [← mulVec_mulVec, heis_act', heis_act', heis_act']
  have hL : (w - herm (Hpk k r') (res k r' w) y' • e0 k r' + w (iL k r') • (liftVec k 1 r' y' + b' • e0 k r'))
      (iL k r') = w (iL k r') := by
    simp [base_vector_last_zero, lift_iL]
  have hR : res k r' (w - herm (Hpk k r') (res k r' w) y' • e0 k r' +
      w (iL k r') • (liftVec k 1 r' y' + b' • e0 k r')) = res k r' w + w (iL k r') • y' := by
    simp only [res_add, res_sub, res_smul, restriction_base_vector_zero, res_lift, smul_zero, sub_zero, add_zero]
  rw [hL, hR, herm_add_left, herm_smul_left, herm_add_right, lift_add]
  funext p
  simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma heisG_zero (k r' : ℕ) : heisG k r' (liftVec k 1 r' 0) 0 = 1 := by
  apply mat_ext
  intro w
  rw [heis_act', lift_zero, herm_zero_right]
  simp

lemma Hherm (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [conjTranspose_apply, Hpk, Fin.ext_iff]
  split_ifs <;> first | omega | simp

lemma herm_self_im (k r : ℕ) (y : Fin (2 * r + k + 1) → ℂ) : (herm (Hpk k r) y y).im = 0 := by
  exact Complex.conj_eq_iff_im.mp (herm_conj _ (Hherm k r) y y)

lemma hb_add (k r' : ℕ) (y y' : Fin (2 * r' + k + 1) → ℂ) (s s' : ℝ) :
    hb k r' y s + hb k r' y' s' - herm (Hpk k r') y' y = hb k r' (y + y') (s + s' - (herm (Hpk k r') y' y).im) := by
  have h1 : herm (Hpk k r') (y + y') (y + y') =
      herm (Hpk k r') y y + herm (Hpk k r') y' y + (herm (Hpk k r') y y' + herm (Hpk k r') y' y') := by
    rw [herm_add_left, herm_add_right, herm_add_right]
    ring
  have h2 : (herm (Hpk k r') y y').re = (herm (Hpk k r') y' y).re := by
    rw [← herm_conj _ (Hherm k r') y' y, Complex.conj_re]
  simp only [hb]
  apply Complex.ext
  · simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, h1, h2]
    ring
  · simp only [Complex.add_im, Complex.sub_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_im]
    ring

theorem heisMul : HeisMul := by
  intro k r' x x'
  simp only [heis0]
  rw [heisG_mul, hb_add]

lemma heisenberg_at_zero (k r' : ℕ) : heis0 k r' (0, 0) = 1 := by
  have h : hb k r' 0 0 = 0 := by simp [hb, herm_zero_right]
  simp only [heis0, h]
  exact heisG_zero k r'

lemma heisenberg_mul_neg (k r' : ℕ) (x : HPar k r') : heis0 k r' x * heis0 k r' (-x.1, -x.2) = 1 := by
  rw [heisMul k r' x (-x.1, -x.2)]
  have h : (herm (Hpk k r') (-x.1) x.1).im = 0 := by
    rw [herm_neg_left, Complex.neg_im, herm_self_im, neg_zero]
  convert heisenberg_at_zero k r' using 2 <;> simp [h]

theorem heisInv : HeisInv := by
  intro k r' x
  exact Matrix.inv_eq_right_inv (heisenberg_mul_neg k r' x)

lemma herm_zero_left {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v : ι → ℂ) : herm H 0 v = 0 := by
  simp [herm]

lemma heis_col (k r' : ℕ) (x : HPar k r') (p : Fin (2 * (1 + r') + k + 1)) :
    heis0 k r' x p (iL k r') = (es0 k r' + (liftVec k 1 r' x.1 + hb k r' x.1 x.2 • e0 k r')) p := by
  have hcol : heis0 k r' x p (iL k r') = (heis0 k r' x *ᵥ es0 k r') p := by
    simp [dual_base_vector_eq_single, mulVec, dotProduct, Pi.single_apply]
  rw [hcol]
  simp only [heis0]
  rw [heis_act', restriction_dual_base_vector_zero, dual_base_vector_last_one, herm_zero_left]
  simp

def coord (k r' : ℕ) (g : Mat k (1 + r')) : HPar k r' :=
  (fun j => g (levPos k 1 r' j) (iL k r'), (g (i0 k r') (iL k r')).im)

lemma coord_heis (k r' : ℕ) (x : HPar k r') : coord k r' (heis0 k r' x) = x := by
  have h1 : ∀ j, es0 k r' (levPos k 1 r' j) = 0 := fun j => congrFun (restriction_dual_base_vector_zero k r') j
  have h2 : ∀ j, e0 k r' (levPos k 1 r' j) = 0 := fun j => congrFun (restriction_base_vector_zero k r') j
  have h3 : ∀ j, liftVec k 1 r' x.1 (levPos k 1 r' j) = x.1 j := fun j => congrFun (res_lift k r' x.1) j
  simp only [coord, heis_col]
  refine Prod.ext ?_ ?_
  · funext j
    simp [h1, h2, h3]
  · simp [dual_base_vector_first_zero, lifted_vector_first, base_vector_first_one, hb]

lemma continuous_coord (k r' : ℕ) : Continuous (coord k r') := by
  unfold coord
  first
  | fun_prop
  | exact Continuous.prodMk (continuous_pi fun j => (continuous_apply _).comp (continuous_apply _))
      (Complex.continuous_im.comp ((continuous_apply _).comp (continuous_apply _)))

lemma continuous_herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) :
    Continuous fun p : (ι → ℂ) × (ι → ℂ) => herm H p.1 p.2 := by
  simp only [herm, dotProduct, mulVec, Pi.star_apply]
  fun_prop

lemma continuous_lift (k r' : ℕ) : Continuous (liftVec k 1 r') := by
  apply continuous_pi
  intro p
  by_cases hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1
  · simp only [liftVec, dif_pos hp]
    exact continuous_apply _
  · simp only [liftVec, dif_neg hp]
    exact continuous_const

lemma continuous_hb (k r' : ℕ) : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := by
  have hc : Continuous fun x : HPar k r' => herm (Hpk k r') x.1 x.1 :=
    (continuous_herm (Hpk k r')).comp (continuous_fst.prodMk continuous_fst)
  simp only [hb]
  first
  | fun_prop
  | exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp hc).neg.div_const 2)).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

lemma continuous_heis0 (k r' : ℕ) : Continuous (heis0 k r') := by
  have hl : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (continuous_lift k r').comp continuous_fst
  have hh : ∀ j, Continuous fun x : HPar k r' => herm (Hpk k (1 + r')) (bvec j) (liftVec k 1 r' x.1) :=
    fun j => (continuous_herm _).comp (continuous_const.prodMk hl)
  have hl' : ∀ p, Continuous fun x : HPar k r' => liftVec k 1 r' x.1 p := fun p => (continuous_apply p).comp hl
  have hb' := continuous_hb k r'
  unfold heis0 heisG
  apply continuous_pi
  intro p
  apply continuous_pi
  intro q
  simp only [Matrix.add_apply, Matrix.sub_apply, vecMulVec, of_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

lemma Hset_eq (k r' : ℕ) : Hset k r' = {g | heis0 k r' (coord k r' g) = g} := by
  ext g
  constructor
  · intro hg
    obtain ⟨x, rfl⟩ := (show g ∈ Set.range (heis0 k r') from hg)
    show heis0 k r' (coord k r' (heis0 k r' x)) = heis0 k r' x
    rw [coord_heis]
  · intro h
    show g ∈ Set.range (heis0 k r')
    exact ⟨coord k r' g, h⟩

lemma isClosed_Hset (k r' : ℕ) : IsClosed (Hset k r') := by
  rw [Hset_eq]
  exact isClosed_eq ((continuous_heis0 k r').comp (continuous_coord k r')) continuous_id

theorem heisClosed : HeisClosed := by
  intro k r'
  refine ⟨fun x y h => ?_, ⟨?_, ?_, ?_, ?_, isClosed_Hset k r'⟩⟩
  · have := congrArg (coord k r') h
    rwa [coord_heis, coord_heis] at this
  · exact Set.mem_range.mpr ⟨(0, 0), heisenberg_at_zero k r'⟩
  · intro a ha b hb
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hb
    exact Set.mem_range.mpr ⟨_, (heisMul k r' x y).symm⟩
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    exact Set.mem_range.mpr ⟨_, (heisInv k r' x).symm⟩
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    exact Matrix.isUnit_det_of_right_inverse (heisenberg_mul_neg k r' x)

lemma levi_first_row (k r' : ℕ) (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (i0 k r') q = if i0 k r' = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg]
  all_goals first | rfl | omega | (simp only [first_index_val, iL_val, lev_val]; omega) | (rw [lev_val]; constructor <;> omega) | (simp_all [Fin.ext_iff] <;> omega)

lemma lev_row_iL (k r' : ℕ) (g : Mat k r') (q : Fin (2 * (1 + r') + k + 1)) :
    ιLev k 1 r' g (iL k r') q = if iL k r' = q then 1 else 0 := by
  simp only [ιLev]
  rw [dif_neg]
  all_goals first | rfl | omega | (simp only [first_index_val, iL_val, lev_val]; omega) | (rw [lev_val]; constructor <;> omega) | (simp_all [Fin.ext_iff] <;> omega)

lemma levi_entry_first_zero (k r' : ℕ) (g : Mat k r') (i : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (i0 k r') = 0 := by
  have hi := i.isLt
  simp only [ιLev]
  rw [dif_pos, dif_neg]
  all_goals first | rfl | omega | (simp only [first_index_val, iL_val, lev_val]; omega) | (rw [lev_val]; constructor <;> omega) | (simp_all [Fin.ext_iff] <;> omega)

lemma lev_lev_iL (k r' : ℕ) (g : Mat k r') (i : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (iL k r') = 0 := by
  have hi := i.isLt
  simp only [ιLev]
  rw [dif_pos, dif_neg]
  all_goals first | rfl | omega | (simp only [first_index_val, iL_val, lev_val]; omega) | (rw [lev_val]; constructor <;> omega) | (simp_all [Fin.ext_iff] <;> omega)

lemma lev_lev_lev (k r' : ℕ) (g : Mat k r') (i j : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' i) (levPos k 1 r' j) = g i j := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [ιLev]
  rw [dif_pos, dif_pos]
  all_goals first | rfl | omega | (simp only [first_index_val, iL_val, lev_val]; omega) | (rw [lev_val]; constructor <;> omega) | (simp_all [Fin.ext_iff] <;> omega)

lemma levi_action_first_coordinate (k r' : ℕ) (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (ιLev k 1 r' g *ᵥ u) (i0 k r') = u (i0 k r') := by
  simp [mulVec, dotProduct, levi_first_row]

lemma lev_act_iL (k r' : ℕ) (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    (ιLev k 1 r' g *ᵥ u) (iL k r') = u (iL k r') := by
  simp [mulVec, dotProduct, lev_row_iL]

lemma lev_act_res (k r' : ℕ) (g : Mat k r') (u : Fin (2 * (1 + r') + k + 1) → ℂ) :
    res k r' (ιLev k 1 r' g *ᵥ u) = g *ᵥ res k r' u := by
  funext j
  simp only [res, mulVec, dotProduct]
  rw [sum_split k r']
  simp [levi_entry_first_zero, lev_lev_iL, lev_lev_lev]

lemma lev_mul (k r' : ℕ) (g h : Mat k r') : ιLev k 1 r' g * ιLev k 1 r' h = ιLev k 1 r' (g * h) := by
  apply mat_ext
  intro u
  rw [← mulVec_mulVec]
  apply vec_ext
  · simp only [levi_action_first_coordinate]
  · simp only [lev_act_res]
    rw [mulVec_mulVec]
  · simp only [lev_act_iL]

lemma lev_one (k r' : ℕ) : ιLev k 1 r' (1 : Mat k r') = 1 := by
  apply mat_ext
  intro u
  rw [one_mulVec]
  apply vec_ext <;> simp [levi_action_first_coordinate, lev_act_res, lev_act_iL]

lemma levi_fixes_base_vector (k r' : ℕ) (g : Mat k r') : ιLev k 1 r' g *ᵥ e0 k r' = e0 k r' := by
  apply vec_ext <;> simp [levi_action_first_coordinate, lev_act_res, lev_act_iL, restriction_base_vector_zero]

lemma lev_lift (k r' : ℕ) (g : Mat k r') (y : Fin (2 * r' + k + 1) → ℂ) :
    ιLev k 1 r' g *ᵥ liftVec k 1 r' y = liftVec k 1 r' (g *ᵥ y) := by
  apply vec_ext <;> simp [levi_action_first_coordinate, lev_act_res, lev_act_iL, res_lift, lifted_vector_first, lift_iL]

lemma isUnit_det_Hpk (k r : ℕ) : IsUnit (Hpk k r).det := Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

lemma isUnit_det_GV {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : IsUnit g.det := by
  have hH := isUnit_det_Hpk k r
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h4 : (gᴴ.det * g.det) * (Hpk k r).det = 1 * (Hpk k r).det := by
    rw [one_mul]
    nth_rewrite 2 [← h2]
    ring
  have h3 := hH.mul_right_cancel h4
  exact ⟨⟨g.det, gᴴ.det, by rw [mul_comm]; exact h3, h3⟩, rfl⟩

lemma isUnit_det_lev {k r' : ℕ} {g : Mat k r'} (hg : IsUnit g.det) : IsUnit (ιLev k 1 r' g).det := by
  apply Matrix.isUnit_det_of_right_inverse (B := ιLev k 1 r' g⁻¹)
  rw [lev_mul, Matrix.mul_nonsing_inv _ hg, lev_one]

lemma lev_heisG (k r' : ℕ) {g : Mat k r'} (hg : g ∈ GV k r') (y : Fin (2 * r' + k + 1) → ℂ) (b : ℂ) :
    ιLev k 1 r' g * heisG k r' (liftVec k 1 r' y) b = heisG k r' (liftVec k 1 r' (g *ᵥ y)) b * ιLev k 1 r' g := by
  apply mat_ext
  intro u
  rw [← mulVec_mulVec, ← mulVec_mulVec, heis_act', heis_act', lev_act_res, lev_act_iL, herm_UH (H := Hpk k r') hg]
  simp only [mulVec_add, mulVec_sub, mulVec_smul, levi_fixes_base_vector, lev_lift]

theorem heisConjLev : HeisConjLev := by
  intro k r' g hg x
  have hu : IsUnit (ιLev k 1 r' g).det := isUnit_det_lev (isUnit_det_GV hg)
  have hb' : hb k r' (g *ᵥ x.1) x.2 = hb k r' x.1 x.2 := by
    simp only [hb, herm_UH (H := Hpk k r') hg]
  simp only [heis0]
  rw [lev_heisG k r' hg, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one, hb']

def heisT (k r' : ℕ) (x : HPar k r') : Mt k (1 + r') := heis0 k r' x

lemma continuous_heisT (k r' : ℕ) : Continuous (heisT k r') := continuous_heis0 k r'

lemma measurable_heisT (k r' : ℕ) : Measurable (heisT k r') := (continuous_heisT k r').measurable

lemma μHeis_eq (k r' : ℕ) : μHeis k r' = (volume : Measure (HPar k r')).map (heisT k r') := rfl

lemma map_μHeis (k r' : ℕ) {Φ : Mt k (1 + r') → Mt k (1 + r')} (hΦ : Measurable Φ) {T : HPar k r' → HPar k r'}
    (hT : MeasurePreserving T volume volume) (h : ∀ x, Φ (heisT k r' x) = heisT k r' (T x)) :
    (μHeis k r').map Φ = μHeis k r' := by
  rw [μHeis_eq, Measure.map_map hΦ (measurable_heisT k r')]
  have hc : Φ ∘ heisT k r' = heisT k r' ∘ T := funext h
  rw [hc, ← Measure.map_map (measurable_heisT k r') hT.measurable, hT.map_eq]

lemma measurable_lmulM {k r : ℕ} (a : Mat k r) : Measurable (lmulM a) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [lmulM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

lemma measurable_rmulF {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Measurable (rmulF a) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [rmulF, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

lemma measurable_conjM {k r : ℕ} (a : Mat k r) : Measurable (conjM a) := by
  apply Continuous.measurable
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [conjM, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

lemma shear (k r' : ℕ) {f : (Fin (2 * r' + k + 1) → ℂ) → (Fin (2 * r' + k + 1) → ℂ)}
    (hf : MeasurePreserving f volume volume) {c : (Fin (2 * r' + k + 1) → ℂ) → ℝ} (hc : Measurable c) :
    MeasurePreserving (fun p : HPar k r' => (f p.1, p.2 + c p.1)) volume volume := by
  exact hf.skew_product (g := fun y s => s + c y) (μc := volume) (μd := volume)
    (measurable_snd.add (hc.comp measurable_fst)) (ae_of_all _ fun y => map_add_right_eq_self volume (c y))

lemma measurable_herm_im_left (k r : ℕ) (y₀ : Fin (2 * r + k + 1) → ℂ) :
    Measurable fun y : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) y y₀).im := (Complex.continuous_im.comp ((continuous_herm _).comp (continuous_id.prodMk continuous_const))).measurable

lemma measurable_herm_im_right (k r : ℕ) (y₀ : Fin (2 * r + k + 1) → ℂ) :
    Measurable fun y : Fin (2 * r + k + 1) → ℂ => (herm (Hpk k r) y₀ y).im := (Complex.continuous_im.comp ((continuous_herm _).comp (continuous_const.prodMk continuous_id))).measurable

theorem heisHaar : HeisHaar := by
  intro k r'
  have hcl : @IsClosed (Mt k (1 + r')) _ (Hset k r') := isClosed_Hset k r'
  have hmeasU : @MeasurableSet (Mt k (1 + r')) _ (Hset k r')ᶜ := hcl.measurableSet.compl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [μHeis_eq]
    exact (Measure.map_apply (measurable_heisT k r') hmeasU).trans
      (measure_mono_null (fun x hx => hx (Set.mem_range.mpr ⟨x, rfl⟩)) measure_empty)
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    refine map_μHeis k r' (measurable_lmulM _)
      (shear k r' (measurePreserving_add_left volume x.1) ((measurable_herm_im_left k r' x.1).const_sub x.2)) ?_
    intro y
    show heis0 k r' x * heis0 k r' y = heis0 k r' (x.1 + y.1, y.2 + (x.2 - (herm (Hpk k r') y.1 x.1).im))
    rw [heisMul]
    congr 2
    ring
  · intro a ha
    obtain ⟨x, rfl⟩ := Set.mem_range.mp ha
    refine map_μHeis k r' (measurable_rmulF _)
      (shear k r' (measurePreserving_add_left volume x.1) ((measurable_herm_im_right k r' x.1).const_sub x.2)) ?_
    intro y
    show heis0 k r' y * heis0 k r' x = heis0 k r' (x.1 + y.1, y.2 + (x.2 - (herm (Hpk k r') x.1 y.1).im))
    rw [heisMul]
    congr 2 <;> first | ring | abel
  · intro K hK
    have hK' : IsCompact (coord k r' '' (K : Set (Mat k (1 + r')))) := hK.image (continuous_coord k r')
    rw [μHeis_eq, Measure.map_apply (measurable_heisT k r') hK.measurableSet]
    refine lt_of_le_of_lt (measure_mono ?_) hK'.measure_lt_top
    intro x hx
    exact ⟨heisT k r' x, hx, coord_heis k r' x⟩
  · rw [μHeis_eq]
    intro h
    rw [Measure.map_eq_zero_iff (measurable_heisT k r').aemeasurable] at h
    first
    | exact NeZero.ne _ h
    | exact (IsOpenPosMeasure.open_pos (μ := (volume : Measure (HPar k r'))) Set.univ isOpen_univ
        Set.univ_nonempty) (by rw [h]; rfl)

lemma normSq_det_GV {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) : Complex.normSq g.det = 1 := by
  have hH := isUnit_det_Hpk k r
  have h : gᴴ * Hpk k r * g = Hpk k r := hg
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h4 : (star g.det * g.det) * (Hpk k r).det = 1 * (Hpk k r).det := by
    rw [one_mul]
    nth_rewrite 2 [← h2]
    ring
  have h3 := hH.mul_right_cancel h4
  have h5 : ((Complex.normSq g.det : ℝ) : ℂ) = 1 := by
    rw [Complex.normSq_eq_conj_mul_self]
    exact h3
  exact_mod_cast h5

lemma measurePreserving_GV {k r : ℕ} {g : Mat k r} (hg : g ∈ GV k r) :
    MeasurePreserving (fun y : Fin (2 * r + k + 1) → ℂ => g *ᵥ y) volume volume := by
  have hn := normSq_det_GV hg
  set f : (Fin (2 * r + k + 1) → ℂ) →ₗ[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
    (Matrix.toLin' g).restrictScalars ℝ with hf
  have hfg : (fun y : Fin (2 * r + k + 1) → ℂ => g *ᵥ y) = f := by
    funext y
    simp [hf, Matrix.toLin'_apply]
  have hd : LinearMap.det f = 1 := by
    rw [hf, LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply, hn]
  rw [hfg]
  refine ⟨f.continuous_of_finiteDimensional.measurable, ?_⟩
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume (by rw [hd]; norm_num), hd]
  simp

theorem heisConjLevMeas : HeisConjLevMeas := by
  intro k r' g hg
  refine map_μHeis k r' (measurable_conjM _)
    (shear k r' (c := fun _ => (0 : ℝ)) (measurePreserving_GV hg) measurable_const) ?_
  intro y
  show ιLev k 1 r' g * heis0 k r' y * (ιLev k 1 r' g)⁻¹ = heis0 k r' (g *ᵥ y.1, y.2 + 0)
  rw [heisConjLev k r' g hg y, add_zero]

end Formalism.FourierDecayAlt.P.B2x5

namespace Formalism.FourierDecayAlt.P

theorem heisMul_statement : Formalism.FourierDecayAlt.B2.HeisMul := B2x5.heisMul

theorem heisenberg_inverse : Formalism.FourierDecayAlt.B2.HeisInv := B2x5.heisInv

theorem heisenberg_subgroup_closed : Formalism.FourierDecayAlt.B2.HeisClosed := B2x5.heisClosed

theorem heisenberg_haar_measure : Formalism.FourierDecayAlt.B2.HeisHaar := B2x5.heisHaar

theorem heisenberg_conjugation_by_levi : Formalism.FourierDecayAlt.B2.HeisConjLev := B2x5.heisConjLev

theorem heisenberg_levi_conjugation_measure : Formalism.FourierDecayAlt.B2.HeisConjLevMeas := B2x5.heisConjLevMeas

end Formalism.FourierDecayAlt.P
