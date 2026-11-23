import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.FormalDegreeBessel.FinalG
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ConjugationContinuousOnInvertible
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RankOneEmbeddings

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal

noncomputable section

namespace Formalism.FourierDecayAlt.P.TwoByOneBlock

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

section PartA

variable {k r : ℕ}

def jV (k r : ℕ) (u : Fin (k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := fun i =>
  if h : r ≤ i.val ∧ i.val ≤ r + k then u ⟨i.val - r, by omega⟩ else 0

abbrev mid (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ mid k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hj h.2)]
  by_cases h : q = j
  · subst h; rw [if_pos ⟨rfl, hj⟩, if_pos rfl]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ mid k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  unfold embWb
  rw [dif_neg (fun h => hq h.1)]
  by_cases h : q = j
  · rw [if_pos ⟨h, hq⟩, if_pos h]
  · rw [if_neg (fun h' => h h'.1), if_neg h]

lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : mid k r q) (hj : mid k r j) :
    embWb k r μ q j = μ ⟨q.val - r, by have := hq; omega⟩ ⟨j.val - r, by have := hj; omega⟩ := by
  unfold embWb
  rw [dif_pos ⟨hq, hj⟩]

lemma bc_mid_col (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) (hj : mid k r j) :
    bigCell k r c μ i j = if hi : mid k r i then μ ⟨i.val - r, by have := hi; omega⟩ ⟨j.val - r, by have := hj; omega⟩
      else 0 := by
  unfold bigCell
  rw [dif_neg (show ¬ j.val < r by have := hj; omega), dif_pos hj.2]

lemma bc_mid_row_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : mid k r i) (hj : ¬ mid k r j) : bigCell k r c μ i j = 0 := by
  have h1 := hi
  have hjl := j.isLt
  unfold bigCell
  by_cases hj1 : j.val < r
  · rw [dif_pos hj1, if_neg (by simp only [Fin.ext_iff, esI]; omega)]
  · rw [dif_neg hj1, dif_neg (show ¬ j.val ≤ r + k by omega), if_neg (by omega)]

lemma bc_out_col (c : Fin r → ℂ) (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hj : ¬ mid k r j) : bigCell k r c μ i j = bigCell k r c ν i j := by
  unfold bigCell
  by_cases hj1 : j.val < r
  · rw [dif_pos hj1, dif_pos hj1]
  · rw [dif_neg hj1, dif_neg hj1, dif_neg (show ¬ j.val ≤ r + k by omega), dif_neg (show ¬ j.val ≤ r + k by omega)]

lemma bc_out_row (c : Fin r → ℂ) (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : ¬ mid k r i) : bigCell k r c μ i j = bigCell k r c ν i j := by
  by_cases hj : mid k r j
  · rw [bc_mid_col c μ i j hj, bc_mid_col c ν i j hj, dif_neg hi, dif_neg hi]
  · exact bc_out_col c μ ν i j hj

lemma bc_one_mid (c : Fin r → ℂ) (i j : Fin (2 * r + k + 1)) (hi : mid k r i) (hj : mid k r j) :
    bigCell k r c 1 i j = if i = j then 1 else 0 := by
  rw [bc_mid_col c 1 i j hj, dif_pos hi, Matrix.one_apply]
  have h1 := hi
  have h2 := hj
  simp only [Fin.ext_iff]
  by_cases h : i.val = j.val
  · rw [if_pos (by omega), if_pos h]
  · rw [if_neg (by omega), if_neg h]

theorem bigCellFactor : BigCellFactor := by
  intro k r c μ
  constructor
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hj : mid k r j
    · by_cases hi : mid k r i
      · rw [Finset.sum_eq_single i]
        · rw [bc_one_mid c i i hi hi, if_pos rfl, one_mul, emb_mid μ i j hi hj, bc_mid_col c μ i j hj, dif_pos hi]
        · intro q _ hq
          by_cases hqm : mid k r q
          · rw [bc_one_mid c i q hi hqm, if_neg (fun h => hq h.symm), zero_mul]
          · rw [bc_mid_row_out c 1 i q hi hqm, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [bc_mid_col c μ i j hj, dif_neg hi]
        symm
        apply Finset.sum_eq_zero
        intro q _
        by_cases hqm : mid k r q
        · rw [bc_mid_col c 1 i q hqm, dif_neg hi, zero_mul]
        · rw [emb_out_row μ q j hqm, if_neg (show ¬ (q = j) from fun h => hqm (h ▸ hj)), mul_zero]
    · rw [Finset.sum_eq_single j]
      · rw [emb_out_col μ j j hj, if_pos rfl, mul_one]
        exact bc_out_col c μ 1 i j hj
      · intro q _ hq
        rw [emb_out_col μ q j hj, if_neg hq, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hi : mid k r i
    · by_cases hj : mid k r j
      · rw [Finset.sum_eq_single j]
        · rw [bc_one_mid c j j hj hj, if_pos rfl, mul_one, emb_mid μ i j hi hj, bc_mid_col c μ i j hj, dif_pos hi]
        · intro q _ hq
          by_cases hqm : mid k r q
          · rw [bc_one_mid c q j hqm hj, if_neg hq, mul_zero]
          · rw [emb_out_col μ i q hqm, if_neg (show ¬ (i = q) from fun h => hqm (h ▸ hi)), zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · rw [bc_mid_row_out c μ i j hi hj]
        symm
        apply Finset.sum_eq_zero
        intro q _
        by_cases hqm : mid k r q
        · rw [bc_mid_row_out c 1 q j hqm hj, mul_zero]
        · rw [emb_out_col μ i q hqm, if_neg (show ¬ (i = q) from fun h => hqm (h ▸ hi)), zero_mul]
    · rw [Finset.sum_eq_single i]
      · rw [emb_out_row μ i i hi, if_pos rfl, one_mul]
        exact bc_out_row c μ 1 i j hi
      · intro q _ hq
        rw [emb_out_row μ i q hi, if_neg (fun h => hq h.symm), zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h

lemma mid_wI (a : Fin (k + 1)) : mid k r (wI k r a) := by
  have := a.isLt
  constructor <;> simp only [wI] <;> omega

lemma mid_exists {i : Fin (2 * r + k + 1)} (hi : mid k r i) : ∃ a : Fin (k + 1), i = wI k r a :=
  ⟨⟨i.val - r, by have := hi; omega⟩, by apply Fin.ext; simp only [wI]; have := hi; omega⟩

lemma wI_inj : Function.Injective (wI k r) := by
  intro a b h
  have := congrArg Fin.val h
  simp only [wI] at this
  exact Fin.ext (by omega)

lemma sum_mid (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ i, ¬ mid k r i → f i = 0) :
    ∑ i, f i = ∑ a : Fin (k + 1), f (wI k r a) := by
  symm
  apply Finset.sum_of_injOn (wI k r) (wI_inj.injOn) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  · intro i _ hi
    apply hf
    intro hm
    obtain ⟨a, rfl⟩ := mid_exists hm
    exact hi ⟨a, Finset.mem_coe.2 (Finset.mem_univ _), rfl⟩
  · intro i _; rfl

lemma emb_wI (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a b : Fin (k + 1)) :
    embWb k r μ (wI k r a) (wI k r b) = μ a b := by
  rw [emb_mid μ _ _ (mid_wI a) (mid_wI b)]
  congr 1 <;> (apply Fin.ext; simp [wI])

lemma jV_wI (u : Fin (k + 1) → ℂ) (a : Fin (k + 1)) : jV k r u (wI k r a) = u a := by
  unfold jV
  rw [dif_pos (mid_wI a)]
  congr 1
  apply Fin.ext
  simp [wI]

lemma jV_out (u : Fin (k + 1) → ℂ) {i : Fin (2 * r + k + 1)} (hi : ¬ mid k r i) : jV k r u i = 0 := by
  unfold jV
  rw [dif_neg hi]

lemma mul_emb_out (M : Mat k r) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hj : ¬ mid k r j) : (M * embWb k r μ) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [emb_out_col μ j j hj, if_pos rfl, mul_one]
  · intro q _ hq; rw [emb_out_col μ q j hj, if_neg hq, mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma mul_emb_mid (M : Mat k r) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1))
    (b : Fin (k + 1)) : (M * embWb k r μ) i (wI k r b) = ∑ c, M i (wI k r c) * μ c b := by
  rw [Matrix.mul_apply, sum_mid]
  · simp only [emb_wI]
  · intro q hq
    rw [emb_out_row μ q _ hq, if_neg (show ¬ (q = wI k r b) from fun h => hq (h ▸ mid_wI b)), mul_zero]

lemma emb_mul_out (M : Mat k r) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : ¬ mid k r i) : (embWb k r μ * M) i j = M i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · rw [emb_out_row μ i i hi, if_pos rfl, one_mul]
  · intro q _ hq; rw [emb_out_row μ i q hi, if_neg (fun h => hq h.symm), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

lemma emb_mul_mid (M : Mat k r) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a : Fin (k + 1))
    (j : Fin (2 * r + k + 1)) : (embWb k r μ * M) (wI k r a) j = ∑ c, μ a c * M (wI k r c) j := by
  rw [Matrix.mul_apply, sum_mid]
  · simp only [emb_wI]
  · intro q hq
    rw [emb_out_col μ _ q hq, if_neg (show ¬ (wI k r a = q) from fun h => hq (h ▸ mid_wI a)), zero_mul]

lemma wbPart_jV (u : Fin (k + 1) → ℂ) : wbPart k r (jV k r u) = u := by
  funext a
  exact jV_wI u a

lemma jV_wbPart {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) : jV k r (wbPart k r v) = v := by
  funext i
  by_cases hi : mid k r i
  · obtain ⟨a, rfl⟩ := mid_exists hi
    rw [jV_wI]; rfl
  · rw [jV_out _ hi, hv i (by have := hi; omega)]

lemma inWb_jV (u : Fin (k + 1) → ℂ) : inWb k r (jV k r u) := by
  intro i hi
  exact jV_out u (by omega)

lemma emb_mulVec_jV (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (u : Fin (k + 1) → ℂ) :
    embWb k r μ *ᵥ jV k r u = jV k r (μ *ᵥ u) := by
  funext i
  show ∑ j, embWb k r μ i j * jV k r u j = _
  rw [sum_mid _ (fun j hj => by rw [jV_out u hj, mul_zero])]
  by_cases hi : mid k r i
  · obtain ⟨a, rfl⟩ := mid_exists hi
    simp only [emb_wI, jV_wI]
    rfl
  · rw [jV_out _ hi]
    apply Finset.sum_eq_zero
    intro b _
    rw [emb_out_row μ i _ hi, if_neg (show ¬ (i = wI k r b) from fun h => hi (h ▸ mid_wI b)), zero_mul]

lemma Hpk_wI (a b : Fin (k + 1)) : Hpk k r (wI k r a) (wI k r b) = Hb k a b := by
  rw [GBasic.Hpk_eq, GBasic.sig_mid _ _ _ (mid_wI a).1 (mid_wI a).2]
  unfold Hb
  rw [Matrix.diagonal_apply]
  by_cases h : a = b
  · subst h
    rw [if_pos rfl, if_pos rfl]
    simp [GBasic.sgn, wI, Fin.ext_iff]
  · rw [if_neg h, if_neg (fun h' => h (wI_inj h').symm)]

lemma Hpk_mid_out {i j : Fin (2 * r + k + 1)} (hi : mid k r i) (hj : ¬ mid k r j) : Hpk k r i j = 0 := by
  rw [GBasic.Hpk_eq, GBasic.sig_mid _ _ _ hi.1 hi.2, if_neg (show ¬ (j = i) from fun h => hj (h ▸ hi))]

lemma sig_out {i : Fin (2 * r + k + 1)} (hi : ¬ mid k r i) : ¬ mid k r (GBasic.sig k r i) := by
  have h := GBasic.sig_val k r i
  have hl := i.isLt
  rw [if_pos (by omega)] at h
  intro hm
  have := hm
  omega

lemma Hpk_out_mid {i j : Fin (2 * r + k + 1)} (hi : ¬ mid k r i) (hj : mid k r j) : Hpk k r i j = 0 := by
  rw [GBasic.Hpk_eq, if_neg (show ¬ (j = GBasic.sig k r i) from fun h => sig_out hi (h ▸ hj))]

lemma herm_jV (u u' : Fin (k + 1) → ℂ) : herm (Hpk k r) (jV k r u) (jV k r u') = herm (Hb k) u u' := by
  show ∑ i, star (jV k r u') i * ∑ j, Hpk k r i j * jV k r u j = ∑ a, star u' a * ∑ b, Hb k a b * u b
  rw [sum_mid _ (fun i hi => by rw [Pi.star_apply, jV_out u' hi, star_zero, zero_mul])]
  apply Finset.sum_congr rfl
  intro a _
  rw [sum_mid _ (fun j hj => by rw [jV_out u hj, mul_zero])]
  simp only [Pi.star_apply, jV_wI, Hpk_wI]

lemma emb_mul (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : embWb k r (a * b) = embWb k r a * embWb k r b := by
  ext i j
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · obtain ⟨x, rfl⟩ := mid_exists hi
      obtain ⟨y, rfl⟩ := mid_exists hj
      rw [mul_emb_mid, emb_wI, Matrix.mul_apply]
      simp only [emb_wI]
    · rw [mul_emb_out _ _ _ _ hj, emb_out_col _ _ _ hj, emb_out_col _ _ _ hj]
  · rw [emb_mul_out _ _ _ _ hi, emb_out_row _ _ _ hi, emb_out_row _ _ _ hi]

lemma emb_one : embWb k r 1 = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · obtain ⟨x, rfl⟩ := mid_exists hi
      obtain ⟨y, rfl⟩ := mid_exists hj
      rw [emb_wI, Matrix.one_apply]
      simp only [wI_inj.eq_iff]
    · rw [emb_out_col _ _ _ hj]
  · rw [emb_out_row _ _ _ hi]

lemma Hb_herm : (Hb k)ᴴ = Hb k := by
  unfold Hb
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext j
  simp only [Pi.star_apply]
  split_ifs <;> simp

lemma Hb_sq : Hb k * Hb k = 1 := by
  unfold Hb
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext j
  split_ifs <;> simp

lemma Hb_unit : IsUnit (Hb k).det := by
  have h := congrArg Matrix.det (Hb_sq (k := k))
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

lemma UHb_mul {a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : a ∈ UH (Hb k)) (hb : b ∈ UH (Hb k)) :
    a * b ∈ UH (Hb k) :=
  (uHGroup (k + 1) (Hb k) Hb_unit).2.1 a ha b hb

lemma UHb_inv {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : a ∈ UH (Hb k)) :
    IsUnit a.det ∧ a⁻¹ ∈ UH (Hb k) :=
  (uHGroup (k + 1) (Hb k) Hb_unit).2.2 a ha

lemma UHb_det {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : a ∈ UH (Hb k)) : ‖a.det‖ = 1 := by
  have h : aᴴ * Hb k * a = Hb k := ha
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose] at h2
  have h0 : (Hb k).det ≠ 0 := Hb_unit.ne_zero
  have h3 : star a.det * a.det = 1 := by
    have : (star a.det * a.det) * (Hb k).det = 1 * (Hb k).det := by
      rw [one_mul]
      calc (star a.det * a.det) * (Hb k).det = star a.det * (Hb k).det * a.det := by ring
        _ = (Hb k).det := h2
    exact mul_right_cancel₀ h0 this
  have h4 : ‖a.det‖ * ‖a.det‖ = 1 := by
    have := congrArg norm h3
    rwa [norm_mul, norm_star, norm_one] at this
  nlinarith [norm_nonneg a.det]

lemma emb_inv {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) :
    (embWb k r μ)⁻¹ = embWb k r μ⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← emb_mul, Matrix.mul_nonsing_inv _ (UHb_inv hμ).1, emb_one]

lemma emb_conjTranspose (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : (embWb k r μ)ᴴ = embWb k r μᴴ := by
  ext i j
  rw [Matrix.conjTranspose_apply]
  by_cases hi : mid k r i
  · by_cases hj : mid k r j
    · obtain ⟨x, rfl⟩ := mid_exists hi
      obtain ⟨y, rfl⟩ := mid_exists hj
      rw [emb_wI, emb_wI, Matrix.conjTranspose_apply]
    · rw [emb_out_row _ _ _ hj, emb_out_col _ _ _ hj]
      by_cases h : i = j
      · rw [if_pos h.symm, if_pos h, star_one]
      · rw [if_neg (fun h' => h h'.symm), if_neg h, star_zero]
  · rw [emb_out_col _ _ _ hi, emb_out_row _ _ _ hi]
    by_cases h : i = j
    · rw [if_pos h.symm, if_pos h, star_one]
    · rw [if_neg (fun h' => h h'.symm), if_neg h, star_zero]

lemma emb_form_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (a b : Fin (k + 1)) :
    ((embWb k r μ)ᴴ * Hpk k r * embWb k r μ) (wI k r a) (wI k r b) = (μᴴ * Hb k * μ) a b := by
  rw [emb_conjTranspose, mul_emb_mid, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro c _
  rw [emb_mul_mid, Matrix.mul_apply]
  simp only [Hpk_wI]

lemma emb_form (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    embWb k r μ ∈ GV k r ↔ μ ∈ UH (Hb k) := by
  constructor
  · intro h
    have h' : (embWb k r μ)ᴴ * Hpk k r * embWb k r μ = Hpk k r := h
    show μᴴ * Hb k * μ = Hb k
    ext a b
    rw [← emb_form_mid (r := r), h', Hpk_wI]
  · intro h
    have h' : μᴴ * Hb k * μ = Hb k := h
    show (embWb k r μ)ᴴ * Hpk k r * embWb k r μ = Hpk k r
    ext i j
    by_cases hi : mid k r i
    · by_cases hj : mid k r j
      · obtain ⟨x, rfl⟩ := mid_exists hi
        obtain ⟨y, rfl⟩ := mid_exists hj
        rw [emb_form_mid, h', Hpk_wI]
      · obtain ⟨x, rfl⟩ := mid_exists hi
        rw [mul_emb_out _ _ _ _ hj, emb_conjTranspose, emb_mul_mid, Hpk_mid_out hi hj]
        apply Finset.sum_eq_zero
        intro c _
        rw [Hpk_mid_out (mid_wI c) hj, mul_zero]
    · by_cases hj : mid k r j
      · obtain ⟨y, rfl⟩ := mid_exists hj
        rw [mul_emb_mid, Hpk_out_mid hi hj]
        apply Finset.sum_eq_zero
        intro c _
        rw [emb_conjTranspose, emb_mul_out _ _ _ _ hi, Hpk_out_mid hi (mid_wI c), zero_mul]
      · rw [mul_emb_out _ _ _ _ hj, emb_conjTranspose, emb_mul_out _ _ _ _ hi]

lemma emb_fix_out (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) {j : Fin (2 * r + k + 1)} (hj : ¬ mid k r j) :
    embWb k r μ *ᵥ bvec j = bvec j := by
  funext i
  unfold bvec
  rw [Matrix.mulVec_single_one]
  show embWb k r μ i j = _
  rw [emb_out_col _ _ _ hj, Pi.single_apply]

lemma eI_out (a : Fin r) : ¬ mid k r (eI k r a) := by
  have := a.isLt
  intro h
  have h1 := h.1
  simp only [eI] at h1
  omega

lemma esI_out (a : Fin r) : ¬ mid k r (esI k r a) := by
  have := a.isLt
  intro h
  have h1 := h.2
  simp only [esI] at h1
  omega

lemma emb_mem_UWb {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) : embWb k r μ ∈ UWb k r :=
  ⟨(emb_form μ).2 hμ, fun a => ⟨emb_fix_out μ (eI_out a), emb_fix_out μ (esI_out a)⟩⟩

lemma UWb_iff (g : Mat k r) : g ∈ UWb k r ↔ ∃ μ ∈ UH (Hb k), g = embWb k r μ := by
  constructor
  · rintro ⟨hg, hfix⟩
    have hcol : ∀ i j, ¬ mid k r j → g i j = if i = j then 1 else 0 := by
      intro i j hj
      have hjl := j.isLt
      have key : g *ᵥ bvec j = bvec j := by
        by_cases h1 : j.val < r
        · have e : eI k r ⟨j.val, h1⟩ = j := Fin.ext rfl
          have := (hfix ⟨j.val, h1⟩).1
          rwa [e] at this
        · have h2 : r + k < j.val := by
            by_contra h2
            exact hj ⟨by omega, by omega⟩
          have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := Fin.ext (by simp only [esI]; omega)
          have := (hfix ⟨2 * r + k - j.val, by omega⟩).2
          rwa [e] at this
      have := congrFun key i
      unfold bvec at this
      rw [Matrix.mulVec_single_one, Pi.single_apply] at this
      exact this
    have hrow : ∀ i j, ¬ mid k r i → mid k r j → g i j = 0 := by
      intro i j hi hj
      have hp := sig_out hi
      have h : (gᴴ * Hpk k r * g) (GBasic.sig k r i) j = Hpk k r (GBasic.sig k r i) j := by
        have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
        rw [hg']
      rw [Hpk_out_mid hp hj, Matrix.mul_apply] at h
      have h1 : ∀ b, (gᴴ * Hpk k r) (GBasic.sig k r i) b = Hpk k r (GBasic.sig k r i) b := by
        intro b
        rw [Matrix.mul_apply, Finset.sum_eq_single (GBasic.sig k r i)]
        · rw [Matrix.conjTranspose_apply, hcol _ _ hp, if_pos rfl, star_one, one_mul]
        · intro q _ hq
          rw [Matrix.conjTranspose_apply, hcol _ _ hp, if_neg hq, star_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      simp only [h1] at h
      rw [Finset.sum_eq_single i] at h
      · rw [GBasic.Hpk_eq, GBasic.sig_sig, if_pos rfl] at h
        have hs : GBasic.sgn k r (GBasic.sig k r i) ≠ 0 := by
          unfold GBasic.sgn
          split_ifs <;> simp
        exact (mul_eq_zero.1 h).resolve_left hs
      · intro q _ hq
        rw [GBasic.Hpk_eq, GBasic.sig_sig, if_neg hq, zero_mul]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hge : g = embWb k r (Matrix.of fun a b => g (wI k r a) (wI k r b)) := by
      ext i j
      by_cases hj : mid k r j
      · by_cases hi : mid k r i
        · obtain ⟨x, rfl⟩ := mid_exists hi
          obtain ⟨y, rfl⟩ := mid_exists hj
          rw [emb_wI, Matrix.of_apply]
        · rw [hrow i j hi hj, emb_out_row _ _ _ hi, if_neg (show ¬ (i = j) from fun h => hi (h ▸ hj))]
      · rw [hcol i j hj, emb_out_col _ _ _ hj]
    refine ⟨_, ?_, hge⟩
    rw [← emb_form (r := r), ← hge]
    exact hg
  · rintro ⟨μ, hμ, rfl⟩
    exact emb_mem_UWb hμ

lemma UWset_iff {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : Mat k r) :
    g ∈ UWset k r z ↔ ∃ μ ∈ UH (Hb k), μ *ᵥ wbPart k r z = wbPart k r z ∧ g = embWb k r μ := by
  constructor
  · rintro ⟨hg, hfix, hgz⟩
    obtain ⟨μ, hμ, rfl⟩ := (UWb_iff g).1 ⟨hg, hfix⟩
    refine ⟨μ, hμ, ?_, rfl⟩
    rw [← jV_wbPart hz, emb_mulVec_jV] at hgz
    have := congrArg (wbPart k r) hgz
    rwa [wbPart_jV, wbPart_jV] at this
  · rintro ⟨μ, hμ, hfz, rfl⟩
    obtain ⟨h1, h2⟩ := emb_mem_UWb (r := r) hμ
    refine ⟨h1, h2, ?_⟩
    rw [← jV_wbPart hz, emb_mulVec_jV, hfz]

theorem uWbFacts : UWbFacts := by
  intro k r
  refine ⟨?_, ?_, ?_⟩
  · ext g
    rw [UWb_iff]
    constructor
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨μ, hμ, rfl⟩
    · rintro ⟨μ, hμ, rfl⟩
      exact ⟨μ, hμ, rfl⟩
  · rintro z g ⟨hg, hfix, _⟩
    exact ⟨hg, hfix⟩
  · intro c m hm
    obtain ⟨μ, _, rfl⟩ := (UWb_iff m).1 hm
    rw [← (bigCellFactor k r c μ).1, ← (bigCellFactor k r c μ).2]

theorem weightFactor : WeightFactor := by
  intro k r T T' q
  unfold bcWeight cWeight zWeight
  split_ifs <;> simp

end PartA

section PartB

section Herm

variable {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ)

lemma herm_add_left (x y w : Fin m → ℂ) : herm H (x + y) w = herm H x w + herm H y w := by
  simp [herm, mulVec_add, dotProduct_add]

lemma herm_smul_left (c : ℂ) (x w : Fin m → ℂ) : herm H (c • x) w = c * herm H x w := by
  simp [herm, mulVec_smul, dotProduct_smul]

lemma herm_add_right (x w w' : Fin m → ℂ) : herm H x (w + w') = herm H x w + herm H x w' := by
  simp [herm, add_dotProduct]

lemma herm_smul_right (c : ℂ) (x w : Fin m → ℂ) : herm H x (c • w) = star c * herm H x w := by
  simp [herm, smul_dotProduct]

lemma herm_symm (hH : Hᴴ = H) (x y : Fin m → ℂ) : herm H y x = star (herm H x y) := by
  unfold herm
  rw [← Matrix.star_dotProduct, Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec]

lemma herm_self_real (hH : Hᴴ = H) (x : Fin m → ℂ) : herm H x x = ((herm H x x).re : ℂ) := by
  have h := herm_symm H hH x x
  apply Complex.ext
  · simp
  · have h2 := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at h2
    simp only [Complex.ofReal_im]
    linarith

end Herm

theorem herm_UH {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (x y : Fin m → ℂ) :
    herm H (g *ᵥ x) (g *ᵥ y) = herm H x y := by
  have hg' : gᴴ * H * g = H := hg
  unfold herm
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg']

theorem mem_UH_of_herm {m : ℕ} {H g : Matrix (Fin m) (Fin m) ℂ}
    (h : ∀ x y : Fin m → ℂ, herm H (g *ᵥ x) (g *ᵥ y) = herm H x y) : g ∈ UH H := by
  show gᴴ * H * g = H
  ext i j
  have h1 := h (Pi.single j 1) (Pi.single i 1)
  unfold herm at h1
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at h1
  simpa [Pi.star_single] using h1

def qrefl {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (c : ℂ) : Matrix (Fin m) (Fin m) ℂ :=
  1 + c • Matrix.vecMulVec d (star d ᵥ* H)

lemma qrefl_mulVec {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (d : Fin m → ℂ) (c : ℂ) (x : Fin m → ℂ) :
    qrefl H d c *ᵥ x = x + (c * herm H x d) • d := by
  have h1 : Matrix.vecMulVec d (star d ᵥ* H) *ᵥ x = herm H x d • d := by
    unfold herm
    rw [Matrix.dotProduct_mulVec]
    ext i
    simp only [Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold qrefl
  rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, h1, smul_smul]

lemma qrefl_mem {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) (d : Fin m → ℂ) (c : ℂ)
    (hc : c + star c + c * star c * herm H d d = 0) : qrefl H d c ∈ UH H := by
  apply mem_UH_of_herm
  intro x y
  rw [qrefl_mulVec, qrefl_mulVec]
  simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_mul]
  rw [herm_symm H hH y d]
  linear_combination (herm H x d * star (herm H y d)) * hc

lemma exists_phase (s : ℂ) (q : ℝ) : ∃ θ : ℂ, θ * star θ = 1 ∧ ∃ t : ℝ, star θ * s = t ∧ q * t ≤ 0 := by
  by_cases hs : s = 0
  · exact ⟨1, by simp, 0, by simp [hs], by simp⟩
  have hn : (‖s‖ : ℂ) ≠ 0 := by
    simpa using hs
  have hss : star s * s = (‖s‖ : ℂ) ^ 2 := by
    rw [Complex.star_def]; exact Complex.conj_mul' s
  have hss' : s * star s = (‖s‖ : ℂ) ^ 2 := by rw [mul_comm]; exact hss
  have hst : star ((‖s‖ : ℂ)) = (‖s‖ : ℂ) := by simp
  rcases le_total 0 q with hq | hq
  · refine ⟨-(s / ‖s‖), ?_, -‖s‖, ?_, ?_⟩
    · rw [star_neg, star_div₀, hst]
      field_simp
      linear_combination hss'
    · rw [star_neg, star_div₀, hst]
      push_cast
      field_simp
      linear_combination -hss
    · have := norm_nonneg s
      nlinarith
  · refine ⟨s / ‖s‖, ?_, ‖s‖, ?_, ?_⟩
    · rw [star_div₀, hst]
      field_simp
      linear_combination hss'
    · rw [star_div₀, hst]
      field_simp
      linear_combination hss
    · have := norm_nonneg s
      nlinarith

theorem UH_mul {m : ℕ} {H g h : Matrix (Fin m) (Fin m) ℂ} (hg : g ∈ UH H) (hh : h ∈ UH H) : g * h ∈ UH H := by
  apply mem_UH_of_herm
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, herm_UH hg, herm_UH hh]

theorem trans {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) (a b : Fin m → ℂ) (q : ℝ) (hq : q ≠ 0)
    (ha : herm H a a = q) (hb : herm H b b = q) :
    ∃ g ∈ UH H, g *ᵥ a = b ∧ ∀ x, herm H x a = 0 → herm H x b = 0 → g *ᵥ x = x := by
  obtain ⟨θ, hθ, t, ht, hqt⟩ := exists_phase (herm H a b) q
  have hqd : (q : ℝ) - t ≠ 0 := by
    intro h
    have : q * q ≤ 0 := by
      have : t = q := by linarith
      rw [this] at hqt; exact hqt
    have h2 : 0 < q * q := mul_self_pos.2 hq
    linarith
  have hqdC : (q : ℂ) - t ≠ 0 := by exact_mod_cast hqd
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hba : herm H b a = star (herm H a b) := herm_symm H hH a b
  have ht' : θ * star (herm H a b) = t := by
    have := congrArg star ht
    simpa using this
  set d : Fin m → ℂ := a + (-θ) • b with hd
  have had : herm H a d = (q : ℂ) - t := by
    rw [hd, herm_add_right, herm_smul_right, ha, star_neg]
    linear_combination -ht
  have hdd : herm H d d = 2 * ((q : ℂ) - t) := by
    rw [hd, herm_add_left, herm_smul_left, ← hd, had, hd, herm_add_right, herm_smul_right, hb, hba, star_neg]
    linear_combination (q : ℂ) * hθ - ht'
  have hR : qrefl H d (-1 / ((q : ℂ) - t)) ∈ UH H := by
    apply qrefl_mem H hH
    rw [hdd]
    have : star (-1 / ((q : ℂ) - t)) = -1 / ((q : ℂ) - t) := by simp
    rw [this]
    field_simp
    ring
  have hS : qrefl H b ((star θ - 1) / q) ∈ UH H := by
    apply qrefl_mem H hH
    rw [hb]
    have : star ((star θ - 1) / (q : ℂ)) = (θ - 1) / q := by simp
    rw [this]
    field_simp
    linear_combination hθ
  refine ⟨qrefl H b ((star θ - 1) / q) * qrefl H d (-1 / ((q : ℂ) - t)), UH_mul hS hR, ?_, ?_⟩
  · rw [← Matrix.mulVec_mulVec, qrefl_mulVec H d, had]
    have h1 : a + (-1 / ((q : ℂ) - t) * ((q : ℂ) - t)) • d = θ • b := by
      rw [div_mul_cancel₀ _ hqdC, hd]
      simp
    rw [h1, qrefl_mulVec, herm_smul_left, hb, ← add_smul]
    have h2 : θ + (star θ - 1) / (q : ℂ) * (θ * q) = 1 := by
      field_simp
      linear_combination hθ
    rw [h2, one_smul]
  · intro x hxa hxb
    have hxd : herm H x d = 0 := by
      rw [hd, herm_add_right, herm_smul_right, hxa, hxb]; simp
    rw [← Matrix.mulVec_mulVec, qrefl_mulVec H d, hxd, mul_zero, zero_smul, add_zero, qrefl_mulVec, hxb, mul_zero,
      zero_smul, add_zero]

theorem trans_fix {m : ℕ} (H : Matrix (Fin m) (Fin m) ℂ) (hH : Hᴴ = H) (z v₁ v₂ : Fin m → ℂ) (T : ℝ) (hT : T ≠ 0)
    (hz : herm H z z = -(T : ℂ)) (h12 : herm H v₁ v₁ = herm H v₂ v₂) (hζ : herm H v₁ z = herm H v₂ z)
    (hne : (herm H v₁ v₁).re * T + Complex.normSq (herm H v₁ z) ≠ 0) :
    ∃ g ∈ UH H, g *ᵥ z = z ∧ g *ᵥ v₁ = v₂ := by
  have hTC : (T : ℂ) ≠ 0 := by exact_mod_cast hT
  set ζ : ℂ := herm H v₁ z with hζdef
  set q : ℝ := ((herm H v₁ v₁).re * T + Complex.normSq ζ) / T with hqdef
  have hq : q ≠ 0 := div_ne_zero hne hT
  have key : ∀ v : Fin m → ℂ, herm H v z = ζ → herm H v v = herm H v₁ v₁ →
      herm H (v + (ζ / T) • z) (v + (ζ / T) • z) = q ∧ herm H z (v + (ζ / T) • z) = 0 := by
    intro v hv hvv
    have hzv : herm H z v = star ζ := by rw [herm_symm H hH v z, hv]
    have hst : star (ζ / (T : ℂ)) = star ζ / T := by simp
    have hns : (Complex.normSq ζ : ℂ) = ζ * star ζ := by
      rw [Complex.star_def, Complex.mul_conj]
    constructor
    · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hv, hzv, hz, hvv, hst]
      rw [herm_self_real H hH v₁, hqdef]
      push_cast
      rw [hns]
      field_simp
      ring
    · simp only [herm_add_right, herm_smul_right, hzv, hz, hst]
      field_simp
      ring
  obtain ⟨h1a, h1b⟩ := key v₁ rfl rfl
  obtain ⟨h2a, h2b⟩ := key v₂ hζ.symm h12.symm
  obtain ⟨g, hg, hga, hgx⟩ := trans H hH _ _ q hq h1a h2a
  have hgz : g *ᵥ z = z := hgx z h1b h2b
  refine ⟨g, hg, hgz, ?_⟩
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, hgz] at hga
  exact add_right_cancel hga

end PartB

section PartC

variable {k r : ℕ}

lemma herm_star {m : ℕ} {H : Matrix (Fin m) (Fin m) ℂ} (hH : Hᴴ = H) (x y : Fin m → ℂ) :
    star (herm H x y) = herm H y x := by
  unfold herm
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hH, ← Matrix.dotProduct_mulVec]

lemma herm_self_eq (z : Fin (2 * r + k + 1) → ℂ) : herm (Hpk k r) z z = -((Tz k r z : ℝ) : ℂ) := by
  have h := herm_star (hpkFacts k r).1 z z
  have him : (herm (Hpk k r) z z).im = 0 := by
    have := congrArg Complex.im h
    simp only [Complex.star_def, Complex.conj_im] at this
    linarith
  apply Complex.ext
  · simp [Tz]
  · simp [him]

lemma inv_fix {a : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (ha : a ∈ UH (Hb k)) {x : Fin (k + 1) → ℂ}
    (hx : a *ᵥ x = x) : a⁻¹ *ᵥ x = x := by
  conv_lhs => rw [← hx]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (UHb_inv ha).1, Matrix.one_mulVec]

lemma orbit {z v₁ v₂ : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hv₁ : inWb k r v₁) (hv₂ : inWb k r v₂)
    (hT : Tz k r z ≠ 0) (h12 : herm (Hpk k r) v₁ v₁ = herm (Hpk k r) v₂ v₂)
    (hζ : herm (Hpk k r) v₁ z = herm (Hpk k r) v₂ z)
    (hne : (herm (Hpk k r) v₁ v₁).re * Tz k r z + Complex.normSq (herm (Hpk k r) v₁ z) ≠ 0) :
    ∃ h ∈ UWset k r z, h *ᵥ v₁ = v₂ := by
  have hzz := herm_self_eq z
  rw [← jV_wbPart hz] at hzz hζ hne
  rw [← jV_wbPart hv₁] at h12 hζ hne
  rw [← jV_wbPart hv₂] at h12 hζ
  simp only [herm_jV] at hzz h12 hζ hne
  rw [jV_wbPart hz] at hzz hne
  obtain ⟨g, hg, hgz, hgv⟩ := trans_fix (Hb k) Hb_herm (wbPart k r z) (wbPart k r v₁) (wbPart k r v₂) (Tz k r z) hT
    hzz h12 hζ hne
  refine ⟨embWb k r g, (UWset_iff hz _).2 ⟨g, hg, hgz, rfl⟩, ?_⟩
  rw [← jV_wbPart hv₁, emb_mulVec_jV, hgv, jV_wbPart hv₂]

lemma sec_vec {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    (hz : inWb k r z) (hz' : inWb k r z') (hsec : IsSection k r z z' μsec) {ζ : ℂ}
    (hζ : Tz k r z * Tz k r z' < Complex.normSq ζ) :
    inWb k r (embWb k r (μsec ζ) *ᵥ z') ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') (embWb k r (μsec ζ) *ᵥ z') = herm (Hpk k r) z' z' ∧
      herm (Hpk k r) (embWb k r (μsec ζ) *ᵥ z') z = ζ := by
  obtain ⟨hU, hval⟩ := hsec.2 ζ hζ
  have hU' : μsec ζ ∈ UH (Hb k) := hU
  have e : embWb k r (μsec ζ) *ᵥ z' = jV k r (μsec ζ *ᵥ wbPart k r z') := by
    conv_lhs => rw [← jV_wbPart hz']
    rw [emb_mulVec_jV]
  rw [e]
  refine ⟨inWb_jV _, ?_, ?_⟩
  · rw [herm_jV, herm_UH hU']
    conv_rhs => rw [← jV_wbPart hz']
    rw [herm_jV]
  · conv_lhs => rw [← jV_wbPart hz]
    rw [herm_jV, hval]

theorem rankOneMem : RankOneMem := by
  intro k r z z' μsec hz hz' hsec ζ hζ h hh h' hh'
  obtain ⟨hU, hval⟩ := hsec.2 ζ hζ
  have hU' : μsec ζ ∈ UH (Hb k) := hU
  obtain ⟨η, hη, hηz, rfl⟩ := (UWset_iff hz h).1 hh
  obtain ⟨η', hη', hηz', rfl⟩ := (UWset_iff hz' h').1 hh'
  rw [emb_inv hη, ← emb_mul, ← emb_mul]
  refine ⟨(UWb_iff _).2 ⟨_, UHb_mul (UHb_mul (UHb_inv hη).2 hU') hη', rfl⟩, ?_⟩
  conv_lhs => rw [← jV_wbPart hz', ← jV_wbPart hz]
  rw [emb_mulVec_jV, herm_jV, ← Matrix.mulVec_mulVec, hηz', ← Matrix.mulVec_mulVec]
  conv_lhs => rw [← inv_fix hη hηz]
  rw [herm_UH (UHb_inv hη).2, hval]

theorem rankOneCoord : RankOneCoord := by
  intro k r z z' μsec _ hz hz' hT _ hsec m hm hζ
  set ζ := herm (Hpk k r) (m *ᵥ z') z with hζdef
  obtain ⟨hU, _⟩ := hsec.2 ζ hζ
  have hU' : μsec ζ ∈ UH (Hb k) := hU
  obtain ⟨s1, s2, s3⟩ := sec_vec hz hz' hsec hζ
  obtain ⟨ν, hν, rfl⟩ := (UWb_iff m).1 hm
  have e : embWb k r ν *ᵥ z' = jV k r (ν *ᵥ wbPart k r z') := by
    conv_lhs => rw [← jV_wbPart hz']
    rw [emb_mulVec_jV]
  have n1 : herm (Hpk k r) (embWb k r ν *ᵥ z') (embWb k r ν *ᵥ z') = herm (Hpk k r) z' z' := by
    rw [e, herm_jV, herm_UH hν]
    conv_rhs => rw [← jV_wbPart hz']
    rw [herm_jV]
  obtain ⟨h, hh, hv⟩ := orbit (v₁ := embWb k r ν *ᵥ z') (v₂ := embWb k r (μsec ζ) *ᵥ z') hz
    (by rw [e]; exact inWb_jV _) s1 hT.ne' (by rw [n1, s2]) (by rw [s3]) (by
      rw [n1, herm_self_eq z', ← hζdef]
      simp only [Complex.neg_re, Complex.ofReal_re]
      nlinarith)
  obtain ⟨η, hη, hηz, rfl⟩ := (UWset_iff hz h).1 hh
  have hfix : ((μsec ζ)⁻¹ * η * ν) *ᵥ wbPart k r z' = wbPart k r z' := by
    have h1 : η *ᵥ (ν *ᵥ wbPart k r z') = μsec ζ *ᵥ wbPart k r z' := by
      have h2 := congrArg (wbPart k r) hv
      rw [e, emb_mulVec_jV, wbPart_jV] at h2
      rw [h2]
      conv_lhs => rw [← jV_wbPart hz']
      rw [emb_mulVec_jV, wbPart_jV]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ (UHb_inv hU').1, Matrix.one_mulVec]
  refine ⟨embWb k r η, hh, embWb k r ((μsec ζ)⁻¹ * η * ν),
    (UWset_iff hz' _).2 ⟨_, UHb_mul (UHb_mul (UHb_inv hU').2 hη) hν, hfix, rfl⟩, ?_⟩
  rw [emb_inv hη, ← emb_mul, ← emb_mul]
  congr 1
  rw [Matrix.mul_assoc (μsec ζ)⁻¹, ← Matrix.mul_assoc _ (μsec ζ)⁻¹, Matrix.mul_assoc η⁻¹,
    Matrix.mul_nonsing_inv _ (UHb_inv hU').1, Matrix.mul_one, ← Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (UHb_inv hη).1, Matrix.one_mul]

end PartC

section PartM

open Set
open scoped Pointwise

def Sq (k : ℕ) (x : Fin k → ℂ) : ℝ := ∑ i, Complex.normSq (x i)

lemma Sq_cont (k : ℕ) : Continuous (Sq k) := by
  unfold Sq
  exact continuous_finsetSum _ fun i _ => Complex.continuous_normSq.comp (continuous_apply i)

lemma Sq_nonneg {k : ℕ} (x : Fin k → ℂ) : 0 ≤ Sq k x := Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

lemma Sq_smul {k : ℕ} (a : ℝ) (x : Fin k → ℂ) : Sq k (a • x) = a ^ 2 * Sq k x := by
  unfold Sq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, Complex.real_smul, Complex.normSq_mul, Complex.normSq_ofReal]
  ring

lemma ext_Iic (μ ν : Measure ℝ) (h : ∀ b, μ (Iic b) = ν (Iic b)) (hf : ∀ b, μ (Iic b) ≠ ∞) : μ = ν := by
  refine Measure.ext_of_Ioc' μ ν (fun a b _ => ne_top_of_le_ne_top (hf b) (measure_mono Ioc_subset_Iic_self))
    (fun a b hab => ?_)
  rw [← Iic_sdiff_Iic, measure_sdiff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (hf a),
    measure_sdiff (Iic_subset_Iic.2 hab.le) nullMeasurableSet_Iic (h a ▸ hf a), h a, h b]

def Vb (k : ℕ) : ℝ≥0∞ := volume {x : Fin k → ℂ | Sq k x ≤ 1}

lemma Vb_ne_top (k : ℕ) : Vb k ≠ ∞ := by
  have : {x : Fin k → ℂ | Sq k x ≤ 1} ⊆ Metric.closedBall 0 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : Complex.normSq (x i) ≤ Sq k x :=
      Finset.single_le_sum (f := fun i => Complex.normSq (x i)) (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
    have h2 : ‖x i‖ ^ 2 ≤ 1 := by rw [← Complex.normSq_eq_norm_sq]; exact h1.trans hx
    nlinarith [norm_nonneg (x i)]
  exact ne_top_of_le_ne_top measure_closedBall_lt_top.ne (measure_mono this)

lemma Vb_ne_zero (k : ℕ) : Vb k ≠ 0 := by
  have ho : IsOpen {x : Fin k → ℂ | Sq k x < 1} := isOpen_lt (Sq_cont k) continuous_const
  have hn : {x : Fin k → ℂ | Sq k x < 1}.Nonempty := ⟨0, by simp [Sq]⟩
  have := ho.measure_pos volume hn
  exact (this.trans_le (measure_mono fun x (hx : Sq k x < 1) => (le_of_lt hx : Sq k x ≤ 1))).ne'

lemma vol_Sq_le (n : ℕ) {b : ℝ} (hb : 0 ≤ b) :
    volume {x : Fin (n + 1) → ℂ | Sq (n + 1) x ≤ b} = ENNReal.ofReal (b ^ (n + 1)) * Vb (n + 1) := by
  have hset : {x : Fin (n + 1) → ℂ | Sq (n + 1) x ≤ b} = √b • {x : Fin (n + 1) → ℂ | Sq (n + 1) x ≤ 1} := by
    rcases hb.eq_or_lt with rfl | hb'
    · rw [Real.sqrt_zero, zero_smul_set ⟨0, by simp [Sq]⟩]
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_zero]
      constructor
      · intro hx
        have h0 : Sq (n + 1) x = 0 := le_antisymm hx (Sq_nonneg x)
        funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).1 h0 i (Finset.mem_univ i)
        simpa using this
      · rintro rfl; simp [Sq]
    · have hs : √b ≠ 0 := (Real.sqrt_pos.2 hb').ne'
      ext x
      rw [mem_smul_set_iff_inv_smul_mem₀ hs]
      simp only [Set.mem_ofPred_eq, Sq_smul, inv_pow, Real.sq_sqrt hb]
      rw [inv_mul_le_iff₀ hb', mul_one]
  have hfr : Module.finrank ℝ (Fin (n + 1) → ℂ) = 2 * (n + 1) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  rw [hset, Measure.addHaar_smul, hfr, pow_mul, Real.sq_sqrt hb, abs_of_nonneg (pow_nonneg hb _)]
  rfl

def dens (n : ℕ) : Measure ℝ := (volume.restrict (Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal (t ^ n)

lemma dens_Iic (n : ℕ) (b : ℝ) : dens n (Iic b) = ENNReal.ofReal ((max b 0) ^ (n + 1) / (n + 1)) := by
  unfold dens
  rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
  have hI : Iic b ∩ Ioi (0 : ℝ) = Ioc 0 b := by ext t; simp [and_comm]
  rw [hI]
  rcases le_total b 0 with hb | hb
  · rw [Ioc_eq_empty (not_lt.2 hb), max_eq_right hb]; simp
  · rw [max_eq_left hb, ← ofReal_integral_eq_lintegral_ofReal]
    · rw [← intervalIntegral.integral_of_le hb, integral_pow]
      simp
    · exact (continuous_pow n).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    · exact (ae_restrict_iff' measurableSet_Ioc).2 (ae_of_all _ fun t ht => pow_nonneg ht.1.le n)

lemma map_Sq (n : ℕ) :
    Measure.map (Sq (n + 1)) volume = ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) • dens n := by
  have hF : ∀ b, Measure.map (Sq (n + 1)) volume (Iic b) = ENNReal.ofReal ((max b 0) ^ (n + 1)) * Vb (n + 1) := by
    intro b
    rw [Measure.map_apply (Sq_cont _).measurable measurableSet_Iic]
    rcases le_total 0 b with hb | hb
    · rw [max_eq_left hb]; exact vol_Sq_le n hb
    · rcases hb.eq_or_lt with rfl | hb'
      · rw [max_self]; exact vol_Sq_le n le_rfl
      · rw [max_eq_right hb]
        have : Sq (n + 1) ⁻¹' Iic b = ∅ := by
          ext x; simp only [mem_preimage, mem_Iic, mem_empty_iff_false, iff_false, not_le]
          exact hb'.trans_le (Sq_nonneg x)
        rw [this]; simp
  refine ext_Iic _ _ (fun b => ?_) (fun b => ?_)
  · rw [hF, Measure.smul_apply, dens_Iic, smul_eq_mul]
    have h0 : (0 : ℝ) ≤ max b 0 := le_max_right _ _
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    have : ENNReal.ofReal ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ≥0∞) := by
      rw [← Nat.cast_succ, ENNReal.ofReal_natCast]
    rw [this]
    have hne : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by simp
    have hnt : ((n + 1 : ℕ) : ℝ≥0∞) ≠ ∞ := ENNReal.natCast_ne_top _
    rw [mul_comm (((n + 1 : ℕ) : ℝ≥0∞)) _, mul_assoc, ENNReal.mul_div_cancel hne hnt, mul_comm]
  · rw [hF]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Vb_ne_top _)

def Nq (k : ℕ) (u : Fin (k + 1) → ℂ) : ℝ :=
  Complex.normSq (u (Fin.last k)) - ∑ i : Fin k, Complex.normSq (u i.castSucc)

def cs (T T' s : ℝ) : ℂ := ((-(√T * √(T' / s)) : ℝ) : ℂ)

lemma cs_meas (T T' : ℝ) : Measurable (cs T T') := by
  unfold cs
  exact Complex.measurable_ofReal.comp
    ((measurable_const.mul (Real.continuous_sqrt.measurable.comp (measurable_const.div measurable_id))).neg)

lemma cs_real_sq {T T' s : ℝ} (hT : 0 < T) (hT' : 0 < T') (hs : 0 < s) :
    (-(√T * √(T' / s))) ^ 2 = T * T' / s := by
  calc (-(√T * √(T' / s))) ^ 2 = (√T) ^ 2 * (√(T' / s)) ^ 2 := by ring
    _ = T * (T' / s) := by rw [Real.sq_sqrt hT.le, Real.sq_sqrt (div_pos hT' hs).le]
    _ = T * T' / s := by ring

lemma cs_sq {T T' s : ℝ} (hT : 0 < T) (hT' : 0 < T') (hs : 0 < s) :
    Complex.normSq (cs T T' s) = T * T' / s := by
  unfold cs
  rw [Complex.normSq_ofReal, ← sq, cs_real_sq hT hT' hs]

def Wf (n : ℕ) (T T' : ℝ) (φ : ℂ → ℝ≥0∞) : ℂ → ℝ≥0∞ :=
  {ζ : ℂ | T * T' < Complex.normSq ζ}.indicator fun ζ => ENNReal.ofReal ((Complex.normSq ζ - T * T') ^ n) * φ ζ

lemma Wf_meas (n : ℕ) (T T' : ℝ) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) : Measurable (Wf n T T' φ) := by
  unfold Wf
  refine Measurable.indicator ?_ (measurableSet_lt measurable_const Complex.continuous_normSq.measurable)
  exact (ENNReal.measurable_ofReal.comp ((Complex.continuous_normSq.measurable.sub_const _).pow_const _)).mul hφ

lemma lint_Wf (n : ℕ) (T T' : ℝ) (φ : ℂ → ℝ≥0∞) :
    (∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight (n + 1) T T' ζ) * φ ζ) = ∫⁻ ζ : ℂ, Wf n T T' φ ζ := by
  have hnull : volume {ζ : ℂ | Complex.normSq ζ = T * T'} = 0 := by
    refine measure_mono_null ?_ (Measure.addHaar_sphere volume (0 : ℂ) (√(T * T')))
    intro ζ (hζ : Complex.normSq ζ = T * T')
    rw [mem_sphere_zero_iff_norm, ← hζ, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  refine lintegral_congr_ae ?_
  have : ∀ᵐ ζ : ℂ, ¬ Complex.normSq ζ = T * T' := by rw [ae_iff]; simpa using hnull
  filter_upwards [this] with ζ hζ
  unfold Wf zWeight
  rw [Set.indicator_apply]
  by_cases h : T * T' < Complex.normSq ζ
  · rw [if_pos h.le, if_pos (show ζ ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from h), Nat.add_sub_cancel]
  · rw [if_neg (fun h' => h (lt_of_le_of_ne h' (Ne.symm hζ))),
      if_neg (show ¬ ζ ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from h)]; simp

lemma lint_scale {a : ℝ} (ha : a ≠ 0) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ y : ℂ, g ((a : ℂ) * y)) = ENNReal.ofReal ((a ^ 2)⁻¹) * ∫⁻ ζ : ℂ, g ζ := by
  have h := Measure.map_addHaar_smul (volume : Measure ℂ) ha
  rw [Complex.finrank_real_complex, abs_of_nonneg (inv_nonneg.2 (sq_nonneg a))] at h
  have h2 : (∫⁻ y : ℂ, g (a • y)) = ∫⁻ ζ, g ζ ∂(Measure.map (a • ·) (volume : Measure ℂ)) :=
    (lintegral_map hg (measurable_const_smul a)).symm
  rw [h, lintegral_smul_measure] at h2
  simpa only [Complex.real_smul, smul_eq_mul] using h2

def Ff (T T' : ℝ) (φ : ℂ → ℝ≥0∞) (y : ℂ) : ℝ → ℝ≥0∞ := (Ioc 0 T').indicator fun s => φ (cs T T' s * y)

lemma Ff_meas (T T' : ℝ) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun p : ℂ × ℝ => Ff T T' φ p.1 p.2 := by
  have : (fun p : ℂ × ℝ => Ff T T' φ p.1 p.2) =
      (Prod.snd ⁻¹' Ioc 0 T').indicator fun p : ℂ × ℝ => φ (cs T T' p.2 * p.1) := by
    funext p
    by_cases h : p.2 ∈ Ioc 0 T'
    · rw [Ff, Set.indicator_of_mem h, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Ioc 0 T' from h)]
    · rw [Ff, Set.indicator_of_notMem h, Set.indicator_of_notMem (show ¬ p ∈ Prod.snd ⁻¹' Ioc 0 T' from h)]
  rw [this]
  exact (hφ.comp (((cs_meas T T').comp measurable_snd).mul measurable_fst)).indicator (measurable_snd measurableSet_Ioc)

def Rf (n : ℕ) (T T' : ℝ) (φ : ℂ → ℝ≥0∞) (y : ℂ) : ℝ → ℝ≥0∞ :=
  (Ioc 0 T').indicator fun s => ENNReal.ofReal ((s / (T * T')) ^ n) * Wf n T T' φ (cs T T' s * y)

lemma Rf_meas (n : ℕ) (T T' : ℝ) {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun p : ℂ × ℝ => Rf n T T' φ p.1 p.2 := by
  have : (fun p : ℂ × ℝ => Rf n T T' φ p.1 p.2) =
      (Prod.snd ⁻¹' Ioc 0 T').indicator fun p : ℂ × ℝ =>
        ENNReal.ofReal ((p.2 / (T * T')) ^ n) * Wf n T T' φ (cs T T' p.2 * p.1) := by
    funext p
    by_cases h : p.2 ∈ Ioc 0 T'
    · rw [Rf, Set.indicator_of_mem h, Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Ioc 0 T' from h)]
    · rw [Rf, Set.indicator_of_notMem h, Set.indicator_of_notMem (show ¬ p ∈ Prod.snd ⁻¹' Ioc 0 T' from h)]
  rw [this]
  refine Measurable.indicator ?_ (measurable_snd measurableSet_Ioc)
  exact (ENNReal.measurable_ofReal.comp ((measurable_snd.div_const _).pow_const _)).mul
    ((Wf_meas n T T' hφ).comp (((cs_meas T T').comp measurable_snd).mul measurable_fst))

lemma refl_eq (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (φ : ℂ → ℝ≥0∞) (y : ℂ) (s : ℝ) :
    (Ioi (0 : ℝ)).indicator (fun t => ENNReal.ofReal (t ^ n) * Ff T T' φ y (Complex.normSq y - t))
      (Complex.normSq y - s) = Rf n T T' φ y s := by
  have hTT : 0 < T * T' := mul_pos hT hT'
  rw [Set.indicator_apply, sub_sub_cancel]
  unfold Ff Rf
  by_cases hs : s ∈ Ioc 0 T'
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
    have hs0 : 0 < s := hs.1
    unfold Wf
    rw [Set.indicator_apply]
    have hN : Complex.normSq (cs T T' s * y) = T * T' / s * Complex.normSq y := by
      rw [Complex.normSq_mul, cs_sq hT hT' hs0]
    have hiff : (T * T' < Complex.normSq (cs T T' s * y)) ↔ 0 < Complex.normSq y - s := by
      rw [hN, div_mul_eq_mul_div, lt_div_iff₀ hs0, sub_pos]
      exact mul_lt_mul_iff_right₀ hTT
    by_cases h : 0 < Complex.normSq y - s
    · rw [if_pos (show Complex.normSq y - s ∈ Ioi (0 : ℝ) from h),
        if_pos (show cs T T' s * y ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from hiff.2 h), ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← mul_pow, hN]
      congr 3
      field_simp
    · rw [if_neg (show ¬ Complex.normSq y - s ∈ Ioi (0 : ℝ) from h),
        if_neg (show ¬ cs T T' s * y ∈ {ζ : ℂ | T * T' < Complex.normSq ζ} from fun h' => h (hiff.1 h')), mul_zero]
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, mul_zero, ite_self]

def Jc (n : ℕ) (T T' : ℝ) : ℝ≥0∞ :=
  ∫⁻ s in Ioc 0 T', ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))

lemma Jc_ne_top (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') : Jc n T T' ≠ ∞ := by
  unfold Jc
  have hb : ∀ s ∈ Ioc 0 T', ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T')) ≤
      ENNReal.ofReal ((1 / T) ^ n) * ENNReal.ofReal (1 / T) := by
    intro s hs
    have h1 : s / (T * T') ≤ 1 / T := by
      rw [div_le_div_iff₀ (by positivity) hT]; nlinarith [hs.2]
    have h0 : 0 ≤ s / (T * T') := by have := hs.1; positivity
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ h0 h1 n)) (ENNReal.ofReal_le_ofReal h1)
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' measurableSet_Ioc hb)
  rw [setLIntegral_const, Real.volume_Ioc]
  exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) ENNReal.ofReal_ne_top

lemma Jc_ne_zero (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') : Jc n T T' ≠ 0 := by
  unfold Jc
  have hm : Measurable fun s : ℝ => ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T')) :=
    (ENNReal.measurable_ofReal.comp ((measurable_id.div_const _).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.div_const _))
  refine ((setLIntegral_pos_iff hm).2 ?_).ne'
  have hsub : Ioc 0 T' ⊆ (Function.support fun s : ℝ =>
      ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))) ∩ Ioc 0 T' := by
    intro s hs
    refine ⟨?_, hs⟩
    have h0 : 0 < s / (T * T') := by have := hs.1; positivity
    rw [Function.mem_support]
    exact mul_ne_zero (ENNReal.ofReal_pos.2 (pow_pos h0 n)).ne' (ENNReal.ofReal_pos.2 h0).ne'
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioc, sub_zero]
  exact ENNReal.ofReal_pos.2 hT'

lemma inner_eq (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) (y : ℂ) :
    (∫⁻ x : Fin (n + 1) → ℂ, Ff T T' φ y (Complex.normSq y - Sq (n + 1) x)) =
      ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) * ∫⁻ s : ℝ, Rf n T T' φ y s := by
  have hF : Measurable fun t : ℝ => Ff T T' φ y (Complex.normSq y - t) :=
    (Ff_meas T T' hφ).comp (measurable_const.prodMk (measurable_const.sub measurable_id))
  have hd : Measurable fun t : ℝ => ENNReal.ofReal (t ^ n) :=
    ENNReal.measurable_ofReal.comp (measurable_id.pow_const n)
  rw [← lintegral_map hF (Sq_cont _).measurable, map_Sq, lintegral_smul_measure, smul_eq_mul]
  congr 1
  unfold dens
  rw [lintegral_withDensity_eq_lintegral_mul _ hd hF, ← lintegral_indicator measurableSet_Ioi]
  have hg : Measurable ((Ioi (0 : ℝ)).indicator
      fun t => ENNReal.ofReal (t ^ n) * Ff T T' φ y (Complex.normSq y - t)) :=
    (hd.mul hF).indicator measurableSet_Ioi
  have h2 := (Measure.measurePreserving_sub_left (volume : Measure ℝ) (Complex.normSq y)).lintegral_comp hg
  refine Eq.trans ?_ (Eq.trans h2.symm (lintegral_congr fun s => refl_eq n hT hT' φ y s))
  rfl

lemma outer_eq (n : ℕ) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') {φ : ℂ → ℝ≥0∞} (hφ : Measurable φ) (s : ℝ) :
    (∫⁻ y : ℂ, Rf n T T' φ y s) =
      (Ioc 0 T').indicator (fun s => ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))) s *
        ∫⁻ ζ : ℂ, Wf n T T' φ ζ := by
  by_cases hs : s ∈ Ioc 0 T'
  · have hs0 : 0 < s := hs.1
    simp only [Rf, Set.indicator_of_mem hs]
    have hm : Measurable fun y : ℂ => Wf n T T' φ (cs T T' s * y) :=
      (Wf_meas n T T' hφ).comp (measurable_const_mul _)
    rw [lintegral_const_mul _ hm]
    have hne : -(√T * √(T' / s)) ≠ 0 :=
      neg_ne_zero.2 (mul_pos (Real.sqrt_pos.2 hT) (Real.sqrt_pos.2 (div_pos hT' hs0))).ne'
    unfold cs
    rw [lint_scale hne (Wf_meas n T T' hφ), cs_real_sq hT hT' hs0, inv_div, mul_assoc]
  · simp only [Rf, Set.indicator_of_notMem hs, lintegral_zero, zero_mul]

theorem push_calc (k : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (hT : 0 < T) (hT' : 0 < T') :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ ∀ φ : ℂ → ℝ≥0∞, Measurable φ →
      (∫⁻ u : Fin (k + 1) → ℂ in {u | 0 < Nq k u ∧ Nq k u ≤ T'},
          φ (((-(√T * √(T' / Nq k u)) : ℝ) : ℂ) * u (Fin.last k))) =
        c * ∫⁻ ζ : ℂ, ENNReal.ofReal (zWeight k T T' ζ) * φ ζ := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  have hc0 : ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) ≠ 0 := mul_ne_zero (by simp) (Vb_ne_zero _)
  have hct : ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (Vb_ne_top _)
  refine ⟨((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) * Jc n T T', mul_ne_zero hc0 (Jc_ne_zero n hT hT'),
    ENNReal.mul_ne_top hct (Jc_ne_top n hT hT'), ?_⟩
  intro φ hφ
  rw [lint_Wf]
  have hNq : Measurable (Nq (n + 1)) := by
    unfold Nq
    exact (Complex.continuous_normSq.measurable.comp (measurable_pi_apply _)).sub
      (Finset.measurable_sum _ fun i _ => Complex.continuous_normSq.measurable.comp (measurable_pi_apply _))
  have hA : MeasurableSet {u : Fin (n + 1 + 1) → ℂ | 0 < Nq (n + 1) u ∧ Nq (n + 1) u ≤ T'} :=
    (measurableSet_lt measurable_const hNq).inter (measurableSet_le hNq measurable_const)
  rw [← lintegral_indicator hA]
  let Φ : ℂ × (Fin (n + 1) → ℂ) → ℝ≥0∞ := fun p => Ff T T' φ p.1 (Complex.normSq p.1 - Sq (n + 1) p.2)
  have hΦ : Measurable Φ :=
    (Ff_meas T T' hφ).comp (measurable_fst.prodMk ((Complex.continuous_normSq.measurable.comp measurable_fst).sub
      ((Sq_cont _).measurable.comp measurable_snd)))
  have e := volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1 + 1) => ℂ) (Fin.last (n + 1))
  have h1 : ∀ u : Fin (n + 1 + 1) → ℂ,
      {u : Fin (n + 1 + 1) → ℂ | 0 < Nq (n + 1) u ∧ Nq (n + 1) u ≤ T'}.indicator
        (fun u => φ (((-(√T * √(T' / Nq (n + 1) u)) : ℝ) : ℂ) * u (Fin.last (n + 1)))) u =
      Φ (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 1) => ℂ) (Fin.last (n + 1)) u) := by
    intro u
    have hv : MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1 + 1) => ℂ) (Fin.last (n + 1)) u =
        (u (Fin.last (n + 1)), fun j : Fin (n + 1) => u j.castSucc) := by
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
      rfl
    rw [hv]
    show _ = (Ioc 0 T').indicator (fun s => φ (cs T T' s * u (Fin.last (n + 1)))) (Nq (n + 1) u)
    rw [Set.indicator_apply, Set.indicator_apply]
    rfl
  rw [lintegral_congr h1, e.lintegral_comp hΦ, Measure.volume_eq_prod, lintegral_prod _ hΦ.aemeasurable]
  have h2 : ∀ y : ℂ, (∫⁻ x : Fin (n + 1) → ℂ, Φ (y, x)) =
      ((n + 1 : ℕ) * Vb (n + 1) : ℝ≥0∞) * ∫⁻ s : ℝ, Rf n T T' φ y s := fun y => inner_eq n hT hT' hφ y
  have hJ : Measurable ((Ioc 0 T').indicator
      fun s : ℝ => ENNReal.ofReal ((s / (T * T')) ^ n) * ENNReal.ofReal (s / (T * T'))) :=
    ((ENNReal.measurable_ofReal.comp ((measurable_id.div_const _).pow_const _)).mul
      (ENNReal.measurable_ofReal.comp (measurable_id.div_const _))).indicator measurableSet_Ioc
  rw [lintegral_congr h2, lintegral_const_mul _ (Rf_meas n T T' hφ).lintegral_prod_right',
    lintegral_lintegral_swap (Rf_meas n T T' hφ).aemeasurable, lintegral_congr (outer_eq n hT hT' hφ),
    lintegral_mul_const _ hJ, lintegral_indicator measurableSet_Ioc]
  unfold Jc
  ring

end PartM

section PartD

variable {k r : ℕ}

lemma herm_Hb (u v : Fin (k + 1) → ℂ) :
    herm (Hb k) u v = (∑ i : Fin k, star (v i.castSucc) * u i.castSucc) - star (v (Fin.last k)) * u (Fin.last k) := by
  unfold herm Hb
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp [Matrix.mulVec_diagonal, Fin.castSucc_ne_last, sub_eq_add_neg]

lemma herm_Hb_self (u : Fin (k + 1) → ℂ) : herm (Hb k) u u = -((Nq k u : ℝ) : ℂ) := by
  rw [herm_Hb]
  unfold Nq
  push_cast
  simp only [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  ring

lemma Nq_cont : Continuous (Nq k) := by
  unfold Nq
  fun_prop

lemma Nq_UH {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) (u : Fin (k + 1) → ℂ) :
    Nq k (μ *ᵥ u) = Nq k u := by
  have h := herm_UH hμ u u
  rw [herm_Hb_self, herm_Hb_self] at h
  exact_mod_cast neg_injective h

lemma Nq_smul (c : ℝ) (u : Fin (k + 1) → ℂ) : Nq k ((c : ℂ) • u) = c ^ 2 * Nq k u := by
  unfold Nq
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul, Complex.normSq_ofReal]
  rw [← Finset.mul_sum]
  ring

def scl (k : ℕ) (T' : ℝ) (u : Fin (k + 1) → ℂ) : Fin (k + 1) → ℂ := ((√(T' / Nq k u) : ℝ) : ℂ) • u

def shell (k : ℕ) (T' : ℝ) : Set (Fin (k + 1) → ℂ) := {u | 0 < Nq k u ∧ Nq k u ≤ T'}

def σb (k : ℕ) (T' : ℝ) : Measure (Fin (k + 1) → ℂ) := ((volume : Measure (Fin (k + 1) → ℂ)).restrict (shell k T')).map (scl k T')

lemma scl_meas (T' : ℝ) : Measurable (scl k T') := by
  unfold scl
  have h : Measurable (Nq k) := Nq_cont.measurable
  exact (Complex.measurable_ofReal.comp ((measurable_const.div h).sqrt)).smul measurable_id

lemma shell_meas (T' : ℝ) : MeasurableSet (shell k T') :=
  (measurableSet_lt measurable_const Nq_cont.measurable).inter (measurableSet_le Nq_cont.measurable measurable_const)

lemma mulVec_meas {m : ℕ} (μ : Matrix (Fin m) (Fin m) ℂ) : Measurable (fun u : Fin m → ℂ => μ *ᵥ u) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).measurable

theorem map_mulVec_volume {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (h : ‖M.det‖ = 1) :
    Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = volume := by
  have hdet : LinearMap.det ((Matrix.toLin' M).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply,
      Complex.normSq_eq_norm_sq, h, one_pow]
  have h2 := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (ι → ℂ))
    (f := (Matrix.toLin' M).restrictScalars ℝ) (by rw [hdet]; exact one_ne_zero)
  rw [hdet] at h2
  have h3 : Measure.map (fun x : ι → ℂ => M *ᵥ x) volume = ENNReal.ofReal |(1 : ℝ)⁻¹| • volume := h2
  simpa using h3

lemma σb_inv (T' : ℝ) {μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} (hμ : μ ∈ UH (Hb k)) :
    (σb k T').map (fun u => μ *ᵥ u) = σb k T' := by
  unfold σb
  rw [Measure.map_map (mulVec_meas μ) (scl_meas T')]
  have h1 : (fun u => μ *ᵥ u) ∘ scl k T' = scl k T' ∘ (fun u => μ *ᵥ u) := by
    funext u
    simp only [Function.comp, scl, Nq_UH hμ, Matrix.mulVec_smul]
  rw [h1, ← Measure.map_map (scl_meas T') (mulVec_meas μ)]
  congr 1
  have h2 : (fun u => μ *ᵥ u) ⁻¹' shell k T' = shell k T' := by
    ext u
    show (0 < Nq k (μ *ᵥ u) ∧ Nq k (μ *ᵥ u) ≤ T') ↔ (0 < Nq k u ∧ Nq k u ≤ T')
    rw [Nq_UH hμ]
  conv_lhs => rw [← h2]
  rw [← Measure.restrict_map (mulVec_meas μ) (shell_meas T'), map_mulVec_volume μ (UHb_det hμ)]

lemma σb_conc {T' : ℝ} (hT' : 0 < T') : ∀ᵐ u ∂σb k T', Nq k u = T' := by
  unfold σb
  rw [ae_map_iff (scl_meas T').aemeasurable (measurableSet_eq_fun Nq_cont.measurable measurable_const),
    ae_restrict_iff' (shell_meas T')]
  refine Filter.Eventually.of_forall fun u hu => ?_
  unfold scl
  rw [Nq_smul, Real.sq_sqrt (div_nonneg hT'.le hu.1.le), div_mul_cancel₀ _ hu.1.ne']

lemma zW_meas (k : ℕ) (T T' : ℝ) : Measurable (fun ζ : ℂ => ENNReal.ofReal (zWeight k T T' ζ)) := by
  unfold zWeight
  refine ENNReal.measurable_ofReal.comp (Measurable.ite ?_ ?_ measurable_const)
  · exact measurableSet_le measurable_const Complex.continuous_normSq.measurable
  · exact ((Complex.continuous_normSq.measurable).sub_const _).pow_const _

lemma σb_push (hk : 1 ≤ k) {T T' : ℝ} (hT : 0 < T) (hT' : 0 < T') (zb : Fin (k + 1) → ℂ)
    (hz : herm (Hb k) zb zb = -((T : ℝ) : ℂ)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧ (σb k T').map (fun u => herm (Hb k) u zb) =
      c • (volume : Measure ℂ).withDensity (fun ζ => ENNReal.ofReal (zWeight k T T' ζ)) := by
  obtain ⟨c, hc0, hc1, hc⟩ := push_calc k hk T T' hT hT'
  refine ⟨c, hc0, hc1, ?_⟩
  set z₀ : Fin (k + 1) → ℂ := ((√T : ℝ) : ℂ) • bvec (Fin.last k) with hz₀
  have hz₀z₀ : herm (Hb k) z₀ z₀ = ((-T : ℝ) : ℂ) := by
    rw [herm_Hb_self, hz₀, Nq_smul, Real.sq_sqrt hT.le]
    simp [Nq, bvec]
  obtain ⟨g, hg, hgz, -⟩ := trans (Hb k) Hb_herm z₀ zb (-T) (neg_ne_zero.2 hT.ne') hz₀z₀ (by rw [hz]; push_cast; rfl)
  have hgi := UHb_inv hg
  have hf : (fun u => herm (Hb k) u zb) = (fun u => herm (Hb k) u z₀) ∘ (fun u => g⁻¹ *ᵥ u) := by
    funext u
    have := herm_UH hg (g⁻¹ *ᵥ u) z₀
    rw [hgz, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hgi.1, Matrix.one_mulVec] at this
    exact this
  have hm0 : Measurable (fun u : Fin (k + 1) → ℂ => herm (Hb k) u z₀) := by
    simp only [herm_Hb]
    fun_prop
  rw [hf, ← Measure.map_map hm0 (mulVec_meas _), σb_inv T' hgi.2]
  unfold σb
  rw [Measure.map_map hm0 (scl_meas T')]
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  rw [lintegral_map hφ (hm0.comp (scl_meas T')), lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul _ (zW_meas k T T') hφ]
  have := hc φ hφ
  simp only [Pi.mul_apply, smul_eq_mul]
  rw [← this]
  refine lintegral_congr fun u => ?_
  congr 1
  simp only [Function.comp, scl, herm_Hb, hz₀, bvec]
  simp
  ring

end PartD

section PartE

variable {k r : ℕ}

lemma jV_meas : Measurable (jV k r) := by
  refine measurable_pi_iff.2 fun i => ?_
  unfold jV
  by_cases h : r ≤ i.val ∧ i.val ≤ r + k
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate

def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det

theorem detF_cont : Continuous (detF (k := k) (r := r)) := Continuous.matrix_det (continuous_id (X := Mat k r))

theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := Continuous.matrix_adjugate (continuous_id (X := Mat k r))

theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  show (Ring.inverse (Matrix.of x : Mat k r).det • (Matrix.of x : Mat k r).adjugate : Mat k r) = _
  rw [Ring.inverse_eq_inv']; rfl

theorem invM_meas : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]; exact detF_cont.measurable.inv.smul adjF_cont.measurable

def act (h : Mt k r) (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ := ((Matrix.of h : Mat k r)⁻¹ : Mat k r) *ᵥ v

lemma act_meas' : Measurable (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => act p.2 p.1) := by
  refine measurable_pi_iff.2 fun i => ?_
  show Measurable (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => ∑ j, invM p.2 i j * p.1 j)
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (invM_meas.comp measurable_snd))).mul
    ((measurable_pi_apply j).comp measurable_fst)

lemma act_meas_left (x : Fin (2 * r + k + 1) → ℂ) : Measurable (fun y : Mt k r => act y x) := by
  refine measurable_pi_iff.2 fun i => ?_
  show Measurable (fun y : Mt k r => ∑ j, invM y i j * x j)
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp invM_meas)).mul_const _

lemma act_lmul {h₁ : Mat k r} (hunit : IsUnit h₁.det) (h : Mt k r) (v : Fin (2 * r + k + 1) → ℂ) :
    act (lmulM h₁ h) (h₁ *ᵥ v) = act h v := by
  show ((h₁ * (Matrix.of h : Mat k r) : Mat k r)⁻¹ : Mat k r) *ᵥ (h₁ *ᵥ v) = ((Matrix.of h : Mat k r)⁻¹ : Mat k r) *ᵥ v
  rw [Matrix.mul_inv_rev, Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]

lemma GV_unit {g : Mat k r} (hg : g ∈ GV k r) : IsUnit g.det := by
  have hH : IsUnit (Hpk k r).det := by
    have := (hpkFacts k r).2.1
    exact (Matrix.isUnit_iff_isUnit_det _).1 (IsUnit.of_mul_eq_one _ this)
  exact ((uHGroup _ (Hpk k r) hH).2.2 g hg).1

instance (T' : ℝ) : SFinite (σb k T') := by unfold σb; infer_instance

def σV (k r : ℕ) (T' : ℝ) : Measure (Fin (2 * r + k + 1) → ℂ) := (σb k T').map (jV k r)

instance (T' : ℝ) : SFinite (σV k r T') := by unfold σV; infer_instance

lemma σV_inv (T' : ℝ) {g : Mat k r} (hg : g ∈ UWb k r) : (σV k r T').map (fun v => g *ᵥ v) = σV k r T' := by
  obtain ⟨μ, hμ, rfl⟩ := (UWb_iff g).1 hg
  unfold σV
  rw [Measure.map_map (mulVec_meas _) jV_meas]
  have : (fun v => embWb k r μ *ᵥ v) ∘ jV k r = jV k r ∘ (fun u => μ *ᵥ u) := by
    funext u; exact emb_mulVec_jV μ u
  rw [this, ← Measure.map_map jV_meas (mulVec_meas _), σb_inv T' hμ]

lemma UWset_inv_mem_UWb {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {h : Mat k r} (hh : h ∈ UWset k r z) :
    h⁻¹ ∈ UWb k r := by
  obtain ⟨η, hη, -, rfl⟩ := (UWset_iff hz h).1 hh
  rw [emb_inv hη]
  exact (UWb_iff _).2 ⟨η⁻¹, (UHb_inv hη).2, rfl⟩

lemma ae_weight (k : ℕ) (T T' : ℝ) :
    ∀ᵐ ζ ∂((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k T T' ζ)), T * T' < Complex.normSq ζ := by
  rw [ae_withDensity_iff (zW_meas k T T')]
  have hnull : (volume : Measure ℂ) {ζ | Complex.normSq ζ = T * T'} = 0 := by
    refine measure_mono_null ?_ (Measure.addHaar_sphere (volume : Measure ℂ) 0 (√(T * T')))
    intro ζ hζ
    have hζ' : Complex.normSq ζ = T * T' := hζ
    rw [mem_sphere_zero_iff_norm, ← hζ', Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  have : ∀ᵐ ζ ∂(volume : Measure ℂ), Complex.normSq ζ ≠ T * T' := by
    rw [ae_iff]; simpa using hnull
  filter_upwards [this] with ζ hζ h0
  by_contra hlt
  apply h0
  unfold zWeight
  rw [if_neg (fun hle => hlt (lt_of_le_of_ne hle (Ne.symm hζ)))]
  simp

lemma avg {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) {μW : Measure (Mt k r)} [SFinite μW]
    (hW : IsHaarOn (UWset k r z) μW) (T' : ℝ) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ v, ∫⁻ h, F (act h v) ∂μW ∂σV k r T' = μW Set.univ * ∫⁻ v, F v ∂σV k r T' := by
  have hFa : Measurable (fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => F (act p.2 p.1)) :=
    hF.comp act_meas'
  rw [lintegral_lintegral_swap hFa.aemeasurable]
  have hae : ∀ᵐ h : Mt k r ∂μW, h ∈ (UWset k r z : Set (Mt k r)) := by
    rw [ae_iff]; exact hW.conc
  have : ∀ᵐ h : Mt k r ∂μW, ∫⁻ v, F (act h v) ∂σV k r T' = ∫⁻ v, F v ∂σV k r T' := by
    filter_upwards [hae] with h hh
    have hi := σV_inv T' (UWset_inv_mem_UWb hz (h := Matrix.of h) hh)
    calc ∫⁻ v, F (act h v) ∂σV k r T'
        = ∫⁻ v, F v ∂((σV k r T').map (fun v => ((Matrix.of h : Mat k r)⁻¹ : Mat k r) *ᵥ v)) :=
          (lintegral_map hF (mulVec_meas _)).symm
      _ = _ := by rw [hi]
  rw [lintegral_congr_ae this, lintegral_const, mul_comm]

lemma avg_orbit {z : Fin (2 * r + k + 1) → ℂ} {μW : Measure (Mt k r)}
    (hW : IsHaarOn (UWset k r z) μW) {F : (Fin (2 * r + k + 1) → ℂ) → ℝ≥0∞} (hF : Measurable F)
    {h₁ : Mat k r} (hh₁ : h₁ ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    ∫⁻ h, F (act h v) ∂μW = ∫⁻ h, F (act h (h₁ *ᵥ v)) ∂μW := by
  have hunit := GV_unit hh₁.1
  have hF2 : Measurable (fun y : Mt k r => F (act y (h₁ *ᵥ v))) :=
    hF.comp (act_meas_left _)
  have hlc : Continuous (lmulM h₁ : Mt k r → Mt k r) := by
    unfold lmulM
    exact (continuous_const (y := h₁)).matrix_mul (continuous_id (X := Mat k r))
  have hlm : Measurable (lmulM h₁ : Mt k r → Mt k r) := hlc.measurable
  conv_rhs => rw [← hW.left h₁ hh₁]
  rw [lintegral_map hF2 hlm]
  refine lintegral_congr fun h => ?_
  rw [act_lmul hunit]

lemma herm_Hb_meas (zb : Fin (k + 1) → ℂ) : Measurable (fun u : Fin (k + 1) → ℂ => herm (Hb k) u zb) := by
  simp only [herm_Hb]
  fun_prop

lemma key (hk : 1 ≤ k) {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {μW : Measure (Mt k r)} [SFinite μW] (hz : inWb k r z) (hz' : inWb k r z') (hT : 0 < Tz k r z) (hT' : 0 < Tz k r z')
    (hsec : IsSection k r z z' μsec) (hW : IsHaarOn (UWset k r z) μW)
    (hf : AEMeasurable (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z'))
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
      c • (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW).map
        (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z')) = (μW Set.univ) • σV k r (Tz k r z') := by
  have hzz : herm (Hb k) (wbPart k r z) (wbPart k r z) = -((Tz k r z : ℝ) : ℂ) := by
    rw [← herm_jV (r := r), jV_wbPart hz, herm_self_eq]
  obtain ⟨c, hc0, hc1, hpush⟩ := σb_push hk hT hT' (wbPart k r z) hzz
  refine ⟨c, hc0, hc1, ?_⟩
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hFf : AEMeasurable (fun p : ℂ × Mt k r => F (act p.2 (embWb k r (μsec p.1) *ᵥ z')))
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW) :=
    hF.comp_aemeasurable hf
  have hΨm := hFf.lintegral_prod_right'
  rw [lintegral_smul_measure, lintegral_map' hF.aemeasurable hf, lintegral_prod _ hFf, smul_eq_mul,
    lintegral_smul_measure, smul_eq_mul, ← avg hz hW _ hF]
  have hGm : Measurable (fun v => ∫⁻ h, F (act h v) ∂μW) :=
    Measurable.lintegral_prod_right' (f := fun p : (Fin (2 * r + k + 1) → ℂ) × Mt k r => F (act p.2 p.1)) (hF.comp act_meas')
  unfold σV
  rw [lintegral_map hGm jV_meas]
  have hπm := herm_Hb_meas (wbPart k r z)
  have hgg : ∀ᵐ u ∂σb k (Tz k r z'), Tz k r z * Tz k r z' < Complex.normSq (herm (Hb k) u (wbPart k r z)) := by
    refine ae_of_ae_map (p := fun ζ => Tz k r z * Tz k r z' < Complex.normSq ζ) hπm.aemeasurable ?_
    rw [hpush]
    exact Measure.ae_smul_measure (ae_weight k _ _) c
  have hcongr : ∀ᵐ u ∂σb k (Tz k r z'), ∫⁻ h, F (act h (jV k r u)) ∂μW =
      (fun ζ => ∫⁻ h, F (act h (embWb k r (μsec ζ) *ᵥ z')) ∂μW) (herm (Hb k) u (wbPart k r z)) := by
    filter_upwards [hgg, σb_conc hT'] with u hu1 hu2
    have hζ' : herm (Hpk k r) (jV k r u) z = herm (Hb k) u (wbPart k r z) := by
      rw [← herm_jV (r := r), jV_wbPart hz]
    obtain ⟨s1, s2, s3⟩ := sec_vec hz hz' hsec hu1
    have huu : herm (Hpk k r) (jV k r u) (jV k r u) = -((Tz k r z' : ℝ) : ℂ) := by
      rw [herm_jV, herm_Hb_self, hu2]
    obtain ⟨h₁, hh₁, hx⟩ := orbit hz (inWb_jV u) s1 hT.ne' (by rw [huu, s2, herm_self_eq]) (by rw [hζ', s3])
      (by
        rw [huu, hζ']
        have : (-((Tz k r z' : ℝ) : ℂ)).re = -Tz k r z' := by simp
        rw [this]
        nlinarith)
    rw [avg_orbit hW hF hh₁ (jV k r u), hx]
  rw [lintegral_congr_ae hcongr]
  have hΨm' : AEMeasurable (fun ζ => ∫⁻ h, F (act h (embWb k r (μsec ζ) *ᵥ z')) ∂μW)
      ((σb k (Tz k r z')).map fun u => herm (Hb k) u (wbPart k r z)) := by
    rw [hpush]; exact hΨm.smul_measure c
  rw [← lintegral_map' hΨm' hπm.aemeasurable, hpush, lintegral_smul_measure, smul_eq_mul]

theorem hypInv : HypInv := by
  intro k r z z' μsec μW hk hz hz' hT hT' hsec hW m hm
  have hdef : hypMeas k r z z' μsec μW =
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW).map
        (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z')) := rfl
  rw [hdef]
  by_cases hf : AEMeasurable (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z'))
      (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW)
  swap
  · rw [Measure.map_of_not_aemeasurable hf, Measure.map_zero]
  have : IsFiniteMeasureOnCompacts μW := ⟨fun K hK => hW.finite_compact K hK⟩
  have : SigmaFinite μW := inferInstance
  obtain ⟨c, hc0, hc1, hkey⟩ := key hk hz hz' hT hT' hsec hW hf
  have hν : (((volume : Measure ℂ).withDensity fun ζ => ENNReal.ofReal (zWeight k (Tz k r z) (Tz k r z') ζ)).prod μW).map
        (fun p : ℂ × Mt k r => act p.2 (embWb k r (μsec p.1) *ᵥ z')) = c⁻¹ • ((μW Set.univ) • σV k r (Tz k r z')) := by
    rw [← hkey, smul_smul, ENNReal.inv_mul_cancel hc0 hc1, one_smul]
  rw [hν, Measure.map_smul, Measure.map_smul, σV_inv _ hm]

end PartE

end Formalism.FourierDecayAlt.P.TwoByOneBlock

namespace Formalism.FourierDecayAlt.P

theorem unipotent_weyl_properties : Formalism.FourierDecayAlt.B2.UWbFacts := TwoByOneBlock.uWbFacts

theorem weight_factorization : Formalism.FourierDecayAlt.B2.WeightFactor := TwoByOneBlock.weightFactor

theorem hyperbolic_element_inverse : Formalism.FourierDecayAlt.B2.HypInv := TwoByOneBlock.hypInv

theorem b2_rank_one_mem : Formalism.FourierDecayAlt.B2.RankOneMem := TwoByOneBlock.rankOneMem

theorem b2_rank_one_coord : Formalism.FourierDecayAlt.B2.RankOneCoord := TwoByOneBlock.rankOneCoord

theorem rank_one_integration_formula : Formalism.FourierDecayAlt.B2.RankOneInt :=
  rank_one_formula_of_parts haar_measure_unique_up_to_scalar opposite_weyl_subgroup_closed weyl_subgroup_closed weyl_subgroup_compact
    unipotent_weyl_properties b2_rank_one_mem b2_rank_one_coord hyperbolic_element_inverse

end Formalism.FourierDecayAlt.P
