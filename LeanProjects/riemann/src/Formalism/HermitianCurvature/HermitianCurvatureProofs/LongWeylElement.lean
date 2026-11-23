import Formalism.HermitianCurvature.WeylElementCommutesLevelOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentHeisenbergDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianLeviVectorBaseOrthogonal

open Matrix MeasureTheory Filter Topology
open scoped ComplexConjugate ENNReal NNReal
open Formalism.FourierDecayAlt.B2 Formalism.FourierDecayAlt.B Formalism.QuantumDeterminants Formalism.REAL

noncomputable section

namespace Formalism.FourierDecayAlt.P.LongWeylElement

section PartL

theorem conjM_cont {k r : ℕ} (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  first
    | (show Continuous fun x : Mt k r => (a * Matrix.of x * a⁻¹ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
       exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
    | (unfold conjM; fun_prop)

theorem lmulM_cont {k r : ℕ} (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  first
    | (show Continuous fun x : Mt k r => (a * Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
       exact continuous_const.matrix_mul continuous_id)
    | (unfold lmulM; fun_prop)

theorem rmulF_cont {n : ℕ} (a : Matrix (Fin n) (Fin n) ℂ) : Continuous (rmulF a) := by
  first
    | (show Continuous fun x : Fin n → Fin n → ℂ => (Matrix.of x * a : Matrix (Fin n) (Fin n) ℂ)
       exact continuous_id.matrix_mul continuous_const)
    | (unfold rmulF; fun_prop)

def mid (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : Prop := 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1

theorem mid_levPos (k r' : ℕ) (s : Fin (2 * r' + k + 1)) : mid k r' (levPos k 1 r' s) := by
  have := s.isLt
  show 1 ≤ s.val + 1 ∧ s.val + 1 < 2 * r' + k + 1 + 1
  constructor <;> omega

theorem mid_iff (k r' : ℕ) (p : Fin (2 * (1 + r') + k + 1)) : mid k r' p ↔ p ∈ Set.range (levPos k 1 r') := by
  constructor
  · intro h
    have h' : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 := h
    refine ⟨⟨p.val - 1, by omega⟩, Fin.ext ?_⟩
    show p.val - 1 + 1 = p.val
    omega
  · rintro ⟨s, rfl⟩
    exact mid_levPos k r' s

theorem levPos_inj (k r' : ℕ) : Function.Injective (levPos k 1 r') := by
  intro a b h
  have h' : a.val + 1 = b.val + 1 := congrArg Fin.val h
  exact Fin.ext (by omega)

theorem lev_mm (k r' : ℕ) (g : Mat k r') (s t : Fin (2 * r' + k + 1)) :
    ιLev k 1 r' g (levPos k 1 r' s) (levPos k 1 r' t) = g s t := by
  have hs := s.isLt
  have ht := t.isLt
  have h3 : s.val ≤ 2 * r' + k := by omega
  have h4 : t.val ≤ 2 * r' + k := by omega
  simp [ιLev, levPos, h3, h4]

theorem lev_mn (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : mid k r' p) (hq : ¬ mid k r' q) :
    ιLev k 1 r' g p q = 0 := by
  have hp' : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1 := hp
  have hq' : ¬ (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) := hq
  simp only [ιLev, dif_pos hp', dif_neg hq']

theorem lev_n (k r' : ℕ) (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : ¬ mid k r' p) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  have hp' : ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1) := hp
  simp only [ιLev, dif_neg hp']

theorem lev_one (k r' : ℕ) : ιLev k 1 r' 1 = 1 := by
  ext p q
  simp only [ιLev, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem lev_mul (k r' : ℕ) (g h : Mat k r') : ιLev k 1 r' (g * h) = ιLev k 1 r' g * ιLev k 1 r' h := by
  first
    | exact Formalism.FourierDecayAlt.P.B2x2.lev_mul k r' g h
    | exact (Formalism.FourierDecayAlt.P.B2x5.lev_mul k r' g h).symm

def blk (k r' : ℕ) (x : Mt k (1 + r')) : Mt k r' := fun s t => x (levPos k 1 r' s) (levPos k 1 r' t)

theorem blk_cont (k r' : ℕ) : Continuous (blk k r') := by
  first
    | (unfold blk; fun_prop)
    | exact continuous_pi fun s => continuous_pi fun t =>
        (continuous_apply (levPos k 1 r' t)).comp (continuous_apply (levPos k 1 r' s))

theorem blk_lev (k r' : ℕ) (x : Mt k r') : blk k r' (levM k r' x) = x := by
  funext s t
  exact lev_mm k r' (Matrix.of x) s t

theorem levM_cont (k r' : ℕ) : Continuous (levM k r') := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
  show Continuous fun x : Mt k r' => ιLev k 1 r' (Matrix.of x) p q
  simp only [ιLev]
  split_ifs <;> first
    | exact continuous_const
    | fun_prop
    | exact (continuous_apply _).comp (continuous_apply _)

end PartL

section PartW

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

def iZ (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨0, by omega⟩
def iL (k r' : ℕ) : Fin (2 * (1 + r') + k + 1) := ⟨2 * (1 + r') + k, by omega⟩

lemma weight_zero_not_pos_det (c : ℂ) (i q : Fin (2 * (1 + r') + k + 1)) (h1 : ¬(i.val = 0 ∧ q.val = 2 * (1 + r') + k))
    (h2 : ¬(i.val = 2 * (1 + r') + k ∧ q.val = 0)) (h3 : ¬(i.val = q.val ∧ 0 < i.val ∧ i.val < 2 * (1 + r') + k)) :
    w0 k r' c i q = 0 := by
  simp only [w0]
  rw [if_neg h1, if_neg h2, if_neg]
  rintro ⟨h, h'⟩
  exact h3 ⟨congrArg Fin.val h, h'⟩

private lemma w0_apply_eq_ite_first_index (c : ℂ) (i m : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c i m = if i.val = 0 then (if m = iL k r' then (star c)⁻¹ else 0)
      else if i.val = 2 * (1 + r') + k then (if m = iZ k r' then c else 0) else (if m = i then 1 else 0) := by
  have hi := i.isLt
  have hm := m.isLt
  simp only [w0, iL, iZ, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma weylMatrix_mul_apply (c : ℂ) (A : Mat k (1 + r')) (i j : Fin (2 * (1 + r') + k + 1)) :
    (w0 k r' c * A) i j = if i.val = 0 then (star c)⁻¹ * A (iL k r') j
      else if i.val = 2 * (1 + r') + k then c * A (iZ k r') j else A i j := by
  rw [Matrix.mul_apply]
  simp only [w0_apply_eq_ite_first_index]
  split_ifs <;> simp

private lemma w0_apply_eq_ite_col (c : ℂ) (m j : Fin (2 * (1 + r') + k + 1)) :
    w0 k r' c m j = if j.val = 0 then (if m = iL k r' then c else 0)
      else if j.val = 2 * (1 + r') + k then (if m = iZ k r' then (star c)⁻¹ else 0) else (if m = j then 1 else 0) := by
  have hj := j.isLt
  have hm := m.isLt
  simp only [w0, iL, iZ, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma mul_long_weyl_element_apply (c : ℂ) (A : Mat k (1 + r')) (i j : Fin (2 * (1 + r') + k + 1)) :
    (A * w0 k r' c) i j = if j.val = 0 then A i (iL k r') * c
      else if j.val = 2 * (1 + r') + k then A i (iZ k r') * (star c)⁻¹ else A i j := by
  rw [Matrix.mul_apply]
  simp only [w0_apply_eq_ite_col]
  split_ifs <;> simp

lemma lev_out_row (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : p.val = 0 ∨ p.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  apply lev_n
  show ¬ (1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)
  omega

lemma lev_out_col (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hq : q.val = 0 ∨ q.val = 2 * (1 + r') + k) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  have hq' : ¬ mid k r' q := by
    show ¬ (1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1)
    omega
  by_cases hp : mid k r' p
  · rw [lev_mn k r' g p q hp hq', if_neg]
    rintro rfl
    exact hq' hp
  · exact lev_n k r' g p q hp

lemma lev_mid (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hp : 1 ≤ p.val ∧ p.val < 2 * r' + k + 1 + 1)
    (hq : 1 ≤ q.val ∧ q.val < 2 * r' + k + 1 + 1) :
    ιLev k 1 r' g p q = g ⟨p.val - 1, by omega⟩ ⟨q.val - 1, by omega⟩ := by
  simp only [ιLev, dif_pos hp, dif_pos hq]

theorem t_w0comm : WeylElementCommutesLevelOne := by
  intro k r' c g
  ext i j
  rw [weylMatrix_mul_apply, mul_long_weyl_element_apply, lev_out_row g (iL k r') j (Or.inr rfl), lev_out_row g (iZ k r') j (Or.inl rfl),
    lev_out_col g i (iL k r') (Or.inr rfl), lev_out_col g i (iZ k r') (Or.inl rfl)]
  have hi := i.isLt
  have hj := j.isLt
  by_cases hj0 : j.val = 0 ∨ j.val = 2 * (1 + r') + k
  · rw [lev_out_col g i j hj0]
    simp only [iL, iZ, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
  · by_cases hi0 : i.val = 0 ∨ i.val = 2 * (1 + r') + k
    · rw [lev_out_row g i j hi0]
      simp only [iL, iZ, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
    · simp only [iL, iZ, Fin.ext_iff, Fin.val_mk]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)

private lemma matrix_apply_congr_of_eq {n m : ℕ} (μ : Matrix (Fin n) (Fin m) ℂ) {a b c d : ℕ} {ha : a < n} {hb : b < m}
    {hc : c < n} {hd : d < m} (h1 : a = c) (h2 : b = d) : μ ⟨a, ha⟩ ⟨b, hb⟩ = μ ⟨c, hc⟩ ⟨d, hd⟩ := by
  subst h1
  subst h2
  rfl

set_option maxHeartbeats 800000 in

theorem t_bigcellrec : BigCellRec := by
  intro k r' c μ
  ext i j
  rw [weylMatrix_mul_apply]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h0 : i.val = 0
  · rw [if_pos h0, lev_out_row _ (iL k r') j (Or.inr rfl)]
    simp only [bigCell, esI, iL, a0, Fin.ext_iff, Fin.val_mk, h0]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
  · by_cases hL : i.val = 2 * (1 + r') + k
    · rw [if_neg h0, if_pos hL, lev_out_row _ (iZ k r') j (Or.inl rfl)]
      simp only [bigCell, esI, iZ, a0, Fin.ext_iff, Fin.val_mk, hL]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
    · rw [if_neg h0, if_neg hL]
      have hmi : 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1 := by omega
      by_cases hmj : 1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1
      · rw [lev_mid _ i j hmi hmj]
        dsimp only [bigCell, esI, Fin.val_mk]
        by_cases hA : j.val < 1 + r'
        · have hA' : j.val - 1 < r' := by omega
          simp only [hA, hA', dite_true]
          simp only [Fin.ext_iff, Fin.val_mk]
          split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
        · have hA' : ¬ (j.val - 1 < r') := by omega
          by_cases hB : j.val ≤ 1 + r' + k
          · have hB' : j.val - 1 ≤ r' + k := by omega
            simp only [hA, hA', hB, hB', dite_true, dite_false]
            split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
          · have hB' : ¬ (j.val - 1 ≤ r' + k) := by omega
            simp only [hA, hA', hB, hB', dite_true, dite_false]
            split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))
      · rw [lev_mn k r' _ i j hmi hmj]
        simp only [bigCell, esI, Fin.ext_iff, Fin.val_mk]
        split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, mul_zero]; done) | (exact matrix_apply_congr_of_eq _ (by omega) (by omega)) | (simp only [mul_one]; congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega)) | (congr 3 <;> (try dsimp only [Fin.val_mk, Fin.coe_natAdd] at *) <;> first | omega | (ext; simp only [Fin.coe_natAdd, Fin.val_mk]; omega))

end PartW

section PartU

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r' : ℕ}

lemma not_mid_iff (p : Fin (2 * (1 + r') + k + 1)) : ¬ mid k r' p ↔ p = iZ k r' ∨ p = iL k r' := by
  have hp := p.isLt
  simp only [mid, iZ, iL, Fin.ext_iff, Fin.val_mk]
  constructor <;> intro h <;> omega

lemma lev_col_n (g : Mat k r') (p q : Fin (2 * (1 + r') + k + 1)) (hq : ¬ mid k r' q) :
    ιLev k 1 r' g p q = if p = q then 1 else 0 := by
  by_cases hp : mid k r' p
  · rw [lev_mn k r' g p q hp hq, if_neg]
    rintro rfl
    exact hq hp
  · exact lev_n k r' g p q hp

lemma lev_conjT (g : Mat k r') : (ιLev k 1 r' g)ᴴ = ιLev k 1 r' gᴴ := by
  ext p q
  simp only [Matrix.conjTranspose_apply, ιLev, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega) | (simp; done)

lemma lev_inj {g h : Mat k r'} (e : ιLev k 1 r' g = ιLev k 1 r' h) : g = h := by
  ext s t
  have := congrFun (congrFun e (levPos k 1 r' s)) (levPos k 1 r' t)
  rwa [lev_mm, lev_mm] at this

lemma Hpk_eq (k r' : ℕ) : Hpk k (1 + r') = w0 k r' 1 * ιLev k 1 r' (Hpk k r') := by
  ext i j
  rw [weylMatrix_mul_apply]
  simp only [star_one, inv_one, one_mul]
  have hi := i.isLt
  have hj := j.isLt
  by_cases h0 : i.val = 0
  · rw [if_pos h0, lev_out_row (Hpk k r') (iL k r') j (Or.inr rfl)]
    simp only [Hpk, iL, Fin.ext_iff, Fin.val_mk, h0]
    split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
  · by_cases hL : i.val = 2 * (1 + r') + k
    · rw [if_neg h0, if_pos hL, lev_out_row (Hpk k r') (iZ k r') j (Or.inl rfl)]
      simp only [Hpk, iZ, Fin.ext_iff, Fin.val_mk, hL]
      split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)
    · rw [if_neg h0, if_neg hL]
      have hmi : mid k r' i := by
        show 1 ≤ i.val ∧ i.val < 2 * r' + k + 1 + 1
        omega
      by_cases hmj : mid k r' j
      · obtain ⟨s, rfl⟩ := (mid_iff k r' i).1 hmi
        obtain ⟨t, rfl⟩ := (mid_iff k r' j).1 hmj
        rw [lev_mm, Formalism.FourierDecayAlt.P.B2x4.Hpk_levPos]
      · rw [lev_col_n (Hpk k r') i j hmj, if_neg (fun h => by subst h; exact hmj hmi)]
        have hj' : ¬ (1 ≤ j.val ∧ j.val < 2 * r' + k + 1 + 1) := hmj
        simp only [Hpk, Fin.ext_iff]
        split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)

lemma long_weyl_element_sq_one (k r' : ℕ) : w0 k r' 1 * w0 k r' 1 = 1 := by
  ext i j
  rw [weylMatrix_mul_apply]
  simp only [w0_apply_eq_ite_first_index]
  have hi := i.isLt
  have hj := j.isLt
  simp only [iL, iZ, Matrix.one_apply, Fin.ext_iff, Fin.val_mk, star_one, inv_one, one_mul, true_and, and_true]
  split_ifs <;> first | rfl | (exfalso; omega) | (simp only [mul_one, one_mul, mul_zero, zero_mul]; done) | (simp; done) | (simp_all; done)

lemma lev_UH (g : Mat k r') : ιLev k 1 r' g ∈ GV k (1 + r') ↔ g ∈ GV k r' := by
  show (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = Hpk k (1 + r') ↔ gᴴ * Hpk k r' * g = Hpk k r'
  have key : (ιLev k 1 r' g)ᴴ * Hpk k (1 + r') * ιLev k 1 r' g = w0 k r' 1 * ιLev k 1 r' (gᴴ * Hpk k r' * g) := by
    rw [lev_conjT, Hpk_eq, ← Matrix.mul_assoc, ← t_w0comm k r' 1 gᴴ]
    simp only [Matrix.mul_assoc, ← lev_mul]
  rw [key, Hpk_eq]
  constructor
  · intro h
    apply lev_inj
    have := congrArg (fun M => w0 k r' 1 * M) h
    simpa only [← Matrix.mul_assoc, long_weyl_element_sq_one, Matrix.one_mul] using this
  · intro h
    rw [h]

lemma col_eq {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j p : Fin m) : (g *ᵥ bvec j) p = g p j := by
  first
    | (simp [bvec, Matrix.mulVec_single]; done)
    | (simp [bvec, Matrix.mulVec, dotProduct, Pi.single_apply]; done)
    | simp only [bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]

lemma fix_iff {m : ℕ} (g : Matrix (Fin m) (Fin m) ℂ) (j : Fin m) :
    g *ᵥ bvec j = bvec j ↔ ∀ p, g p j = if p = j then 1 else 0 := by
  constructor
  · intro h p
    have := congrFun h p
    rw [col_eq] at this
    rw [this]
    simp [bvec, Pi.single_apply]
  · intro h
    funext p
    rw [col_eq, h p]
    simp [bvec, Pi.single_apply]

lemma lev_col_iff (g : Mat k r') (t : Fin (2 * r' + k + 1)) :
    (∀ p, ιLev k 1 r' g p (levPos k 1 r' t) = if p = levPos k 1 r' t then 1 else 0) ↔
      ∀ s, g s t = if s = t then 1 else 0 := by
  constructor
  · intro h s
    have := h (levPos k 1 r' s)
    rw [lev_mm] at this
    rw [this]
    exact if_congr (levPos_inj k r').eq_iff rfl rfl
  · intro h p
    by_cases hp : mid k r' p
    · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
      rw [lev_mm, h s]
      exact if_congr (levPos_inj k r').eq_iff.symm rfl rfl
    · exact lev_n k r' g p _ hp

lemma eI_zero : eI k (1 + r') (a0 r') = iZ k r' := rfl

lemma esI_zero : esI k (1 + r') (a0 r') = iL k r' := rfl

lemma eI_succ (a : Fin r') : eI k (1 + r') (Fin.natAdd 1 a) = levPos k 1 r' (eI k r' a) := by
  apply Fin.ext
  show 1 + a.val = a.val + 1
  omega

lemma esI_succ (a : Fin r') : esI k (1 + r') (Fin.natAdd 1 a) = levPos k 1 r' (esI k r' a) := by
  have := a.isLt
  apply Fin.ext
  show 2 * (1 + r') + k - (1 + a.val) = 2 * r' + k - a.val + 1
  omega

lemma fin_cases' (a : Fin (1 + r')) : a = a0 r' ∨ ∃ a' : Fin r', a = Fin.natAdd 1 a' := by
  have := a.isLt
  by_cases h : a.val = 0
  · left
    exact Fin.ext h
  · right
    refine ⟨⟨a.val - 1, by omega⟩, Fin.ext ?_⟩
    show a.val = 1 + (a.val - 1)
    omega

lemma Hpk_Z (q : Fin (2 * (1 + r') + k + 1)) : Hpk k (1 + r') (iZ k r') q = if q = iL k r' then 1 else 0 := by
  have hq := q.isLt
  simp only [Hpk, iZ, iL, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma Hpk_L (q : Fin (2 * (1 + r') + k + 1)) : Hpk k (1 + r') (iL k r') q = if q = iZ k r' then 1 else 0 := by
  have hq := q.isLt
  simp only [Hpk, iZ, iL, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma row_of_col {m : ℕ} (g H : Matrix (Fin m) (Fin m) ℂ) (i₀ j : Fin m)
    (hc : ∀ p, g p i₀ = if p = i₀ then 1 else 0) : (gᴴ * H * g) i₀ j = (H * g) i₀ j := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Finset.sum_eq_single i₀]
  · rw [Matrix.conjTranspose_apply, hc i₀, if_pos rfl, star_one, one_mul]
  · intro m _ hm
    rw [Matrix.conjTranspose_apply, hc m, if_neg hm, star_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem uWbRec : Formalism.FourierDecayAlt.B2.UWbRec := by
  intro k r'
  ext g
  constructor
  · rintro ⟨hG, hfix⟩
    have cZ : ∀ p, g p (iZ k r') = if p = iZ k r' then 1 else 0 := (fix_iff g _).1 (hfix (a0 r')).1
    have cL : ∀ p, g p (iL k r') = if p = iL k r' then 1 else 0 := (fix_iff g _).1 (hfix (a0 r')).2
    have hGe : gᴴ * Hpk k (1 + r') * g = Hpk k (1 + r') := hG
    have rL : ∀ q, g (iL k r') q = if q = iL k r' then 1 else 0 := by
      intro q
      have h1 := row_of_col g (Hpk k (1 + r')) (iZ k r') q cZ
      rw [hGe, Matrix.mul_apply] at h1
      first
        | (simp only [Hpk_Z, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
            ite_true] at h1
           exact h1.symm)
        | (simp [Hpk_Z] at h1
           exact h1.symm)
    have rZ : ∀ q, g (iZ k r') q = if q = iZ k r' then 1 else 0 := by
      intro q
      have h1 := row_of_col g (Hpk k (1 + r')) (iL k r') q cL
      rw [hGe, Matrix.mul_apply] at h1
      first
        | (simp only [Hpk_L, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ,
            ite_true] at h1
           exact h1.symm)
        | (simp [Hpk_L] at h1
           exact h1.symm)
    have hg : g = ιLev k 1 r' (Matrix.of (blk k r' g)) := by
      ext p q
      by_cases hp : mid k r' p
      · by_cases hq : mid k r' q
        · obtain ⟨s, rfl⟩ := (mid_iff k r' p).1 hp
          obtain ⟨t, rfl⟩ := (mid_iff k r' q).1 hq
          rw [lev_mm]
          rfl
        · rw [lev_mn k r' _ p q hp hq]
          rcases (not_mid_iff q).1 hq with rfl | rfl
          · rw [cZ, if_neg]
            rintro rfl
            exact hq hp
          · rw [cL, if_neg]
            rintro rfl
            exact hq hp
      · rw [lev_n k r' _ p q hp]
        rcases (not_mid_iff p).1 hp with rfl | rfl
        · rw [rZ]
          exact if_congr eq_comm rfl rfl
        · rw [rL]
          exact if_congr eq_comm rfl rfl
    refine ⟨Matrix.of (blk k r' g), ⟨?_, ?_⟩, hg.symm⟩
    · rw [← lev_UH, ← hg]
      exact hG
    · intro a
      constructor
      · have := (hfix (Fin.natAdd 1 a)).1
        rw [eI_succ, fix_iff, hg, lev_col_iff] at this
        exact (fix_iff _ _).2 this
      · have := (hfix (Fin.natAdd 1 a)).2
        rw [esI_succ, fix_iff, hg, lev_col_iff] at this
        exact (fix_iff _ _).2 this
  · rintro ⟨g', ⟨hG', hfix'⟩, rfl⟩
    refine ⟨(lev_UH g').2 hG', fun a => ?_⟩
    rcases fin_cases' a with rfl | ⟨a', rfl⟩
    · constructor
      · rw [fix_iff]
        intro p
        exact lev_col_n g' p _ (by rw [not_mid_iff]; exact Or.inl rfl)
      · rw [fix_iff]
        intro p
        exact lev_col_n g' p _ (by rw [not_mid_iff]; exact Or.inr rfl)
    · constructor
      · rw [eI_succ, fix_iff, lev_col_iff]
        exact (fix_iff g' _).1 (hfix' a').1
      · rw [esI_succ, fix_iff, lev_col_iff]
        exact (fix_iff g' _).1 (hfix' a').2

end PartU

section PartF

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

variable {k r : ℕ}

abbrev midW (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val ≤ r + k

lemma emb_out_col (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hj : ¬ midW k r j) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  have hj' : ¬ (r ≤ j.val ∧ j.val ≤ r + k) := hj
  simp only [embWb, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma emb_out_row (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : ¬ midW k r q) :
    embWb k r μ q j = if q = j then 1 else 0 := by
  have hq' : ¬ (r ≤ q.val ∧ q.val ≤ r + k) := hq
  simp only [embWb, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma emb_mid (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (q j : Fin (2 * r + k + 1)) (hq : midW k r q) (hj : midW k r j) :
    embWb k r μ q j = μ ⟨q.val - r, by have := hq; omega⟩ ⟨j.val - r, by have := hj; omega⟩ := by
  simp only [embWb, dif_pos (show (r ≤ q.val ∧ q.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) from ⟨hq, hj⟩)]

lemma bc_mid_col (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1)) (hj : midW k r j) :
    bigCell k r c μ i j = if hi : midW k r i then μ ⟨i.val - r, by have := hi; omega⟩ ⟨j.val - r, by have := hj; omega⟩
      else 0 := by
  have h1 := hj.1
  have h2 := hj.2
  simp only [bigCell, dif_neg (show ¬ j.val < r by omega), dif_pos h2] <;> rfl

lemma bc_mid_row_out (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : midW k r i) (hj : ¬ midW k r j) : bigCell k r c μ i j = 0 := by
  have h1 := hi.1
  have h2 := hi.2
  have hj' : ¬ (r ≤ j.val ∧ j.val ≤ r + k) := hj
  simp only [bigCell, esI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma bc_out_col (c : Fin r → ℂ) (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hj : ¬ midW k r j) : bigCell k r c μ i j = bigCell k r c ν i j := by
  have hj' : ¬ (r ≤ j.val ∧ j.val ≤ r + k) := hj
  simp only [bigCell]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma bc_out_row (c : Fin r → ℂ) (μ ν : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i j : Fin (2 * r + k + 1))
    (hi : ¬ midW k r i) : bigCell k r c μ i j = bigCell k r c ν i j := by
  have hi' : ¬ (r ≤ i.val ∧ i.val ≤ r + k) := hi
  simp only [bigCell]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma bc_one_mid (c : Fin r → ℂ) (i j : Fin (2 * r + k + 1)) (hi : midW k r i) (hj : midW k r j) :
    bigCell k r c 1 i j = if i = j then 1 else 0 := by
  have h1 := hi.1
  have h2 := hi.2
  have h3 := hj.1
  have h4 := hj.2
  simp only [bigCell, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem t_bigcellfactor : BigCellFactor := by
  intro k r c μ
  constructor
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hj : midW k r j
    · rw [Finset.sum_eq_single i]
      · by_cases hi : midW k r i
        · rw [bc_one_mid c i i hi hi, if_pos (rfl : i = i), one_mul, emb_mid μ i j hi hj, bc_mid_col c μ i j hj,
            dif_pos hi]
        · rw [emb_out_row μ i j hi, if_neg (fun h => by subst h; exact hi hj), mul_zero, bc_mid_col c μ i j hj,
            dif_neg hi]
      · intro m _ hm
        by_cases hm' : midW k r m
        · by_cases hi : midW k r i
          · rw [bc_one_mid c i m hi hm', if_neg (Ne.symm hm), zero_mul]
          · rw [bc_mid_col c 1 i m hm', dif_neg hi, zero_mul]
        · rw [emb_out_row μ m j hm', if_neg (fun h => by subst h; exact hm' hj), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single j]
      · rw [emb_out_col μ j j hj, if_pos (rfl : j = j), mul_one, bc_out_col c 1 μ i j hj]
      · intro m _ hm
        rw [emb_out_col μ m j hj, if_neg hm, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · ext i j
    rw [Matrix.mul_apply]
    by_cases hj : midW k r j
    · rw [Finset.sum_eq_single j]
      · rw [bc_one_mid c j j hj hj, if_pos (rfl : j = j), mul_one, bc_mid_col c μ i j hj]
        by_cases hi : midW k r i
        · rw [emb_mid μ i j hi hj, dif_pos hi]
        · rw [emb_out_row μ i j hi, dif_neg hi, if_neg (fun h => by subst h; exact hi hj)]
      · intro m _ hm
        by_cases hm' : midW k r m
        · rw [bc_one_mid c m j hm' hj, if_neg hm, mul_zero]
        · rw [bc_mid_col c 1 m j hj, dif_neg hm', mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · rw [Finset.sum_eq_single i]
      · by_cases hi : midW k r i
        · rw [bc_mid_row_out c 1 i j hi hj, mul_zero, bc_mid_row_out c μ i j hi hj]
        · rw [emb_out_col μ i i hi, if_pos (rfl : i = i), one_mul, bc_out_col c 1 μ i j hj]
      · intro m _ hm
        by_cases hm' : midW k r m
        · rw [bc_mid_row_out c 1 m j hm' hj, mul_zero]
        · rw [emb_out_col μ i m hm', if_neg (Ne.symm hm), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h

end PartF

section PartG

section General
variable {α α' β β' : Type*} [MeasurableSpace α] [MeasurableSpace α'] [MeasurableSpace β] [MeasurableSpace β']

theorem swap4 (μ₁ : Measure α) (ν₁ : Measure β) (μ₂ : Measure α') (ν₂ : Measure β') [SFinite μ₁] [SFinite ν₁]
    [SFinite μ₂] [SFinite ν₂] (F : (α × β) × (α' × β') → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ u, F u ∂((μ₁.prod ν₁).prod (μ₂.prod ν₂)) =
      ∫⁻ p : (α × α') × (β × β'), F ((p.1.1, p.2.1), (p.1.2, p.2.2)) ∂((μ₁.prod μ₂).prod (ν₁.prod ν₂)) := by
  have m1 : Measurable fun p : (α × α') × (β × β') => F ((p.1.1, p.2.1), (p.1.2, p.2.2)) :=
    hF.comp (by fun_prop)
  have e1 : ∀ x : α × β, ∫⁻ y, F (x, y) ∂(μ₂.prod ν₂) = ∫⁻ a', ∫⁻ b', F (x, (a', b')) ∂ν₂ ∂μ₂ := by
    intro x
    exact lintegral_prod (fun y : α' × β' => F (x, y)) (hF.comp (by fun_prop)).aemeasurable
  have e2 : ∀ x : α × α', ∫⁻ y, F ((x.1, y.1), (x.2, y.2)) ∂(ν₁.prod ν₂) =
      ∫⁻ b, ∫⁻ b', F ((x.1, b), (x.2, b')) ∂ν₂ ∂ν₁ := by
    intro x
    exact lintegral_prod (fun y : β × β' => F ((x.1, y.1), (x.2, y.2))) (hF.comp (by fun_prop)).aemeasurable
  have m2 : Measurable fun x : α × β => ∫⁻ a', ∫⁻ b', F (x, (a', b')) ∂ν₂ ∂μ₂ :=
    ((hF.comp (by fun_prop : Measurable fun q : ((α × β) × α') × β' => (q.1.1, (q.1.2, q.2)))).lintegral_prod_right').lintegral_prod_right'
  have m3 : Measurable fun x : α × α' => ∫⁻ b, ∫⁻ b', F ((x.1, b), (x.2, b')) ∂ν₂ ∂ν₁ :=
    ((hF.comp (by fun_prop : Measurable fun q : ((α × α') × β) × β' => ((q.1.1.1, q.1.2), (q.1.1.2, q.2)))).lintegral_prod_right').lintegral_prod_right'
  rw [lintegral_prod _ hF.aemeasurable, lintegral_prod _ m1.aemeasurable]
  try dsimp only
  simp_rw [e1, e2]
  rw [lintegral_prod _ m2.aemeasurable, lintegral_prod _ m3.aemeasurable]
  try dsimp only
  refine lintegral_congr fun a => ?_
  have m4 : Measurable (Function.uncurry fun (b : β) (a' : α') => ∫⁻ b', F ((a, b), (a', b')) ∂ν₂) :=
    (hF.comp (by fun_prop : Measurable fun q : (β × α') × β' => ((a, q.1.1), (q.1.2, q.2)))).lintegral_prod_right'
  exact lintegral_lintegral_swap m4.aemeasurable

end General

def splitC (r' : ℕ) (c : Fin (1 + r') → ℂ) : ℂ × (Fin r' → ℂ) := (c (a0 r'), fun a => c (Fin.natAdd 1 a))

def splitE (r' : ℕ) : (Fin (1 + r') → ℂ) ≃ᵐ ℂ × (Fin r' → ℂ) :=
  (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (finCongr (Nat.add_comm r' 1))).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ => ℂ) 0)

theorem splitE_mp (r' : ℕ) : MeasurePreserving (splitE r') volume volume := by
  first
    | exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).comp
        (MeasurePreserving.symm _ (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℂ) (finCongr (Nat.add_comm r' 1))))
    | exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ => ℂ) 0).comp
        ((MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ => ℂ) (finCongr (Nat.add_comm r' 1))).symm _)

theorem splitE_eq (r' : ℕ) : (splitE r' : (Fin (1 + r') → ℂ) → ℂ × (Fin r' → ℂ)) = splitC r' := by
  funext c
  refine Prod.ext ?_ ?_
  · show c _ = c (a0 r')
    congr 1
    all_goals (ext; simp [a0])
  · funext a
    show c _ = c (Fin.natAdd 1 a)
    congr 1
    all_goals (ext; simp [Fin.succAbove_zero, Fin.coe_natAdd, add_comm])

theorem lint_split (r' : ℕ) (G : ℂ × (Fin r' → ℂ) → ℝ≥0∞) :
    ∫⁻ c : Fin (1 + r') → ℂ, G (splitC r' c) = ∫⁻ p : ℂ × (Fin r' → ℂ), G p := by
  rw [← splitE_eq r']
  exact (splitE_mp r').lintegral_comp_emb (splitE r').measurableEmbedding G

theorem cWeight_rec (k r' : ℕ) (c : Fin (1 + r') → ℂ) :
    cWeight k (1 + r') c = ‖c (a0 r')‖ ^ (2 * (2 * r' + k + 1)) * cWeight k r' (fun a => c (Fin.natAdd 1 a)) := by
  simp only [cWeight]
  rw [Fin.prod_univ_add, Fin.prod_univ_one]
  have e : Fin.castAdd r' (0 : Fin 1) = a0 r' := Fin.ext (by simp [a0])
  rw [e]
  congr 1
  · congr 1
    simp only [Mdim, a0, Fin.val_mk]
    omega
  · refine Finset.prod_congr rfl fun b _ => ?_
    congr 1
    simp only [Mdim, Fin.coe_natAdd]
    omega

end PartG

section PartM

variable {k r r' : ℕ}

theorem sf {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) : SigmaFinite μ := by
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => h.finite_compact K hK⟩
  first
    | infer_instance
    | exact sigmaFinite_of_locallyFinite
    | exact MeasureTheory.sigmaFinite_of_locallyFinite

theorem haar_ae {U : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn U μ) :
    ∀ᵐ g ∂μ, (Matrix.of g : Mat k r) ∈ U := by
  first
    | exact ae_iff.2 h.2.1
    | exact ae_iff.2 h.2.2.1
    | exact ae_iff.2 h.2.2.2
    | exact ae_iff.2 h.2.2.2.1
    | exact ae_iff.2 h.2.2.2.2
    | exact ae_iff.2 h.2.2.2.2.1
    | exact ae_iff.2 h.1
    | exact ae_iff.2 (by simpa using h.2.1)
    | exact ae_iff.2 (by simpa using h.2.2.1)

def adjF (x : Mt k r) : Mt k r := (Matrix.of x : Mat k r).adjugate
def detF (x : Mt k r) : ℂ := (Matrix.of x : Mat k r).det

theorem detF_cont : Continuous (detF (k := k) (r := r)) := by
  first
    | exact Continuous.matrix_det continuous_id
    | (unfold detF; fun_prop)
theorem adjF_cont : Continuous (adjF (k := k) (r := r)) := by
  first
    | exact Continuous.matrix_adjugate continuous_id
    | (unfold adjF; fun_prop)

theorem invM_smul : (invM : Mt k r → Mt k r) = fun x => (detF x)⁻¹ • adjF x := by
  funext x
  first
    | (show ((Matrix.of x : Mat k r)⁻¹ : Mat k r) = ((Matrix.of x : Mat k r).det)⁻¹ • (Matrix.of x : Mat k r).adjugate
       rw [Matrix.inv_def, Ring.inverse_eq_inv'])
    | (simp only [invM, detF, adjF]
       rw [Matrix.inv_def, Ring.inverse_eq_inv']
       rfl)

theorem invM_meas : Measurable (invM : Mt k r → Mt k r) := by
  rw [invM_smul]
  first
    | exact (detF_cont.measurable.inv).smul adjF_cont.measurable
    | exact (measurable_inv.comp detF_cont.measurable).smul adjF_cont.measurable
    | fun_prop

theorem mulM_cont : Continuous (mulM : Mt k r × Mt k r → Mt k r) := by
  first
    | (show Continuous fun p : Mt k r × Mt k r => (Matrix.of p.1 * Matrix.of p.2 : Mat k r)
       exact continuous_fst.matrix_mul continuous_snd)
    | (unfold mulM; fun_prop)

theorem mulM_meas : Measurable (mulM : Mt k r × Mt k r → Mt k r) := by
  exact mulM_cont.measurable

theorem mm_meas {α : Type*} [MeasurableSpace α] {A B : α → Mt k r} (hA : Measurable A) (hB : Measurable B) :
    Measurable (fun t => mulM (A t, B t)) := by
  first
    | exact mulM_meas.comp (hA.prodMk hB)
    | exact mulM_meas.comp (hA.prod_mk hB)

theorem levM_meas : Measurable (levM k r') := by
  exact (levM_cont k r').measurable

lemma continuous_herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) :
    Continuous fun p : (ι → ℂ) × (ι → ℂ) => herm H p.1 p.2 := by
  first
    | (unfold herm; fun_prop)
    | exact (continuous_snd.star).matrix_dotProduct (continuous_const.matrix_mulVec continuous_fst)
    | (simp only [herm, dotProduct, Matrix.mulVec]; fun_prop)

lemma continuous_lift (k r' : ℕ) : Continuous (liftVec k 1 r') := by
  refine continuous_pi fun p => ?_
  show Continuous fun v : Fin (2 * r' + k + 1) → ℂ => liftVec k 1 r' v p
  simp only [liftVec]
  split_ifs <;> first | exact continuous_const | exact continuous_apply _ | fun_prop

lemma continuous_hb (k r' : ℕ) : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := by
  have h1 : Continuous fun x : HPar k r' => herm (Hpk k r') x.1 x.1 := by
    first
      | exact (continuous_herm (Hpk k r')).comp (continuous_fst.prodMk continuous_fst)
      | exact (continuous_herm (Hpk k r')).comp (continuous_fst.prod_mk continuous_fst)
  unfold hb
  first
    | fun_prop
    | exact (Complex.continuous_ofReal.comp ((Complex.continuous_re.comp h1).neg.div_const 2)).add
        ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)

lemma continuous_heis0 (k r' : ℕ) : Continuous (heis0 k r') := by
  have hv : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 := (continuous_lift k r').comp continuous_fst
  have hb' : Continuous fun x : HPar k r' => hb k r' x.1 x.2 := continuous_hb k r'
  have hh : ∀ j, Continuous fun x : HPar k r' => herm (Hpk k (1 + r')) (bvec j) (liftVec k 1 r' x.1) := by
    intro j
    first
      | exact (continuous_herm _).comp (continuous_const.prodMk hv)
      | exact (continuous_herm _).comp (continuous_const.prod_mk hv)
  refine continuous_pi fun p => continuous_pi fun q => ?_
  simp only [heis0, heisG, Matrix.sub_apply, Matrix.add_apply, Matrix.vecMulVec_apply, Matrix.one_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  have hvp : Continuous fun x : HPar k r' => liftVec k 1 r' x.1 p := (continuous_apply p).comp hv
  fun_prop

def heisF (k r' : ℕ) (x : HPar k r') : Mt k (1 + r') := heis0 k r' x

theorem heisF_meas : Measurable (heisF k r') := by
  have hc : Continuous (heisF k r') := continuous_heis0 k r'
  exact hc.measurable

def bcF (k r : ℕ) (c : Fin r → ℂ) : Mt k r := bigCell k r c 1

theorem bcF_meas : Measurable (bcF k r) := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  show Measurable fun c : Fin r → ℂ => bigCell k r c 1 i j
  simp only [bigCell]
  split_ifs <;> first | exact measurable_const | exact measurable_pi_apply _ | exact (continuous_star.measurable.comp (measurable_pi_apply _)).inv | exact continuous_star.measurable.inv | exact measurable_id | fun_prop | measurability

def w0F (k r' : ℕ) (c : ℂ) : Mt k (1 + r') := w0 k r' c

theorem long_weyl_element_measurable : Measurable (w0F k r') := by
  refine measurable_pi_lambda _ fun i => measurable_pi_lambda _ fun j => ?_
  show Measurable fun c : ℂ => w0 k r' c i j
  simp only [w0]
  split_ifs <;> first | exact measurable_const | exact measurable_pi_apply _ | exact (continuous_star.measurable.comp (measurable_pi_apply _)).inv | exact continuous_star.measurable.inv | exact measurable_id | fun_prop | measurability

theorem cell_meas {α : Type*} [MeasurableSpace α] {N T M N' : α → Mt k r} (hN : Measurable N) (hT : Measurable T)
    (hM : Measurable M) (hN' : Measurable N') :
    Measurable (β := Mt k r) (fun t => ((Matrix.of (N t))⁻¹ * Matrix.of (T t) * Matrix.of (M t) * Matrix.of (N' t) : Mat k r)) := by
  exact mm_meas (mm_meas (mm_meas (invM_meas.comp hN) hT) hM) hN'

theorem os_meas {α : Type*} [MeasurableSpace α] {X X' : α → HPar k r'} {C : α → ℂ} {Gm : α → Mt k r'}
    (hX : Measurable X) (hC : Measurable C) (hG : Measurable Gm) (hX' : Measurable X') :
    Measurable (β := Mt k (1 + r')) (fun t => oneStep k r' (X t) (C t) (Matrix.of (Gm t)) (X' t)) := by
  exact mm_meas (mm_meas (mm_meas (invM_meas.comp (heisF_meas.comp hX)) (long_weyl_element_measurable.comp hC)) (levM_meas.comp hG))
    (heisF_meas.comp hX')

theorem lev_inv (n : Mat k r') (hn : IsUnit n.det) : ιLev k 1 r' n⁻¹ = (ιLev k 1 r' n)⁻¹ := by
  have h1 : ιLev k 1 r' n * ιLev k 1 r' n⁻¹ = 1 := by
    rw [← lev_mul, Matrix.mul_nonsing_inv n hn, lev_one]
  exact (Matrix.inv_eq_right_inv h1).symm

theorem lev_unit (n : Mat k r') (hn : IsUnit n.det) : IsUnit (ιLev k 1 r' n).det := by
  have h1 : ιLev k 1 r' n * ιLev k 1 r' n⁻¹ = 1 := by
    rw [← lev_mul, Matrix.mul_nonsing_inv n hn, lev_one]
  exact Matrix.isUnit_det_of_right_inverse h1

theorem os_cell (x x' : HPar k r') (c : ℂ) (B n n' m : Mat k r') (hn : IsUnit n.det) :
    oneStep k r' x c (n⁻¹ * B * m * n') x' =
      (ιLev k 1 r' n * heis0 k r' x)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * ιLev k 1 r' m *
        (ιLev k 1 r' n' * heis0 k r' x') := by
  have e : w0 k r' c * ιLev k 1 r' n⁻¹ = (ιLev k 1 r' n)⁻¹ * w0 k r' c := by
    rw [t_w0comm k r' c n⁻¹, lev_inv n hn]
  simp only [oneStep, lev_mul, Matrix.mul_inv_rev, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (w0 k r' c), e]
  simp only [Matrix.mul_assoc]

end PartM

section PartK

variable {k r r' : ℕ}

def thetaF (k r' : ℕ) (p : HPar k r' × Mt k r') : Mt k (1 + r') := mulM (levM k r' p.2, heisF k r' p.1)

theorem thetaF_meas : Measurable (thetaF k r') := by
  first
    | exact mulM_meas.comp ((levM_meas.comp measurable_snd).prodMk (heisF_meas.comp measurable_fst))
    | exact mulM_meas.comp ((levM_meas.comp measurable_snd).prod_mk (heisF_meas.comp measurable_fst))

theorem μHeis_eq (k r' : ℕ) : μHeis k r' = (volume : Measure (HPar k r')).map (heisF k r') := rfl

theorem sfHeis : SFinite (μHeis k r') := by
  rw [μHeis_eq]
  infer_instance

attribute [local instance] sfHeis

theorem nuN_eq (hC : HeisConjLevMeas) (hN : ClosedN) (μ' : Measure (Mt k r')) (hμ' : IsHaarOn (Nset k r') μ') :
    ((μHeis k r').prod (μ'.map (levM k r'))).map mulM =
      ((volume : Measure (HPar k r')).prod μ').map (thetaF k r') := by
  have : SigmaFinite μ' := sf hμ'
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have h1 : Measurable fun a : Mt k (1 + r') × Mt k (1 + r') => F (mulM a) := hF.comp mulM_meas
  have h2 : Measurable fun a : HPar k r' × Mt k r' => F (thetaF k r' a) := hF.comp thetaF_meas
  rw [lintegral_map hF mulM_meas, lintegral_map hF thetaF_meas,
    lintegral_prod_symm' _ h1, lintegral_prod_symm' _ h2, lintegral_map h1.lintegral_prod_left' levM_meas]
  refine lintegral_congr_ae ?_
  filter_upwards [haar_ae hμ'] with n hn
  have hu : IsUnit (ιLev k 1 r' (Matrix.of n)).det := lev_unit _ ((hN k r').unit _ hn)
  have hm : Measurable fun y : Mt k (1 + r') => F (mulM (y, levM k r' n)) :=
    hF.comp (mm_meas measurable_id measurable_const)
  calc ∫⁻ y, F (mulM (y, levM k r' n)) ∂(μHeis k r')
      = ∫⁻ y, F (mulM (y, levM k r' n)) ∂((μHeis k r').map (conjM (ιLev k 1 r' (Matrix.of n)))) := by
        rw [hC k r' _ hn.1]
    _ = ∫⁻ y, F (mulM (conjM (ιLev k 1 r' (Matrix.of n)) y, levM k r' n)) ∂(μHeis k r') :=
        lintegral_map hm (conjM_cont _).measurable
    _ = ∫⁻ x, F (mulM (conjM (ιLev k 1 r' (Matrix.of n)) (heisF k r' x), levM k r' n)) := by
        rw [μHeis_eq]
        exact lintegral_map (hm.comp (conjM_cont _).measurable) heisF_meas
    _ = ∫⁻ x, F (thetaF k r' (x, n)) := by
        refine lintegral_congr fun x => ?_
        congr 1
        show ιLev k 1 r' (Matrix.of n) * heis0 k r' x * (ιLev k 1 r' (Matrix.of n))⁻¹ * ιLev k 1 r' (Matrix.of n) =
          ιLev k 1 r' (Matrix.of n) * heis0 k r' x
        rw [Matrix.nonsing_inv_mul_cancel_right _ _ hu]

theorem key (hN : ClosedN) (μN' μb' : Measure (Mt k r')) (hμN' : IsHaarOn (Nset k r') μN') [SigmaFinite μb']
    (f : Mt k (1 + r') → ℝ≥0∞) (hf : Measurable f) (c : ℂ) (B : Mat k r') :
    ∫⁻ X : HPar k r' × HPar k r', ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
        f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * B * Matrix.of q.2 * Matrix.of q.1.2) X.2)
          ∂((μN'.prod μN').prod μb') =
      ∫⁻ p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r'),
        f ((Matrix.of p.1.1)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * Matrix.of p.2 * Matrix.of p.1.2)
          ∂(((((volume : Measure (HPar k r')).prod μN').map (thetaF k r')).prod
            (((volume : Measure (HPar k r')).prod μN').map (thetaF k r'))).prod (μb'.map (levM k r'))) := by
  have : SigmaFinite μN' := sf hμN'
  have hcell : Measurable fun p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r') =>
      f ((Matrix.of p.1.1)⁻¹ * (w0 k r' c * ιLev k 1 r' B) * Matrix.of p.2 * Matrix.of p.1.2) :=
    hf.comp (cell_meas (N := fun p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r') => p.1.1)
      (T := fun _ => (w0 k r' c * ιLev k 1 r' B : Mat k (1 + r'))) (M := fun p => p.2) (N' := fun p => p.1.2)
      (measurable_fst.comp measurable_fst) measurable_const measurable_snd
      (measurable_snd.comp measurable_fst))
  have hΘ : Measurable (Prod.map (Prod.map (thetaF k r') (thetaF k r')) (levM k r')) :=
    (thetaF_meas.prodMap thetaF_meas).prodMap levM_meas
  let Fs : ((HPar k r' × Mt k r') × (HPar k r' × Mt k r')) × Mt k r' → ℝ≥0∞ := fun s =>
    f ((Matrix.of (thetaF k r' s.1.1))⁻¹ * (w0 k r' c * ιLev k 1 r' B) * Matrix.of (levM k r' s.2) *
      Matrix.of (thetaF k r' s.1.2))
  have hFs : Measurable Fs := hf.comp (cell_meas
      (N := fun s : ((HPar k r' × Mt k r') × (HPar k r' × Mt k r')) × Mt k r' => thetaF k r' s.1.1)
      (T := fun _ => (w0 k r' c * ιLev k 1 r' B : Mat k (1 + r'))) (M := fun s => levM k r' s.2)
      (N' := fun s => thetaF k r' s.1.2)
      (thetaF_meas.comp (measurable_fst.comp measurable_fst)) measurable_const (levM_meas.comp measurable_snd)
      (thetaF_meas.comp (measurable_snd.comp measurable_fst)))
  have hsw : Measurable fun p : (HPar k r' × HPar k r') × (Mt k r' × Mt k r') =>
      ∫⁻ m, Fs (((p.1.1, p.2.1), (p.1.2, p.2.2)), m) ∂μb' := by
    have h2 : Measurable fun p : (HPar k r' × HPar k r') × (Mt k r' × Mt k r') =>
        (((p.1.1, p.2.1), (p.1.2, p.2.2)) : (HPar k r' × Mt k r') × (HPar k r' × Mt k r')) := by fun_prop
    exact hFs.lintegral_prod_right'.comp h2
  symm
  calc _ = ∫⁻ s, Fs s ∂((((volume : Measure (HPar k r')).prod μN').prod
            ((volume : Measure (HPar k r')).prod μN')).prod μb') := by
        rw [Measure.map_prod_map _ _ thetaF_meas thetaF_meas,
          Measure.map_prod_map _ _ (thetaF_meas.prodMap thetaF_meas) levM_meas]
        exact lintegral_map hcell hΘ
    _ = ∫⁻ u, ∫⁻ m, Fs (u, m) ∂μb' ∂(((volume : Measure (HPar k r')).prod μN').prod
            ((volume : Measure (HPar k r')).prod μN')) := lintegral_prod _ hFs.aemeasurable
    _ = ∫⁻ p : (HPar k r' × HPar k r') × (Mt k r' × Mt k r'), ∫⁻ m, Fs (((p.1.1, p.2.1), (p.1.2, p.2.2)), m) ∂μb'
          ∂(((volume : Measure (HPar k r')).prod (volume : Measure (HPar k r'))).prod (μN'.prod μN')) :=
        swap4 _ _ _ _ (fun u => ∫⁻ m, Fs (u, m) ∂μb') hFs.lintegral_prod_right'
    _ = ∫⁻ X : HPar k r' × HPar k r', ∫⁻ Q : Mt k r' × Mt k r', ∫⁻ m, Fs (((X.1, Q.1), (X.2, Q.2)), m) ∂μb'
          ∂(μN'.prod μN') := lintegral_prod _ hsw.aemeasurable
    _ = _ := by
        refine lintegral_congr fun X => ?_
        have hq : Measurable fun q : (Mt k r' × Mt k r') × Mt k r' =>
            f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * B * Matrix.of q.2 * Matrix.of q.1.2) X.2) :=
          hf.comp (os_meas (X := fun _ => X.1) (C := fun _ => c) (X' := fun _ => X.2) measurable_const measurable_const
            (cell_meas (N := fun q : (Mt k r' × Mt k r') × Mt k r' => q.1.1) (T := fun _ => B) (M := fun q => q.2)
              (N' := fun q => q.1.2) (measurable_fst.comp measurable_fst) measurable_const measurable_snd
              (measurable_snd.comp measurable_fst)) measurable_const)
        refine Eq.trans ?_ (lintegral_prod _ hq.aemeasurable).symm
        refine lintegral_congr_ae ?_
        have hae : ∀ᵐ Q : Mt k r' × Mt k r' ∂(μN'.prod μN'), (Matrix.of Q.1 : Mat k r') ∈ Nset k r' :=
          Measure.quasiMeasurePreserving_fst.ae (haar_ae hμN')
        filter_upwards [hae] with Q hQ
        refine lintegral_congr fun m => ?_
        exact congrArg f
          (os_cell X.1 X.2 c B (Matrix.of Q.1) (Matrix.of Q.2) (Matrix.of m) ((hN k r').unit _ hQ)).symm

end PartK

section PartS

variable {k r r' : ℕ}

def IterAt (k r : ℕ) : Prop :=
  ∀ (μG μN μb : Measure (Mt k r)), IsHaarOn (GV k r) μG → IsHaarOn (Nset k r) μN → IsHaarOn (UWb k r) μb →
    ∃ C : ℝ≥0, 0 < C ∧ ∀ f : Mt k r → ℝ≥0∞, Measurable f →
      (∫⁻ g, f g ∂μG) = (C : ℝ≥0∞) * ∫⁻ c : Fin r → ℂ, ENNReal.ofReal (cWeight k r c) *
        ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
          f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb)

theorem haar_smul (HU : HaarUnique) {U : Set (Mat k r)} (hU : IsClosedSubgroup U) {μ ν : Measure (Mt k r)}
    (hμ : IsHaarOn U μ) (hν : IsHaarOn U ν) : ∃ a : ℝ≥0, 0 < a ∧ ν = a • μ := by
  obtain ⟨c, hc⟩ := HU k r U μ ν hU hμ hν.conc hν.left hν.finite_compact
  refine ⟨c, ?_, hc⟩
  rcases eq_or_ne c 0 with h0 | h0
  · exact absurd (by rw [hc, h0, zero_smul]) hν.ne_zero
  · exact pos_iff_ne_zero.2 h0

theorem lint_smul3 {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite μ]
    [SFinite ν] (a b : ℝ≥0) (F : (α × α) × β → ℝ≥0∞) :
    ∫⁻ p, F p ∂(((a • μ).prod (a • μ)).prod (b • ν)) = ((a * a * b : ℝ≥0) : ℝ≥0∞) * ∫⁻ p, F p ∂((μ.prod μ).prod ν) := by
  first
    | (simp only [ENNReal.smul_def, Measure.prod_smul_left, Measure.prod_smul_right, smul_smul, lintegral_smul_measure,
        smul_eq_mul, ENNReal.coe_mul]
       ring)
    | (simp [Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, smul_smul, ENNReal.smul_def]
       ring)
    | simp [Measure.prod_smul_left, Measure.prod_smul_right, lintegral_smul_measure, smul_smul, ENNReal.smul_def,
        mul_comm, mul_assoc, mul_left_comm]

theorem cW_meas (k r : ℕ) : Measurable fun c : Fin r → ℂ => ENNReal.ofReal (cWeight k r c) := by
  first
    | (unfold cWeight; fun_prop)
    | exact ENNReal.measurable_ofReal.comp (Finset.measurable_prod _ fun a _ => ((measurable_pi_apply a).norm).pow_const _)
    | (unfold cWeight; measurability)

theorem iter_step (hO : OneStepInt) (HU : HaarUnique) (hL : LevHaar) (hCN : ClosedN) (hCb : ClosedWb)
    (hG : HaarGExists) (hNe : HaarNExists) (hWb : HaarWbExists) (hNR : NRecHaar) (hC : HeisConjLevMeas)
    (k r' : ℕ) (ih : IterAt k r') : IterAt k (1 + r') := by
  intro μG μN μb hμG hμN hμb
  obtain ⟨μG₁, hG₁⟩ := hG k r'
  obtain ⟨μN', hN'⟩ := hNe k r'
  obtain ⟨μb', hb'⟩ := hWb k r'
  obtain ⟨C₀, hC₀, h0⟩ := hO k r' μG μG₁ hμG hG₁
  obtain ⟨C₁, hC₁, h1⟩ := ih μG₁ μN' μb' hG₁ hN' hb'
  have hνN : IsHaarOn (Nset k (1 + r')) (((volume : Measure (HPar k r')).prod μN').map (thetaF k r')) := by
    rw [← nuN_eq hC hCN μN' hN']; exact hNR k r' μN' hN'
  obtain ⟨a, ha, hae⟩ := haar_smul HU (hCN k (1 + r')) hμN hνN
  have hνb : IsHaarOn (UWb k (1 + r')) (μb'.map (levM k r')) := by
    rw [uWbRec k r']; exact (hL k r' _ μb' (hCb k r') hb').2
  obtain ⟨b, hb, hbe⟩ := haar_smul HU (hCb k (1 + r')) hμb hνb
  have : SigmaFinite μG₁ := sf hG₁
  have : SigmaFinite μN' := sf hN'
  have : SigmaFinite μb' := sf hb'
  have : SigmaFinite μN := sf hμN
  have : SigmaFinite μb := sf hμb
  refine ⟨C₀ * C₁ * (a * a * b), by positivity, fun f hf => ?_⟩

  let Kμ : Mt k (1 + r') → ℝ≥0∞ := fun T =>
    ∫⁻ p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r'),
      f ((Matrix.of p.1.1)⁻¹ * Matrix.of T * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb)
  have hKμ : Measurable Kμ := by
    have : Measurable fun t : Mt k (1 + r') × ((Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r')) =>
        f ((Matrix.of t.2.1.1)⁻¹ * Matrix.of t.1 * Matrix.of t.2.2 * Matrix.of t.2.1.2) :=
      hf.comp (cell_meas (N := fun t : Mt k (1 + r') × ((Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r')) => t.2.1.1)
        (T := fun t => t.1) (M := fun t => t.2.2) (N' := fun t => t.2.1.2)
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop))
    exact this.lintegral_prod_right'
  let TT : ℂ × (Fin r' → ℂ) → Mt k (1 + r') := fun p => mulM (w0F k r' p.1, levM k r' (bcF k r' p.2))
  have hTT : Measurable TT := mm_meas (long_weyl_element_measurable.comp measurable_fst) (levM_meas.comp (bcF_meas.comp measurable_snd))

  have step : ∀ c : ℂ, ∫⁻ p : (HPar k r' × HPar k r') × Mt k r', f (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2)
        ∂((volume : Measure (HPar k r' × HPar k r')).prod μG₁) =
      (C₁ : ℝ≥0∞) * (((a * a * b : ℝ≥0) : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') * Kμ (TT (c, c'))) := by
    intro c
    have m1 : Measurable fun p : (HPar k r' × HPar k r') × Mt k r' => f (oneStep k r' p.1.1 c (Matrix.of p.2) p.1.2) :=
      hf.comp (os_meas (X := fun p : (HPar k r' × HPar k r') × Mt k r' => p.1.1) (C := fun _ => c) (Gm := fun p => p.2)
        (X' := fun p => p.1.2) (by fun_prop) measurable_const (by fun_prop) (by fun_prop))
    have m3 : Measurable fun t : ((HPar k r' × HPar k r') × (Fin r' → ℂ)) × ((Mt k r' × Mt k r') × Mt k r') =>
        f (oneStep k r' t.1.1.1 c ((Matrix.of t.2.1.1)⁻¹ * bigCell k r' t.1.2 1 * Matrix.of t.2.2 * Matrix.of t.2.1.2)
          t.1.1.2) :=
      hf.comp (os_meas
        (X := fun t : ((HPar k r' × HPar k r') × (Fin r' → ℂ)) × ((Mt k r' × Mt k r') × Mt k r') => t.1.1.1)
        (C := fun _ => c) (X' := fun t => t.1.1.2) (by fun_prop) measurable_const
        (cell_meas (N := fun t : ((HPar k r' × HPar k r') × (Fin r' → ℂ)) × ((Mt k r' × Mt k r') × Mt k r') => t.2.1.1)
          (T := fun t => bcF k r' t.1.2) (M := fun t => t.2.2) (N' := fun t => t.2.1.2)
          (by fun_prop) (bcF_meas.comp (by fun_prop)) (by fun_prop) (by fun_prop)) (by fun_prop))
    calc _ = ∫⁻ X : HPar k r' × HPar k r', ∫⁻ g₁ : Mt k r', f (oneStep k r' X.1 c (Matrix.of g₁) X.2) ∂μG₁ :=
          lintegral_prod _ m1.aemeasurable
      _ = ∫⁻ X : HPar k r' × HPar k r', (C₁ : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') *
            ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
              f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * bigCell k r' c' 1 * Matrix.of q.2 * Matrix.of q.1.2) X.2)
                ∂((μN'.prod μN').prod μb') := by
          refine lintegral_congr fun X => ?_
          exact h1 (fun g₁ => f (oneStep k r' X.1 c (Matrix.of g₁) X.2))
            (hf.comp (os_meas (X := fun _ => X.1) (C := fun _ => c) (Gm := fun g₁ => g₁) (X' := fun _ => X.2)
              measurable_const measurable_const measurable_id measurable_const))
      _ = (C₁ : ℝ≥0∞) * ∫⁻ X : HPar k r' × HPar k r', ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') *
            ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
              f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * bigCell k r' c' 1 * Matrix.of q.2 * Matrix.of q.1.2) X.2)
                ∂((μN'.prod μN').prod μb') := lintegral_const_mul' _ _ ENNReal.coe_ne_top
      _ = (C₁ : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ∫⁻ X : HPar k r' × HPar k r', ENNReal.ofReal (cWeight k r' c') *
            ∫⁻ q : (Mt k r' × Mt k r') × Mt k r',
              f (oneStep k r' X.1 c ((Matrix.of q.1.1)⁻¹ * bigCell k r' c' 1 * Matrix.of q.2 * Matrix.of q.1.2) X.2)
                ∂((μN'.prod μN').prod μb') := by
          congr 1
          refine lintegral_lintegral_swap ?_
          exact (((cW_meas k r').comp measurable_snd).mul m3.lintegral_prod_right').aemeasurable
      _ = (C₁ : ℝ≥0∞) * ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') *
            (((a * a * b : ℝ≥0) : ℝ≥0∞) * Kμ (TT (c, c'))) := by
          congr 1
          refine lintegral_congr fun c' => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          congr 1
          refine (key hCN μN' μb' hN' f hf c (bigCell k r' c' 1)).trans ?_
          rw [hae, hbe]
          exact lint_smul3 μN μb a b _
      _ = _ := by
          congr 1
          rw [← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
          refine lintegral_congr fun c' => ?_
          exact mul_left_comm _ _ _

  let GG : ℂ × (Fin r' → ℂ) → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (‖p.1‖ ^ (2 * (2 * r' + k + 1))) * (ENNReal.ofReal (cWeight k r' p.2) * Kμ (TT p))
  have hGG : Measurable GG :=
    Measurable.mul (by fun_prop) (((cW_meas k r').comp measurable_snd).mul (hKμ.comp hTT))
  have outer : ∫⁻ c : Fin (1 + r') → ℂ, ENNReal.ofReal (cWeight k (1 + r') c) *
        ∫⁻ p : (Mt k (1 + r') × Mt k (1 + r')) × Mt k (1 + r'),
          f ((Matrix.of p.1.1)⁻¹ * bigCell k (1 + r') c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) =
      ∫⁻ c : ℂ, ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))) *
        ∫⁻ c' : Fin r' → ℂ, ENNReal.ofReal (cWeight k r' c') * Kμ (TT (c, c')) := by
    calc _ = ∫⁻ c : Fin (1 + r') → ℂ, GG (splitC r' c) := by
          refine lintegral_congr fun c => ?_
          show _ = ENNReal.ofReal (‖c (a0 r')‖ ^ (2 * (2 * r' + k + 1))) *
            (ENNReal.ofReal (cWeight k r' fun a => c (Fin.natAdd 1 a)) * Kμ (TT (splitC r' c)))
          rw [cWeight_rec, ENNReal.ofReal_mul (by positivity), mul_assoc, t_bigcellrec k r' c 1]
          rfl
      _ = ∫⁻ p : ℂ × (Fin r' → ℂ), GG p := lint_split r' GG
      _ = ∫⁻ c : ℂ, ∫⁻ c' : Fin r' → ℂ, GG (c, c') := lintegral_prod _ hGG.aemeasurable
      _ = _ := by
          refine lintegral_congr fun c => ?_
          exact lintegral_const_mul' (ENNReal.ofReal (‖c‖ ^ (2 * (2 * r' + k + 1))))
            (fun c' => ENNReal.ofReal (cWeight k r' c') * Kμ (TT (c, c'))) ENNReal.ofReal_ne_top
  rw [h0 f hf, outer]
  simp only [step]
  have e : ∀ (A : ℝ≥0) (w x : ℝ≥0∞), w * ((C₁ : ℝ≥0∞) * ((A : ℝ≥0∞) * x)) =
      ((C₁ * A : ℝ≥0) : ℝ≥0∞) * (w * x) := by
    intro A w x; rw [ENNReal.coe_mul]; ring
  simp only [e]
  rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, ← mul_assoc, ← ENNReal.coe_mul, mul_assoc C₀ C₁]

theorem bc_zero (k : ℕ) (c : Fin 0 → ℂ) : bigCell k 0 c 1 = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  simp only [bigCell, Matrix.one_apply, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem iter_base (HU : HaarUnique) (hCb : ClosedWb) (hNB : NBase) (k : ℕ) : IterAt k 0 := by
  intro μG μN μb hG hN hb
  have hUW : UWb k 0 = GV k 0 := by
    ext g
    constructor
    · exact fun h => h.1
    · exact fun h => ⟨h, fun a => a.elim0⟩
  have hG' : IsHaarOn (UWb k 0) μG := by rw [hUW]; exact hG
  obtain ⟨c₀, hc₀, hce⟩ := haar_smul HU (hCb k 0) hb hG'
  have : SigmaFinite μb := sf hb
  let o : Mt k 0 := (1 : Mat k 0)
  have hNd : μN = μN {o} • Measure.dirac o := by
    rw [← Measure.restrict_singleton, Measure.restrict_eq_self_of_ae_mem]
    have h := haar_ae hN
    rw [hNB k] at h
    exact h
  have hfin : μN {o} ≠ ∞ := (hN.finite_compact {o} isCompact_singleton).ne
  have hne : μN {o} ≠ 0 := by
    intro h
    apply hN.ne_zero
    rw [hNd, h, zero_smul]
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, μN {o} = a := ⟨(μN {o}).toNNReal, (ENNReal.coe_toNNReal hfin).symm⟩
  have ha0 : a ≠ 0 := by
    intro h; apply hne; rw [ha, h]; rfl
  have hNd' : μN = a • Measure.dirac o := by
    rw [hNd, ha]; rfl
  refine ⟨c₀ * (a * a)⁻¹, by positivity, fun f hf => ?_⟩
  have hF : ∀ c : Fin 0 → ℂ, Measurable fun p : (Mt k 0 × Mt k 0) × Mt k 0 =>
      f ((Matrix.of p.1.1)⁻¹ * bigCell k 0 c 1 * Matrix.of p.2 * Matrix.of p.1.2) := fun c =>
    hf.comp (cell_meas (N := fun p : (Mt k 0 × Mt k 0) × Mt k 0 => p.1.1) (T := fun _ => bcF k 0 c) (M := fun p => p.2)
      (N' := fun p => p.1.2) (by fun_prop) measurable_const (by fun_prop) (by fun_prop))
  have inner : ∀ c : Fin 0 → ℂ, ∫⁻ p : (Mt k 0 × Mt k 0) × Mt k 0,
      f ((Matrix.of p.1.1)⁻¹ * bigCell k 0 c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) =
      ((a * a : ℝ≥0) : ℝ≥0∞) * ∫⁻ m, f m ∂μb := by
    intro c
    have h1 : μb = (1 : ℝ≥0) • μb := (one_smul _ _).symm
    rw [hNd']
    conv_lhs => rw [h1]
    rw [lint_smul3 (Measure.dirac o) μb a 1, mul_one, Measure.dirac_prod_dirac, Measure.dirac_prod,
      lintegral_map (hF c) measurable_prodMk_left]
    congr 1
    refine lintegral_congr fun m => ?_
    refine congrArg f ?_
    show ((1 : Mat k 0)⁻¹ * bigCell k 0 c 1 * Matrix.of m * (1 : Mat k 0) : Mat k 0) = Matrix.of m
    rw [bc_zero, inv_one, one_mul, one_mul, mul_one]
  simp only [inner]
  rw [volume_pi, Measure.pi_of_empty, lintegral_dirac, hce, lintegral_smul_measure]
  have hw : cWeight k 0 (fun a => isEmptyElim a) = 1 := by simp [cWeight]
  rw [hw, ENNReal.ofReal_one, one_mul, ← mul_assoc, ← ENNReal.coe_mul, ENNReal.smul_def, smul_eq_mul]
  congr 2
  field_simp

theorem assembleIter : AssembleIter := by
  intro hO HU _ hL _ hCN hCb hG hNe hWb hNR hNB hC _ _ _ k r
  induction r with
  | zero => exact iter_base HU hCb hNB k
  | succ r' ih =>
    have h := iter_step hO HU hL hCN hCb hG hNe hWb hNR hC k r' ih
    rw [Nat.add_comm 1 r'] at h
    exact h

end PartS

end Formalism.FourierDecayAlt.P.LongWeylElement

namespace Formalism.FourierDecayAlt.P

theorem bigCellRec_statement : Formalism.FourierDecayAlt.B2.BigCellRec := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.t_bigcellrec

theorem long_weyl_element_commutation : Formalism.FourierDecayAlt.B2.WeylElementCommutesLevelOne := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.t_w0comm

theorem unipotent_weyl_recursion : Formalism.FourierDecayAlt.B2.UWbRec := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.uWbRec

theorem iterated_integral_of_parts : Formalism.FourierDecayAlt.B2.AssembleIter := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.assembleIter

theorem iterated_integration_formula : Formalism.FourierDecayAlt.B2.IterInt :=
  iterated_integral_of_parts stabilizer_integration_formula haar_measure_unique_up_to_scalar haar_measure_inversion levi_haar_measure_exists unitary_group_closed
    unipotent_radical_closed opposite_weyl_subgroup_closed unitary_group_haar_exists unipotent_haar_exists opposite_weyl_haar_exists
    unipotent_haar_recursion unipotent_haar_base_case heisenberg_levi_conjugation_measure bigCellRec_statement long_weyl_element_commutation unipotent_weyl_recursion

theorem bruhat_big_cell_factorization : Formalism.FourierDecayAlt.B2.BigCellFactor := by
  exact Formalism.FourierDecayAlt.P.LongWeylElement.t_bigcellfactor

end Formalism.FourierDecayAlt.P
