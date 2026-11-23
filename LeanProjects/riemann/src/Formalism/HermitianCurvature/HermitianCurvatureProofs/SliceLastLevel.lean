import Formalism.HermitianCurvature.StatementJF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PhiBoundPartsOfRadicalParametrisation
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DilationUnipotentWeylMeasure
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LongWeylElement
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingExistence
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OppositeWeylSubgroupClosed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormFactor
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TwoByOneBlock
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SmoothnessOnGoodSet
import Formalism.FormalDegreeBessel.FinalBF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalIntegralAeConvergenceContinuity

noncomputable section

section PartDefs
open Matrix MeasureTheory

namespace Formalism.FourierDecayAlt.P.SliceLastLevel

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def phi (k r : ℕ) (c : Fin r → ℂ) (n n' : B.Mat k r) (μ : B.Mat k 0) : B.Mat k r :=
  n⁻¹ * bigCell k r c (castW μ) * n'

def emb0 (k r : ℕ) (Y : B.Mat k 0) : B.Mat k r := fun i j =>
  if h : (r ≤ i.val ∧ i.val ≤ r + k) ∧ (r ≤ j.val ∧ j.val ≤ r + k) then
    Y ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0

end Formalism.FourierDecayAlt.P.SliceLastLevel

end PartDefs

section PartSz
open Matrix

namespace Formalism.FourierDecayAlt.P.SliceLastLevel

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF Formalism.FourierDecayAlt.P.Ux5

section szIndex

variable (k r : ℕ)

def szX (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def szW (w : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + w.val, by omega⟩

def szS (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

lemma szX_val (a : Fin r) : (szX k r a).val = a.val := rfl
lemma szW_val (w : Fin (k + 1)) : (szW k r w).val = r + w.val := rfl
lemma szS_val (a : Fin r) : (szS k r a).val = 2 * r + k - a.val := rfl

def szF : (Fin r ⊕ Fin (k + 1)) ⊕ Fin r → Fin (2 * r + k + 1) :=
  Sum.elim (Sum.elim (szX k r) (szW k r)) (szS k r)

lemma szF_bij : Function.Bijective (szF k r) := by
  constructor
  · rintro ((a | a) | a) ((b | b) | b) h <;>
      simp only [szF, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, szX_val, szW_val, szS_val] at h <;>
      first
        | (have := a.isLt; have := b.isLt; congr 2; exact Fin.ext (by omega))
        | (have := a.isLt; have := b.isLt; congr 1; exact Fin.ext (by omega))
        | (exfalso; have := a.isLt; have := b.isLt; omega)
  · intro i
    have hi := i.isLt
    by_cases h1 : i.val < r
    · exact ⟨Sum.inl (Sum.inl ⟨i.val, h1⟩), Fin.ext rfl⟩
    · by_cases h2 : i.val ≤ r + k
      · exact ⟨Sum.inl (Sum.inr ⟨i.val - r, by omega⟩), Fin.ext (by simp [szF, szW_val]; omega)⟩
      · exact ⟨Sum.inr ⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp [szF, szS_val]; omega)⟩

def szE : (Fin r ⊕ Fin (k + 1)) ⊕ Fin r ≃ Fin (2 * r + k + 1) := Equiv.ofBijective _ (szF_bij k r)

variable {k r}

lemma sz_sum (f : Fin (2 * r + k + 1) → ℂ) :
    ∑ i, f i = (∑ a, f (szX k r a)) + (∑ w, f (szW k r w)) + ∑ a, f (szS k r a) := by
  rw [← Equiv.sum_comp (szE k r) f, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rfl

lemma sz_cases (i : Fin (2 * r + k + 1)) :
    (∃ a, i = szX k r a) ∨ (∃ w, i = szW k r w) ∨ (∃ a, i = szS k r a) := by
  obtain ⟨x, rfl⟩ := (szF_bij k r).2 i
  rcases x with ((a | a) | a)
  · exact Or.inl ⟨a, rfl⟩
  · exact Or.inr (Or.inl ⟨a, rfl⟩)
  · exact Or.inr (Or.inr ⟨a, rfl⟩)

lemma sz_mul_sub {α β : Type*} (A B : B.Mat k r) (f : α → Fin (2 * r + k + 1)) (g : β → Fin (2 * r + k + 1)) :
    (A * B).submatrix f g = A.submatrix f (szX k r) * B.submatrix (szX k r) g +
      A.submatrix f (szW k r) * B.submatrix (szW k r) g + A.submatrix f (szS k r) * B.submatrix (szS k r) g := by
  ext i j
  simp only [submatrix_apply, Matrix.add_apply, Matrix.mul_apply]
  exact sz_sum (fun x => A (f i) x * B x (g j))

end szIndex

section szBlocks

variable {k r : ℕ}

lemma sz_inv_apply {q : B.Mat k r} (hq : q ∈ B.GV k r) (i j : Fin (2 * r + k + 1)) :
    q⁻¹ i j = Formalism.QuantumDeterminants.GBasic.sgn k r i * Formalism.QuantumDeterminants.GBasic.sgn k r j *
      star (q (Formalism.QuantumDeterminants.GBasic.sig k r j) (Formalism.QuantumDeterminants.GBasic.sig k r i)) := by
  have h1 : (Hpk k r * qᴴ * Hpk k r) * q = 1 := by
    have hq' : qᴴ * Hpk k r * q = Hpk k r := hq
    calc (Hpk k r * qᴴ * Hpk k r) * q = Hpk k r * (qᴴ * Hpk k r * q) := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * Hpk k r := by rw [hq']
      _ = 1 := Formalism.QuantumDeterminants.GBasic.Hpk_sq k r
  rw [Matrix.inv_eq_left_inv h1]
  simp only [Matrix.mul_apply, Formalism.QuantumDeterminants.GBasic.Hpk_eq, conjTranspose_apply, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [Formalism.QuantumDeterminants.GBasic.eq_sig_iff k r j, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Formalism.QuantumDeterminants.GBasic.sgn_sig]
  ring

lemma sz_norm_sgn (i : Fin (2 * r + k + 1)) : ‖Formalism.QuantumDeterminants.GBasic.sgn k r i‖ = 1 := by
  unfold Formalism.QuantumDeterminants.GBasic.sgn; split_ifs <;> simp

lemma sz_sgn_S (a : Fin r) : Formalism.QuantumDeterminants.GBasic.sgn k r (szS k r a) = 1 := by
  have ha := a.isLt
  unfold Formalism.QuantumDeterminants.GBasic.sgn; rw [if_neg]; simp only [szS_val]; omega

lemma sz_norm_inv {q : B.Mat k r} (hq : q ∈ B.GV k r) (i j : Fin (2 * r + k + 1)) :
    ‖q⁻¹ i j‖ = ‖q (Formalism.QuantumDeterminants.GBasic.sig k r j) (Formalism.QuantumDeterminants.GBasic.sig k r i)‖ := by
  rw [sz_inv_apply hq, norm_mul, norm_mul, sz_norm_sgn, sz_norm_sgn, norm_star]; ring

lemma sz_sig_X (a : Fin r) : Formalism.QuantumDeterminants.GBasic.sig k r (szX k r a) = szS k r a := by
  apply Fin.ext; rw [Formalism.QuantumDeterminants.GBasic.sig_lo k r _ (by simp [szX_val])]; simp [szX_val, szS_val]

lemma sz_sig_S (a : Fin r) : Formalism.QuantumDeterminants.GBasic.sig k r (szS k r a) = szX k r a := by
  have ha := a.isLt
  apply Fin.ext; rw [Formalism.QuantumDeterminants.GBasic.sig_hi k r _ (by simp [szS_val]; omega)]; simp [szX_val, szS_val]; omega

lemma involution_fixes_middle_basis (w : Fin (k + 1)) : Formalism.QuantumDeterminants.GBasic.sig k r (szW k r w) = szW k r w := by
  have hw := w.isLt
  exact Formalism.QuantumDeterminants.GBasic.sig_mid k r _ (by simp [szW_val]) (by simp [szW_val]; omega)

lemma sz_N_GV {q : B.Mat k r} (hq : q ∈ Nset k r) : q ∈ B.GV k r := hq.1

lemma sz_N_inv {q : B.Mat k r} (hq : q ∈ Nset k r) : q⁻¹ ∈ Nset k r :=
  (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).inv_mem q hq

lemma sz_N_unit {q : B.Mat k r} (hq : q ∈ Nset k r) : IsUnit q.det :=
  (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).unit q hq

lemma sz_eI (b : Fin r) : szX k r b = eI k r b := rfl

lemma sz_N_XX {q : B.Mat k r} (hq : q ∈ Nset k r) (a b : Fin r) (h : b < a) : q (szX k r a) (szX k r b) = 0 := by
  have := hq.2.1 b (szX k r a) (by simp [szX_val]; exact le_of_lt h)
  rw [sz_eI b, this, if_neg]; intro he; rw [Fin.ext_iff] at he; simp [szX_val, eI] at he; omega

lemma unipotent_diag_entry_szX_eq_one {q : B.Mat k r} (hq : q ∈ Nset k r) (a : Fin r) : q (szX k r a) (szX k r a) = 1 := by
  have := hq.2.1 a (szX k r a) (by simp [szX_val])
  exact this.trans (if_pos rfl)

lemma sz_N_WX {q : B.Mat k r} (hq : q ∈ Nset k r) (w : Fin (k + 1)) (b : Fin r) : q (szW k r w) (szX k r b) = 0 := by
  have hb := b.isLt
  have := hq.2.1 b (szW k r w) (by simp [szW_val]; omega)
  rw [sz_eI b, this, if_neg]; intro he; rw [Fin.ext_iff] at he; simp [szW_val, eI] at he; omega

lemma sz_N_SX {q : B.Mat k r} (hq : q ∈ Nset k r) (a b : Fin r) : q (szS k r a) (szX k r b) = 0 := by
  have ha := a.isLt; have hb := b.isLt
  have := hq.2.1 b (szS k r a) (by simp [szS_val]; omega)
  rw [sz_eI b, this, if_neg]; intro he; rw [Fin.ext_iff] at he; simp [szS_val, eI] at he; omega

lemma sz_N_WW {q : B.Mat k r} (hq : q ∈ Nset k r) (v w : Fin (k + 1)) :
    q (szW k r v) (szW k r w) = if v = w then 1 else 0 := by
  have hw := w.isLt
  rw [hq.2.2 _ _ (by simp [szW_val]) (by simp [szW_val]; omega) (by simp [szW_val])]
  congr 1; apply propext; constructor
  · intro h; rw [Fin.ext_iff] at h; simp [szW_val] at h; exact Fin.ext h
  · rintro rfl; rfl

lemma sz_N_SW {q : B.Mat k r} (hq : q ∈ Nset k r) (a : Fin r) (w : Fin (k + 1)) : q (szS k r a) (szW k r w) = 0 := by
  have hw := w.isLt; have ha := a.isLt
  rw [hq.2.2 _ _ (by simp [szW_val]) (by simp [szW_val]; omega) (by simp [szS_val]; omega), if_neg]
  intro he; rw [Fin.ext_iff] at he; simp [szW_val, szS_val] at he; omega

lemma sz_N_SS {q : B.Mat k r} (hq : q ∈ Nset k r) (a b : Fin r) (h : a < b) : q (szS k r a) (szS k r b) = 0 := by
  have hinv : q = (q⁻¹)⁻¹ := (Matrix.nonsing_inv_nonsing_inv q (sz_N_unit hq)).symm
  have h1 := sz_inv_apply (sz_N_GV (sz_N_inv hq)) (szS k r a) (szS k r b)
  rw [← hinv, sz_sig_S, sz_sig_S, sz_N_XX (sz_N_inv hq) b a h] at h1
  rw [h1]; simp

lemma unipotent_diag_entry_szS_eq_one {q : B.Mat k r} (hq : q ∈ Nset k r) (a : Fin r) : q (szS k r a) (szS k r a) = 1 := by
  have hinv : q = (q⁻¹)⁻¹ := (Matrix.nonsing_inv_nonsing_inv q (sz_N_unit hq)).symm
  have h1 := sz_inv_apply (sz_N_GV (sz_N_inv hq)) (szS k r a) (szS k r a)
  rw [← hinv, sz_sig_S, unipotent_diag_entry_szX_eq_one (sz_N_inv hq) a, sz_sgn_S] at h1
  rw [h1]; simp

lemma sz_subN {q : B.Mat k r} (hq : q ∈ Nset k r) :
    q.submatrix (szW k r) (szX k r) = 0 ∧ q.submatrix (szS k r) (szX k r) = 0 ∧
      q.submatrix (szS k r) (szW k r) = 0 ∧ q.submatrix (szW k r) (szW k r) = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext i j
  · exact sz_N_WX hq i j
  · exact sz_N_SX hq i j
  · exact sz_N_SW hq i j
  · rw [submatrix_apply, sz_N_WW hq, Matrix.one_apply]

lemma sz_bc_X (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (szX k r b) = if i = szS k r b then c b else 0 := by
  unfold bigCell
  rw [dif_pos (show (szX k r b).val < r from b.isLt)]
  rfl

lemma bigCell_szW_szW (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (v w : Fin (k + 1)) :
    bigCell k r c μ (szW k r v) (szW k r w) = μ v w := by
  have hv := v.isLt; have hw := w.isLt
  unfold bigCell
  rw [dif_neg (show ¬ (szW k r w).val < r by simp [szW_val]),
    dif_pos (show (szW k r w).val ≤ r + k by simp [szW_val]; omega),
    dif_pos (show r ≤ (szW k r v).val ∧ (szW k r v).val ≤ r + k by simp [szW_val]; omega)]
  congr 1 <;> apply Fin.ext <;> simp [szW_val]

lemma bigCell_middle_col_vanish (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1))
    (hi : i.val < r ∨ r + k < i.val) (w : Fin (k + 1)) : bigCell k r c μ i (szW k r w) = 0 := by
  have hw := w.isLt
  unfold bigCell
  rw [dif_neg (show ¬ (szW k r w).val < r by simp [szW_val]),
    dif_pos (show (szW k r w).val ≤ r + k by simp [szW_val]; omega), dif_neg (by omega)]

lemma sz_bc_S (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (szS k r b) = if i = szX k r b then (star (c b))⁻¹ else 0 := by
  have hb := b.isLt
  unfold bigCell
  rw [dif_neg (show ¬ (szS k r b).val < r by simp [szS_val]; omega),
    dif_neg (show ¬ (szS k r b).val ≤ r + k by simp [szS_val]; omega)]
  have e : (⟨2 * r + k - (szS k r b).val, by simp [szS_val]; omega⟩ : Fin r) = b := by
    apply Fin.ext; simp [szS_val]; omega
  simp only [e]
  congr 1
  apply propext; constructor
  · intro h; apply Fin.ext; simp [szX_val]; simp [szS_val] at h; omega
  · intro h; subst h; simp [szX_val, szS_val]; omega

lemma sz_bc (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (szS k r) (szX k r) = diagonal c ∧
    (bigCell k r c μ).submatrix (szX k r) (szX k r) = 0 ∧
    (bigCell k r c μ).submatrix (szW k r) (szX k r) = 0 ∧
    (bigCell k r c μ).submatrix (szX k r) (szW k r) = 0 ∧
    (bigCell k r c μ).submatrix (szW k r) (szW k r) = μ ∧
    (bigCell k r c μ).submatrix (szS k r) (szW k r) = 0 ∧
    (bigCell k r c μ).submatrix (szX k r) (szS k r) = diagonal (fun a => (star (c a))⁻¹) ∧
    (bigCell k r c μ).submatrix (szW k r) (szS k r) = 0 ∧
    (bigCell k r c μ).submatrix (szS k r) (szS k r) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ext i j <;> simp only [submatrix_apply, Matrix.zero_apply]
  · rw [sz_bc_X, diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg]; intro h'; apply h; have := i.isLt; have := j.isLt; rw [Fin.ext_iff] at h'
      simp [szS_val] at h'; exact Fin.ext (by omega)
  · rw [sz_bc_X, if_neg]; intro h; have := i.isLt; rw [Fin.ext_iff] at h; simp [szS_val, szX_val] at h; omega
  · rw [sz_bc_X, if_neg]; intro h; have := j.isLt; rw [Fin.ext_iff] at h; simp [szS_val, szW_val] at h; omega
  · exact bigCell_middle_col_vanish c μ _ (Or.inl (by simp [szX_val])) j
  · exact bigCell_szW_szW c μ i j
  · exact bigCell_middle_col_vanish c μ _ (Or.inr (by have := i.isLt; simp [szS_val]; omega)) j
  · rw [sz_bc_S, diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg h, if_neg]; intro h'; apply h; rw [Fin.ext_iff] at h'; simp [szX_val] at h'; exact Fin.ext h'
  · rw [sz_bc_S, if_neg]; intro h; have := i.isLt; rw [Fin.ext_iff] at h; simp [szW_val, szX_val] at h; omega
  · rw [sz_bc_S, if_neg]; intro h; have := i.isLt; have := j.isLt; rw [Fin.ext_iff] at h
    simp [szS_val, szX_val] at h; omega

end szBlocks

section szRel

variable {k r : ℕ}

lemma sz_gblocks {m p : B.Mat k r} (hm : m ∈ Nset k r) (hp : p ∈ Nset k r) (c : Fin r → ℂ)
    (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (m * bigCell k r c μ * p).submatrix (szS k r) (szX k r) =
        m.submatrix (szS k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szX k r) ∧
    (m * bigCell k r c μ * p).submatrix (szS k r) (szW k r) =
        m.submatrix (szS k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szW k r) ∧
    (m * bigCell k r c μ * p).submatrix (szS k r) (szS k r) =
        m.submatrix (szS k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szS k r) ∧
    (m * bigCell k r c μ * p).submatrix (szW k r) (szX k r) =
        m.submatrix (szW k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szX k r) ∧
    (m * bigCell k r c μ * p).submatrix (szX k r) (szX k r) =
        m.submatrix (szX k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szX k r) ∧
    (m * bigCell k r c μ * p).submatrix (szW k r) (szW k r) =
        m.submatrix (szW k r) (szS k r) * diagonal c * p.submatrix (szX k r) (szW k r) + μ := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9⟩ := sz_bc (k := k) c μ
  obtain ⟨m1, m2, m3, m4⟩ := sz_subN hm
  obtain ⟨p1, p2, p3, p4⟩ := sz_subN hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [sz_mul_sub, b1, b2, b3, b4, b5, b6, b7, b8, b9, m1, m2, m3, m4, p1, p2, p3, p4, Matrix.mul_zero,
      Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  exact add_comm _ _

lemma sz_one_sub :
    (1 : B.Mat k r).submatrix (szS k r) (szS k r) = 1 ∧ (1 : B.Mat k r).submatrix (szX k r) (szX k r) = 1 ∧
      (1 : B.Mat k r).submatrix (szW k r) (szS k r) = 0 ∧ (1 : B.Mat k r).submatrix (szX k r) (szW k r) = 0 := by
  have iS : Function.Injective (szS k r) := fun a b h => by
    have := a.isLt; have := b.isLt; rw [Fin.ext_iff] at h; simp [szS_val] at h; exact Fin.ext (by omega)
  have iX : Function.Injective (szX k r) := fun a b h => by
    rw [Fin.ext_iff] at h; simp [szX_val] at h; exact Fin.ext h
  refine ⟨Matrix.submatrix_one _ iS, Matrix.submatrix_one _ iX, ?_, ?_⟩ <;> ext i j <;>
    simp only [submatrix_apply, Matrix.one_apply, Matrix.zero_apply] <;> rw [if_neg] <;> intro h <;>
    rw [Fin.ext_iff] at h <;> simp [szS_val, szW_val, szX_val] at h <;> omega

lemma sz_inv_rows {q q' : B.Mat k r} (hq : q ∈ Nset k r) (hq' : q' ∈ Nset k r) (h : q * q' = 1) :
    q.submatrix (szS k r) (szS k r) * q'.submatrix (szS k r) (szS k r) = 1 ∧
    q'.submatrix (szW k r) (szS k r) + q.submatrix (szW k r) (szS k r) * q'.submatrix (szS k r) (szS k r) = 0 := by
  obtain ⟨m1, m2, m3, m4⟩ := sz_subN hq
  obtain ⟨p1, p2, p3, p4⟩ := sz_subN hq'
  obtain ⟨o1, o2, o3, o4⟩ := sz_one_sub (k := k) (r := r)
  have e1 := congrArg (fun M => M.submatrix (szS k r) (szS k r)) h
  have e2 := congrArg (fun M => M.submatrix (szW k r) (szS k r)) h
  simp only [sz_mul_sub, m1, m2, m3, m4, o1, o3, Matrix.zero_mul, Matrix.one_mul, zero_add] at e1 e2
  exact ⟨e1, e2⟩

lemma sz_inv_colsX {q q' : B.Mat k r} (hq : q ∈ Nset k r) (hq' : q' ∈ Nset k r) (h : q * q' = 1) :
    q.submatrix (szX k r) (szX k r) * q'.submatrix (szX k r) (szX k r) = 1 ∧
    q.submatrix (szX k r) (szX k r) * q'.submatrix (szX k r) (szW k r) + q.submatrix (szX k r) (szW k r) = 0 := by
  obtain ⟨m1, m2, m3, m4⟩ := sz_subN hq
  obtain ⟨p1, p2, p3, p4⟩ := sz_subN hq'
  obtain ⟨o1, o2, o3, o4⟩ := sz_one_sub (k := k) (r := r)
  have e1 := congrArg (fun M => M.submatrix (szX k r) (szX k r)) h
  have e2 := congrArg (fun M => M.submatrix (szX k r) (szW k r)) h
  simp only [sz_mul_sub, p1, p2, p3, p4, o2, o4, Matrix.mul_zero, Matrix.mul_one, add_zero] at e1 e2
  exact ⟨e1, e2⟩

end szRel

section szBound

def unitriangularFactorConstant {p : ℕ} (d : Fin p → ℂ) : ℝ :=
  ∑ i : Fin p, ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), d (Fin.castLE i.isLt t)‖

lemma sz_EBp {ι κ : Type*} {m : ℕ} {A : Matrix ι (Fin m) ℂ} {B : Matrix (Fin m) κ ℂ} {Q G : ℝ} (hQ : 0 ≤ Q)
    (hG : 0 ≤ G) {i j i' j' : ℕ} (hA : EB A (Q ^ i * G ^ j)) (hB : EB B (Q ^ i' * G ^ j')) (hm : (m : ℝ) ≤ Q) :
    EB (A * B) (Q ^ (i + i' + 1) * G ^ (j + j')) := by
  refine (EB_mul hA hB).mono ?_
  rw [Fintype.card_fin]
  calc (m : ℝ) * (Q ^ i * G ^ j * (Q ^ i' * G ^ j')) ≤ Q * (Q ^ i * G ^ j * (Q ^ i' * G ^ j')) :=
        mul_le_mul_of_nonneg_right hm (by positivity)
    _ = Q ^ (i + i' + 1) * G ^ (j + j') := by ring

lemma pow_mul_pow_le_pow_mul_pow_of_one_le {Q G : ℝ} (hQ : 1 ≤ Q) (hG : 1 ≤ G) {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) :
    Q ^ a * G ^ b ≤ Q ^ A * G ^ B :=
  mul_le_mul (pow_le_pow_right₀ hQ ha) (pow_le_pow_right₀ hG hb) (by positivity) (by positivity)

lemma entry_bound_mono_exponents {ι κ : Type*} {A : Matrix ι κ ℂ} {Q G : ℝ} (hQ : 1 ≤ Q) (hG : 1 ≤ G) {a b A' B' : ℕ}
    (h : EB A (Q ^ a * G ^ b)) (ha : a ≤ A') (hb : b ≤ B') : EB A (Q ^ A' * G ^ B') :=
  h.mono (pow_mul_pow_le_pow_mul_pow_of_one_le hQ hG ha hb)

lemma sz_core (k s : ℕ) (c : Fin (s + 1) → ℂ) (hc : ∀ a, c a ≠ 0) (Q : ℝ) (hQ2 : 2 ≤ Q)
    (hQr : ((s + 1 : ℕ) : ℝ) ≤ Q) (hQk : ((k + 1 : ℕ) : ℝ) ≤ Q) (hQc : ∀ a, ‖c a‖ ≤ Q) (hQK : 2 * unitriangularFactorConstant c ≤ Q)
    (hQd : (s.factorial : ℝ) / ‖∏ a, c a‖ ≤ Q) {n p : B.Mat k (s + 1)} (hn : n ∈ Nset k (s + 1))
    (hp : p ∈ Nset k (s + 1)) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (hG : 1 ≤ B.gN (n⁻¹ * bigCell k (s + 1) c μ * p)) :
    EB n (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (2 * s + 2)) ∧
    EB p (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (2 * s + 2)) ∧
    EB μ (Q ^ 5 * B.gN (n⁻¹ * bigCell k (s + 1) c μ * p) ^ (s + 2)) := by
  have hm : n⁻¹ ∈ Nset k (s + 1) := sz_N_inv hn
  obtain ⟨hZ, hSW, hSS, hWX, hXX, hWW⟩ := sz_gblocks hm hp c μ
  set m := n⁻¹ with hmdef
  set g := m * bigCell k (s + 1) c μ * p with hgdef
  set G := B.gN g with hGdef
  set L := m.submatrix (szS k (s + 1)) (szS k (s + 1)) with hLdef
  set U := p.submatrix (szX k (s + 1)) (szX k (s + 1)) with hUdef
  set Z := g.submatrix (szS k (s + 1)) (szX k (s + 1)) with hZdef
  set D := (diagonal c : Matrix (Fin (s + 1)) (Fin (s + 1)) ℂ) with hDdef
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hG0 : 0 ≤ G := by linarith
  have hr : ((s + 1 : ℕ) : ℝ) ≤ Q := hQr
  have eG : ∀ {ι κ : Type} (f : ι → Fin (2 * (s + 1) + k + 1)) (f' : κ → Fin (2 * (s + 1) + k + 1)),
      EB (g.submatrix f f') (Q ^ 0 * G ^ 1) := fun f f' a b => by
    simpa using entry_le_gN g (f a) (f' b)
  have eD : EB D (Q ^ 1 * G ^ 0) := fun a b => by
    simp only [hDdef, diagonal_apply, pow_one, pow_zero, mul_one]
    split_ifs with h
    · subst h; exact hQc a
    · simpa using hQ0

  have hL : ∀ a b, a < b → L a b = 0 := fun a b h => sz_N_SS hm a b h
  have hL1 : ∀ a, L a a = 1 := fun a => unipotent_diag_entry_szS_eq_one hm a
  have hU : ∀ a b, b < a → U a b = 0 := fun a b h => sz_N_XX hp a b h
  have hU1 : ∀ a, U a a = 1 := fun a => unipotent_diag_entry_szX_eq_one hp a
  have eZ : EB (L * D * U) G := by
    rw [← hZ]; intro a b; exact entry_le_gN g _ _
  have hGp : (1 : ℝ) ≤ G ^ (s + 1) := one_le_pow₀ hG
  have eU : EB U (Q ^ 1 * G ^ (s + 1)) := fun i j => by
    have h := upper_factor_bound L U c hc hL hL1 hU hU1 hG0 one_pos hGp eZ i j
    refine h.trans ?_
    have : unitriangularFactorConstant c * ((1 + 1⁻¹) * G ^ (s + 1)) = (2 * unitriangularFactorConstant c) * G ^ (s + 1) := by norm_num; ring
    rw [show (∑ i : Fin (s + 1), ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), c (Fin.castLE i.isLt t)‖) =
      unitriangularFactorConstant c from rfl, this, pow_one]
    exact mul_le_mul_of_nonneg_right hQK (by positivity)
  have eZt : EB (Uᵀ * D * Lᵀ) G := by
    have : Uᵀ * D * Lᵀ = (L * D * U)ᵀ := by
      rw [transpose_mul, transpose_mul, hDdef, diagonal_transpose, Matrix.mul_assoc]
    rw [this]; intro a b; exact eZ b a
  have eL : EB L (Q ^ 1 * G ^ (s + 1)) := fun i j => by
    have h := upper_factor_bound Uᵀ Lᵀ c hc (fun a b h => hU b a h) hU1 (fun a b h => hL b a h) hL1 hG0 one_pos hGp
      eZt j i
    rw [transpose_apply] at h
    refine h.trans ?_
    have : unitriangularFactorConstant c * ((1 + 1⁻¹) * G ^ (s + 1)) = (2 * unitriangularFactorConstant c) * G ^ (s + 1) := by norm_num; ring
    rw [show (∑ i : Fin (s + 1), ((i.val + 1).factorial : ℝ) / ‖∏ t : Fin (i.val + 1), c (Fin.castLE i.isLt t)‖) =
      unitriangularFactorConstant c from rfl, this, pow_one]
    exact mul_le_mul_of_nonneg_right hQK (by positivity)

  have hdetL : L.det = 1 := by
    rw [Matrix.det_of_isLowerTriangular L (fun i j h => hL i j (OrderDual.toDual_lt_toDual.mp h))]
    simp [hL1]
  have hdetU : U.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j h => hU i j h)]
    simp [hU1]
  have hdetZ : Z.det = ∏ a, c a := by
    rw [hZ, det_mul, det_mul, hdetL, hdetU, hDdef, det_diagonal]; ring
  have hZu : IsUnit Z.det := by
    rw [hdetZ]; exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun a _ => hc a)
  have eI : EB Z⁻¹ (Q ^ 1 * G ^ s) := by
    have h := inv_entry_le Z (by rw [hZ]; exact eZ)
    simp only [Nat.add_sub_cancel] at h
    refine h.mono ?_
    rw [hdetZ, pow_one, div_eq_mul_inv, mul_assoc, mul_comm (G ^ s), ← mul_assoc, ← div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hQd (by positivity)
  have hIZ : Z⁻¹ * (L * D * U) = 1 := by rw [← hZ]; exact Matrix.nonsing_inv_mul Z hZu
  have hZI : (L * D * U) * Z⁻¹ = 1 := by rw [← hZ]; exact Matrix.mul_nonsing_inv Z hZu
  have hUi : U * Z⁻¹ * L * D = 1 := by
    have : (Z⁻¹ * L * D) * U = 1 := by rw [← hIZ]; simp only [Matrix.mul_assoc]
    have := mul_eq_one_comm.mp this
    simpa only [Matrix.mul_assoc] using this
  have hUi' : Z⁻¹ * L * D * U = 1 := by rw [← hIZ]; simp only [Matrix.mul_assoc]
  have hLi : D * U * Z⁻¹ * L = 1 := by
    have : L * (D * U * Z⁻¹) = 1 := by rw [← hZI]; simp only [Matrix.mul_assoc]
    have := mul_eq_one_comm.mp this
    simpa only [Matrix.mul_assoc] using this
  have hLi' : L * D * U * Z⁻¹ = 1 := hZI

  have hpXW : p.submatrix (szX k (s + 1)) (szW k (s + 1)) =
      U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1)) := by
    rw [hSW]; simp only [← Matrix.mul_assoc]; rw [hUi, Matrix.one_mul]
  have hpXS : p.submatrix (szX k (s + 1)) (szS k (s + 1)) =
      U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szS k (s + 1)) := by
    rw [hSS]; simp only [← Matrix.mul_assoc]; rw [hUi, Matrix.one_mul]
  have hmWS : m.submatrix (szW k (s + 1)) (szS k (s + 1)) =
      g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L := by
    rw [hWX]; simp only [Matrix.mul_assoc]; rw [show D * (U * (Z⁻¹ * L)) = D * U * Z⁻¹ * L by
      simp only [Matrix.mul_assoc], hLi, Matrix.mul_one]
  have hmXS : m.submatrix (szX k (s + 1)) (szS k (s + 1)) =
      g.submatrix (szX k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L := by
    rw [hXX]; simp only [Matrix.mul_assoc]; rw [show D * (U * (Z⁻¹ * L)) = D * U * Z⁻¹ * L by
      simp only [Matrix.mul_assoc], hLi, Matrix.mul_one]
  have hμ : μ = g.submatrix (szW k (s + 1)) (szW k (s + 1)) -
      g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1)) := by
    rw [hWW, hmWS, hpXW]
    have : g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L * D *
        (U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) =
        g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1)) := by
      rw [show g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L * D *
        (U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) =
        g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * (L * D * U * Z⁻¹) *
          g.submatrix (szS k (s + 1)) (szW k (s + 1)) by simp only [Matrix.mul_assoc], hLi', Matrix.mul_one]
    rw [this]; abel

  have hnm : n * m = 1 := Matrix.mul_nonsing_inv n (sz_N_unit hn)
  obtain ⟨hn1, hn2⟩ := sz_inv_rows hn hm hnm
  have hnSS : n.submatrix (szS k (s + 1)) (szS k (s + 1)) = D * U * Z⁻¹ := by
    have : n.submatrix (szS k (s + 1)) (szS k (s + 1)) =
        n.submatrix (szS k (s + 1)) (szS k (s + 1)) * (L * (D * U * Z⁻¹)) := by
      rw [show L * (D * U * Z⁻¹) = L * D * U * Z⁻¹ by simp only [Matrix.mul_assoc], hLi', Matrix.mul_one]
    rw [this, ← Matrix.mul_assoc, hn1, Matrix.one_mul]
  have hnWS : n.submatrix (szW k (s + 1)) (szS k (s + 1)) =
      -(g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹) := by
    have h1 : n.submatrix (szW k (s + 1)) (szS k (s + 1)) * L = -m.submatrix (szW k (s + 1)) (szS k (s + 1)) :=
      eq_neg_of_add_eq_zero_left ((add_comm _ _).trans hn2)
    have : n.submatrix (szW k (s + 1)) (szS k (s + 1)) =
        n.submatrix (szW k (s + 1)) (szS k (s + 1)) * (L * (D * U * Z⁻¹)) := by
      rw [show L * (D * U * Z⁻¹) = L * D * U * Z⁻¹ by simp only [Matrix.mul_assoc], hLi', Matrix.mul_one]
    rw [this, ← Matrix.mul_assoc, h1, hmWS, Matrix.neg_mul]
    congr 1
    rw [show g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * L * (D * U * Z⁻¹) =
      g.submatrix (szW k (s + 1)) (szX k (s + 1)) * Z⁻¹ * (L * D * U * Z⁻¹) by simp only [Matrix.mul_assoc],
      hLi', Matrix.mul_one]
  have hpp : p * p⁻¹ = 1 := Matrix.mul_nonsing_inv p (sz_N_unit hp)
  obtain ⟨hp1, hp2⟩ := sz_inv_colsX hp (sz_N_inv hp) hpp
  have hpiXX : p⁻¹.submatrix (szX k (s + 1)) (szX k (s + 1)) = Z⁻¹ * L * D := by
    have : p⁻¹.submatrix (szX k (s + 1)) (szX k (s + 1)) =
        (Z⁻¹ * L * D * U) * p⁻¹.submatrix (szX k (s + 1)) (szX k (s + 1)) := by rw [hUi', Matrix.one_mul]
    rw [this, Matrix.mul_assoc (Z⁻¹ * L * D), hp1, Matrix.mul_one]
  have hpiXW : p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) =
      -(Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) := by
    have h1 : U * p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) = -p.submatrix (szX k (s + 1)) (szW k (s + 1)) :=
      eq_neg_of_add_eq_zero_left hp2
    have : p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) =
        (Z⁻¹ * L * D * U) * p⁻¹.submatrix (szX k (s + 1)) (szW k (s + 1)) := by rw [hUi', Matrix.one_mul]
    rw [this, Matrix.mul_assoc (Z⁻¹ * L * D), h1, hpXW, Matrix.mul_neg]
    congr 1
    rw [show Z⁻¹ * L * D * (U * Z⁻¹ * g.submatrix (szS k (s + 1)) (szW k (s + 1))) =
      Z⁻¹ * (L * D * U * Z⁻¹) * g.submatrix (szS k (s + 1)) (szW k (s + 1)) by simp only [Matrix.mul_assoc],
      hLi', Matrix.mul_one]

  have hk : ((k + 1 : ℕ) : ℝ) ≤ Q := hQk
  have bXW := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eU eI hr) (eG (szS k (s + 1)) (szW k (s + 1))) hr
  have bXS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eU eI hr) (eG (szS k (s + 1)) (szS k (s + 1))) hr
  have bWS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 (eG (szW k (s + 1)) (szX k (s + 1))) eI hr) eL hr
  have bmXS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 (eG (szX k (s + 1)) (szX k (s + 1))) eI hr) eL hr
  have bnSS := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eD eU hr) eI hr
  have bnWS := EB_neg (sz_EBp hQ0 hG0 (eG (szW k (s + 1)) (szX k (s + 1))) eI hr)
  have bpiXX := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 eI eL hr) eD hr
  have bpiXW := EB_neg (sz_EBp hQ0 hG0 eI (eG (szS k (s + 1)) (szW k (s + 1))) hr)
  have bμ2 := sz_EBp hQ0 hG0 (sz_EBp hQ0 hG0 (eG (szW k (s + 1)) (szX k (s + 1))) eI hr)
    (eG (szS k (s + 1)) (szW k (s + 1))) hr
  rw [← hpXW] at bXW
  rw [← hpXS] at bXS
  rw [← hmWS] at bWS
  rw [← hmXS] at bmXS
  rw [← hnSS] at bnSS
  rw [← hnWS] at bnWS
  rw [← hpiXX] at bpiXX
  rw [← hpiXW] at bpiXW
  have hT1 : (1 : ℝ) ≤ Q ^ 5 * G ^ (2 * s + 2) := by
    have := pow_mul_pow_le_pow_mul_pow_of_one_le hQ1 hG (a := 0) (b := 0) (A := 5) (B := 2 * s + 2) (by omega) (by omega); simpa using this
  have h0T : (0 : ℝ) ≤ Q ^ 5 * G ^ (2 * s + 2) := by linarith
  have hmG : m ∈ B.GV k (s + 1) := sz_N_GV hm
  have hpiG : p⁻¹ ∈ B.GV k (s + 1) := sz_N_GV (sz_N_inv hp)
  have hpinv : (p⁻¹)⁻¹ = p := Matrix.nonsing_inv_nonsing_inv p (sz_N_unit hp)
  have hninv : m⁻¹ = n := Matrix.nonsing_inv_nonsing_inv n (sz_N_unit hn)
  refine ⟨?_, ?_, ?_⟩
  ·
    intro i j
    rcases sz_cases i with ⟨a, rfl⟩ | ⟨v, rfl⟩ | ⟨a, rfl⟩ <;> rcases sz_cases j with ⟨b, rfl⟩ | ⟨w, rfl⟩ | ⟨b, rfl⟩
    · rw [← hninv, sz_norm_inv hmG, sz_sig_X, sz_sig_X]
      exact (entry_bound_mono_exponents hQ1 hG eL (by omega) (by omega)) b a
    · rw [← hninv, sz_norm_inv hmG, sz_sig_X, involution_fixes_middle_basis]
      exact (entry_bound_mono_exponents hQ1 hG bWS (by omega) (by omega)) w a
    · rw [← hninv, sz_norm_inv hmG, sz_sig_X, sz_sig_S]
      exact (entry_bound_mono_exponents hQ1 hG bmXS (by omega) (by omega)) b a
    · rw [sz_N_WX hn]; simpa using h0T
    · rw [sz_N_WW hn]; split_ifs <;> simp [hT1, h0T]
    · exact (entry_bound_mono_exponents hQ1 hG bnWS (by omega) (by omega)) v b
    · rw [sz_N_SX hn]; simpa using h0T
    · rw [sz_N_SW hn]; simpa using h0T
    · exact (entry_bound_mono_exponents hQ1 hG bnSS (by omega) (by omega)) a b
  ·
    intro i j
    rcases sz_cases i with ⟨a, rfl⟩ | ⟨v, rfl⟩ | ⟨a, rfl⟩ <;> rcases sz_cases j with ⟨b, rfl⟩ | ⟨w, rfl⟩ | ⟨b, rfl⟩
    · exact (entry_bound_mono_exponents hQ1 hG eU (by omega) (by omega)) a b
    · exact (entry_bound_mono_exponents hQ1 hG bXW (by omega) (by omega)) a w
    · exact (entry_bound_mono_exponents hQ1 hG bXS (by omega) (by omega)) a b
    · rw [sz_N_WX hp]; simpa using h0T
    · rw [sz_N_WW hp]; split_ifs <;> simp [hT1, h0T]
    · rw [← hpinv, sz_norm_inv hpiG, involution_fixes_middle_basis, sz_sig_S]
      exact (entry_bound_mono_exponents hQ1 hG bpiXW (by omega) (by omega)) b v
    · rw [sz_N_SX hp]; simpa using h0T
    · rw [sz_N_SW hp]; simpa using h0T
    · rw [← hpinv, sz_norm_inv hpiG, sz_sig_S, sz_sig_S]
      exact (entry_bound_mono_exponents hQ1 hG bpiXX (by omega) (by omega)) b a
  ·
    rw [hμ]
    refine (EB_sub (eG (szW k (s + 1)) (szW k (s + 1))) bμ2).mono ?_
    have h1 := pow_mul_pow_le_pow_mul_pow_of_one_le hQ1 hG (a := 0) (b := 1) (A := 3) (B := s + 2) (by omega) (by omega)
    have h2 := pow_mul_pow_le_pow_mul_pow_of_one_le hQ1 hG (a := 0 + 1 + 1 + 0 + 1) (b := 1 + s + 1) (A := 3) (B := s + 2) (by omega) (by omega)
    have h3 : Q ^ 3 * G ^ (s + 2) + Q ^ 3 * G ^ (s + 2) ≤ Q ^ 5 * G ^ (s + 2) := by
      have hQ3 : 0 ≤ Q ^ 3 := pow_nonneg hQ0 3
      have hq : 2 * Q ^ 3 ≤ Q ^ 5 := by
        have e5 : Q ^ 5 = Q ^ 2 * Q ^ 3 := by ring
        have hQsq : (2 : ℝ) ≤ Q ^ 2 := by nlinarith
        rw [e5]; exact mul_le_mul_of_nonneg_right hQsq hQ3
      have hg : 0 ≤ G ^ (s + 2) := by positivity
      have := mul_le_mul_of_nonneg_right hq hg
      linarith
    linarith

end szBound

section szMain

lemma sz_hb_eq (k : ℕ) :
    Hb k = Matrix.reindex (finCongr (by omega : 2 * 0 + k + 1 = k + 1))
      (finCongr (by omega : 2 * 0 + k + 1 = k + 1)) (Hpk k 0) := by
  ext a b
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Hb, Hpk, Matrix.diagonal_apply, finCongr_symm,
    finCongr_apply]
  by_cases hab : a = b
  · subst hab
    by_cases ha : a = Fin.last k
    · subst ha; simp
    · have : a.val ≠ k := fun h => ha (Fin.ext (by simp [h]))
      simp [ha, this]
      have := a.isLt; omega
  · have : a.val ≠ b.val := fun h => hab (Fin.ext h)
    simp [hab, this]

lemma sz_castW_mem {k : ℕ} (μ : B.Mat k 0) (hμ : μ ∈ B.GV k 0) : (castW μ)ᴴ * Hb k * castW μ = Hb k := by
  have h : μᴴ * Hpk k 0 * μ = Hpk k 0 := hμ
  rw [sz_hb_eq, castW]
  simp only [Matrix.reindex_apply]
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]

lemma sz_castW_apply {k : ℕ} (μ : B.Mat k 0) (i j : Fin (2 * 0 + k + 1)) :
    μ i j = castW μ (finCongr (by omega) i) (finCongr (by omega) j) := by
  simp [castW, Matrix.reindex_apply]

lemma sz_phi_mem {k r : ℕ} (c : Fin r → ℂ) (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r} (hn : n ∈ Nset k r)
    (hn' : n' ∈ Nset k r) {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0) : phi k r c n n' μ ∈ B.GV k r := by
  unfold phi
  exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (sz_N_GV (sz_N_inv hn))
    (big_cell_mem_holds k r c (castW μ) hc (sz_castW_mem μ hμ))) (sz_N_GV hn')

lemma sz_N_one (k r : ℕ) : (1 : B.Mat k r) ∈ Nset k r := (Formalism.FourierDecayAlt.P.unipotent_radical_closed k r).one_mem

lemma sz_N_zero {k : ℕ} {q : B.Mat k 0} (hq : q ∈ Nset k 0) : q = 1 := by
  ext i j
  have hj := j.isLt
  rw [hq.2.2 i j (Nat.zero_le _) (by omega) (Nat.zero_le _), Matrix.one_apply]

lemma sz_bc_zero {k : ℕ} (c : Fin 0 → ℂ) (μ : B.Mat k 0) (i j : Fin (2 * 0 + k + 1)) :
    bigCell k 0 c (castW μ) i j = μ i j := by
  have hi := i.isLt; have hj := j.isLt
  unfold bigCell
  rw [dif_neg (by omega), dif_pos (by omega), dif_pos (by omega), sz_castW_apply μ i j]
  congr 1 <;> apply Fin.ext <;> simp

lemma sz_contK {r : ℕ} (s : ℕ) (K : Set (Fin r → ℂ)) (hK0 : ∀ c ∈ K, ∀ a, c a ≠ 0) :
    ContinuousOn (fun c : Fin r → ℂ => 2 * unitriangularFactorConstant c + ∑ a, ‖c a‖ + (s.factorial : ℝ) / ‖∏ a, c a‖) K := by
  have hp : ∀ (q : ℕ) (f : Fin q → Fin r), ContinuousOn (fun c : Fin r → ℂ => ‖∏ t, c (f t)‖) K :=
    fun q f => (continuous_finset_prod _ fun t _ => continuous_apply (f t)).norm.continuousOn
  have hne : ∀ (q : ℕ) (f : Fin q → Fin r), ∀ c ∈ K, ‖∏ t, c (f t)‖ ≠ 0 := fun q f c hc => by
    rw [norm_ne_zero_iff]; exact Finset.prod_ne_zero_iff.mpr fun t _ => hK0 c hc (f t)
  refine ((continuousOn_const.mul ?_).add ?_).add ?_
  · unfold unitriangularFactorConstant
    exact continuousOn_finset_sum _ fun i _ => continuousOn_const.div (hp _ _) (hne _ _)
  · exact continuousOn_finset_sum _ fun a _ => (continuous_apply a).norm.continuousOn
  · exact (continuousOn_const (c := (s.factorial : ℝ)) (s := K)).div (hp r id) (hne r id)

theorem sizes (k r : ℕ) (K : Set (Fin r → ℂ)) (hK : IsCompact K) (hK0 : ∀ c ∈ K, ∀ a, c a ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨((2 * 0 + k + 1 : ℕ) : ℝ), by positivity, fun c hc n hn n' hn' μ hμ => ?_⟩
    rw [sz_N_zero hn, sz_N_zero hn']
    have hb : phi k 0 c 1 1 μ = bigCell k 0 c (castW μ) := by simp [phi]
    have hG : 1 ≤ B.gN (phi k 0 c 1 1 μ) :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (sz_phi_mem c (hK0 c hc) (sz_N_one k 0) (sz_N_one k 0) hμ)
    have e1 : B.gN (1 : B.Mat k 0) ≤ ((2 * 0 + k + 1 : ℕ) : ℝ) * 1 :=
      gN_le_of_EB _ (fun i j => by rw [Matrix.one_apply]; split_ifs <;> simp) (by norm_num)
    refine ⟨by simpa using e1, by simpa using e1, ?_⟩
    have eμ : EB μ (B.gN (phi k 0 c 1 1 μ)) := fun i j => by
      rw [← sz_bc_zero c μ i j, ← hb]; exact entry_le_gN _ i j
    refine (gN_le_of_EB μ eμ (by linarith)).trans ?_
    rw [zero_add, pow_one]
  · obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    obtain ⟨Bd, hBd⟩ := hK.exists_bound_of_continuousOn (sz_contK s K hK0)
    set Q : ℝ := |Bd| + 2 + ((s + 1 : ℕ) : ℝ) + ((k + 1 : ℕ) : ℝ) with hQdef
    refine ⟨((2 * (s + 1) + k + 1 : ℕ) : ℝ) * Q ^ 5, by positivity, fun c hc n hn n' hn' μ hμ => ?_⟩
    have hc0 := hK0 c hc
    have hf := hBd c hc
    have hK1 : 0 ≤ unitriangularFactorConstant c := by unfold unitriangularFactorConstant; exact Finset.sum_nonneg fun i _ => by positivity
    have hsum : 0 ≤ ∑ a, ‖c a‖ := Finset.sum_nonneg fun a _ => norm_nonneg _
    have hd : 0 ≤ (s.factorial : ℝ) / ‖∏ a, c a‖ := by positivity
    have hfe : ‖2 * unitriangularFactorConstant c + ∑ a, ‖c a‖ + (s.factorial : ℝ) / ‖∏ a, c a‖‖ =
        2 * unitriangularFactorConstant c + ∑ a, ‖c a‖ + (s.factorial : ℝ) / ‖∏ a, c a‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hfe] at hf
    have hBdQ' : Bd ≤ Q := by
      rw [hQdef]
      have h1 := le_abs_self Bd
      have h2 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQ2 : 2 ≤ Q := by
      rw [hQdef]
      have h1 := abs_nonneg Bd
      have h2 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by positivity
      have h3 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQr : ((s + 1 : ℕ) : ℝ) ≤ Q := by
      rw [hQdef]
      have h1 := abs_nonneg Bd
      have h3 : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQk : ((k + 1 : ℕ) : ℝ) ≤ Q := by
      rw [hQdef]
      have h1 := abs_nonneg Bd
      have h2 : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by positivity
      linarith
    have hQc : ∀ a, ‖c a‖ ≤ Q := fun a => by
      have := Finset.single_le_sum (f := fun a => ‖c a‖) (fun a _ => norm_nonneg _) (Finset.mem_univ a)
      linarith
    have hQK : 2 * unitriangularFactorConstant c ≤ Q := by linarith
    have hQd : (s.factorial : ℝ) / ‖∏ a, c a‖ ≤ Q := by linarith
    have hG : 1 ≤ B.gN (n⁻¹ * bigCell k (s + 1) c (castW μ) * n') :=
      Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (sz_phi_mem c hc0 hn hn' hμ)
    obtain ⟨e1, e2, e3⟩ := sz_core k s c hc0 Q hQ2 hQr hQk hQc hQK hQd hn hn' (castW μ) hG
    have hphi : phi k (s + 1) c n n' μ = n⁻¹ * bigCell k (s + 1) c (castW μ) * n' := rfl
    rw [hphi]
    set G := B.gN (n⁻¹ * bigCell k (s + 1) c (castW μ) * n')
    have hG0 : 0 ≤ G := by linarith
    have hQ0 : 0 ≤ Q := by linarith
    have hT : 0 ≤ Q ^ 5 * G ^ (2 * s + 2) := by positivity
    have e2r : 2 * (s + 1) = 2 * s + 2 := by ring
    refine ⟨?_, ?_, ?_⟩
    · rw [e2r]; refine (gN_le_of_EB n e1 hT).trans (le_of_eq ?_); ring
    · rw [e2r]; refine (gN_le_of_EB n' e2 hT).trans (le_of_eq ?_); ring
    · have eμ : EB μ (Q ^ 5 * G ^ (s + 2)) := fun i j => by rw [sz_castW_apply μ i j]; exact e3 _ _
      have hT' : 0 ≤ Q ^ 5 * G ^ (s + 2) := by positivity
      refine (gN_le_of_EB μ eμ hT').trans ?_
      rw [show s + 1 + 1 = s + 2 by ring, mul_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : 2 * 0 + k + 1 ≤ 2 * (s + 1) + k + 1)) hT'

end szMain

end Formalism.FourierDecayAlt.P.SliceLastLevel

end PartSz

section PartTr
open Matrix MeasureTheory Filter Topology

set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.SliceLastLevel

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

lemma tr_expSeries_summable {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Summable (fun m : ℕ => ((m.factorial : ℂ))⁻¹ • X ^ m) := by
  letI : SeminormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℂ _
  exact NormedSpace.expSeries_summable' (𝕂 := ℂ) X

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {k r : ℕ}

lemma tr_castW_mul (a b : B.Mat k 0) : castW (a * b) = castW a * castW b := by
  unfold castW
  simp only [Matrix.reindex_apply]
  rw [Matrix.submatrix_mul_equiv]

lemma tr_castW_one : castW (1 : B.Mat k 0) = 1 := by
  unfold castW
  simp

lemma tr_castW_add (a b : B.Mat k 0) : castW (a + b) = castW a + castW b := by
  ext i j
  simp [castW]

lemma tr_castW_ct (a : B.Mat k 0) : (castW a)ᴴ = castW aᴴ := by
  unfold castW
  simp

lemma tr_hb_eq : Hb k = castW (Hpk k 0) := by
  ext i j
  simp only [castW, Matrix.reindex_apply, Matrix.submatrix_apply, Hb, Matrix.diagonal_apply, Hpk]
  by_cases hij : i = j
  · subst hij
    by_cases hl : i = Fin.last k
    · subst hl
      simp [Fin.last]
    · have hv : (i : ℕ) ≠ k := fun h => hl (Fin.ext (by simpa [Fin.last] using h))
      have hlt : (i : ℕ) < k + 1 := i.isLt
      simp [hl, hv]
      omega
  · have hv : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
    simp [hij, Fin.ext_iff, hv]

lemma tr_castW_mem {μ : B.Mat k 0} (hμ : μ ∈ GV k 0) : (castW μ)ᴴ * Hb k * castW μ = Hb k := by
  have h : μᴴ * Hpk k 0 * μ = Hpk k 0 := hμ
  rw [tr_hb_eq, tr_castW_ct, ← tr_castW_mul, ← tr_castW_mul, h]

lemma levelEmbed_eq_conj_cast (Y : B.Mat k 0) : emb0 k r Y = P.B2x3.Em k r * castW Y * (P.B2x3.Em k r)ᵀ := by
  ext i j
  by_cases hj : P.TwoByOneBlock.mid k r j
  · rw [P.B2x3.mul_EmT_mid _ j i hj]
    by_cases hi : P.TwoByOneBlock.mid k r i
    · rw [P.B2x3.Em_mul_mid _ i _ hi]
      unfold emb0
      rw [dif_pos ⟨hi, hj⟩]
      simp only [castW, Matrix.reindex_apply, Matrix.submatrix_apply]
      congr 1
    · rw [P.B2x3.Em_mul_out _ i _ hi]
      unfold emb0
      rw [dif_neg (fun h => hi h.1)]
  · rw [P.B2x3.mul_EmT_out _ j i hj]
    unfold emb0
    rw [dif_neg (fun h => hj h.2)]

lemma tr_castW_smul (c : ℂ) (a : B.Mat k 0) : castW (c • a) = c • castW a := by
  ext i j
  simp [castW]

lemma tr_castW_neg (a : B.Mat k 0) : castW (-a) = -castW a := by
  ext i j
  simp [castW]

lemma tr_EmT_Em : (P.B2x3.Em k r)ᵀ * P.B2x3.Em k r = 1 := P.B2x3.EmT_Em

lemma levelEmbed_mul (a b : B.Mat k 0) : emb0 k r a * emb0 k r b = emb0 k r (a * b) := by
  rw [levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, tr_castW_mul]
  calc P.B2x3.Em k r * castW a * (P.B2x3.Em k r)ᵀ * (P.B2x3.Em k r * castW b * (P.B2x3.Em k r)ᵀ)
      = P.B2x3.Em k r * castW a * ((P.B2x3.Em k r)ᵀ * P.B2x3.Em k r) * castW b * (P.B2x3.Em k r)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [tr_EmT_Em, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma levelEmbed_add (a b : B.Mat k 0) : emb0 k r (a + b) = emb0 k r a + emb0 k r b := by
  rw [levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, tr_castW_add, Matrix.mul_add, Matrix.add_mul]

lemma levelEmbed_smul (c : ℂ) (a : B.Mat k 0) : emb0 k r (c • a) = c • emb0 k r a := by
  rw [levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, tr_castW_smul, Matrix.mul_smul, Matrix.smul_mul]

lemma levelEmbed_neg (a : B.Mat k 0) : emb0 k r (-a) = -emb0 k r a := by
  rw [levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, tr_castW_neg, Matrix.mul_neg, Matrix.neg_mul]

lemma levelEmbed_pow_succ (a : B.Mat k 0) : ∀ n : ℕ, emb0 k r a ^ (n + 1) = emb0 k r (a ^ (n + 1))
  | 0 => by simp
  | n + 1 => by rw [pow_succ, levelEmbed_pow_succ a n, levelEmbed_mul, ← pow_succ]

lemma tr_embWb_castW (a : B.Mat k 0) : B2.embWb k r (castW a) = 1 - emb0 k r 1 + emb0 k r a := by
  rw [P.B2x3.emb_eq, levelEmbed_eq_conj_cast, levelEmbed_eq_conj_cast, tr_castW_one, Matrix.mul_one]
  abel

def tr_emb0L (k r : ℕ) : B.Mat k 0 →L[ℂ] B.Mat k r :=
  LinearMap.toContinuousLinearMap
    { toFun := emb0 k r
      map_add' := levelEmbed_add
      map_smul' := levelEmbed_smul }

lemma tr_emb0L_apply (a : B.Mat k 0) : tr_emb0L k r a = emb0 k r a := rfl

lemma exp_levelEmbed (Y : B.Mat k 0) :
    NormedSpace.exp (emb0 k r Y) = 1 - emb0 k r 1 + emb0 k r (NormedSpace.exp Y) := by
  have hs1 := tr_expSeries_summable (emb0 k r Y)
  have hs0 := tr_expSeries_summable Y
  have hs0' := (summable_nat_add_iff 1).2 hs0
  rw [NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  rw [hs1.tsum_eq_zero_add, hs0.tsum_eq_zero_add]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
  rw [levelEmbed_add, ← tr_emb0L_apply (∑' n, _), ContinuousLinearMap.map_tsum _ hs0']
  simp only [tr_emb0L_apply, levelEmbed_smul, ← levelEmbed_pow_succ]
  abel

lemma tr_bigCell_left (c : Fin r → ℂ) (a μ : B.Mat k 0) :
    bigCell k r c (castW (a * μ)) = B2.embWb k r (castW a) * bigCell k r c (castW μ) := by
  rw [tr_castW_mul, (P.bruhat_big_cell_factorization k r c _).2, (P.bruhat_big_cell_factorization k r c (castW μ)).2,
    P.TwoByOneBlock.emb_mul, Matrix.mul_assoc]

lemma tr_bigCell_right (c : Fin r → ℂ) (a μ : B.Mat k 0) :
    bigCell k r c (castW (μ * a)) = bigCell k r c (castW μ) * B2.embWb k r (castW a) := by
  rw [tr_castW_mul, (P.bruhat_big_cell_factorization k r c _).1, (P.bruhat_big_cell_factorization k r c (castW μ)).1,
    P.TwoByOneBlock.emb_mul, Matrix.mul_assoc]

lemma tr_embWb_exp (Z : B.Mat k 0) : B2.embWb k r (castW (NormedSpace.exp Z)) = NormedSpace.exp (emb0 k r Z) := by
  rw [tr_embWb_castW, exp_levelEmbed]

lemma phi_exp_left (c : Fin r → ℂ) {n : B.Mat k r} (n' : B.Mat k r) (hn : IsUnit n.det) (Y : B.Mat k 0) (t : ℝ)
    (μ : B.Mat k 0) :
    phi k r c n n' (NormedSpace.exp (-((t : ℂ) • Y)) * μ) =
      NormedSpace.exp (-((t : ℂ) • (n⁻¹ * emb0 k r Y * n))) * phi k r c n n' μ := by
  have hU : IsUnit n := (Matrix.isUnit_iff_isUnit_det _).2 hn
  have e : NormedSpace.exp (-((t : ℂ) • (n⁻¹ * emb0 k r Y * n))) =
      n⁻¹ * NormedSpace.exp (emb0 k r (-((t : ℂ) • Y))) * n := by
    rw [← Matrix.exp_conj' _ _ hU, levelEmbed_neg, levelEmbed_smul]
    rw [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul]
  unfold phi
  rw [tr_bigCell_left, tr_embWb_exp, e]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ n n⁻¹, Matrix.mul_nonsing_inv _ hn, Matrix.mul_one]

lemma phi_exp_right (c : Fin r → ℂ) (n : B.Mat k r) {n' : B.Mat k r} (hn' : IsUnit n'.det) (Y : B.Mat k 0) (t : ℝ)
    (μ : B.Mat k 0) :
    phi k r c n n' (μ * NormedSpace.exp ((t : ℂ) • Y)) =
      phi k r c n n' μ * NormedSpace.exp ((t : ℂ) • (n'⁻¹ * emb0 k r Y * n')) := by
  have hU : IsUnit n' := (Matrix.isUnit_iff_isUnit_det _).2 hn'
  have e : NormedSpace.exp ((t : ℂ) • (n'⁻¹ * emb0 k r Y * n')) =
      n'⁻¹ * NormedSpace.exp (emb0 k r ((t : ℂ) • Y)) * n' := by
    rw [← Matrix.exp_conj' _ _ hU, levelEmbed_smul]
    rw [Matrix.mul_smul, Matrix.smul_mul]
  unfold phi
  rw [tr_bigCell_right, tr_embWb_exp, e]
  simp only [← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ n' n'⁻¹, Matrix.mul_nonsing_inv _ hn', Matrix.mul_one]

section transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma tr_rdV_phi (c : Fin r → ℂ) (n : B.Mat k r) {n' : B.Mat k r} (hn' : IsUnit n'.det) (Y : B.Mat k 0)
    (f : B.Mat k r → E) (μ : B.Mat k 0) :
    RdV Y (fun μ => f (phi k r c n n' μ)) μ = RdV (n'⁻¹ * emb0 k r Y * n') f (phi k r c n n' μ) := by
  show deriv (fun t : ℝ => f (phi k r c n n' (μ * NormedSpace.exp ((t : ℂ) • Y)))) 0 =
    deriv (fun t : ℝ => f (phi k r c n n' μ * NormedSpace.exp ((t : ℂ) • (n'⁻¹ * emb0 k r Y * n')))) 0
  simp only [phi_exp_right c n hn']

lemma tr_ldV_phi (c : Fin r → ℂ) {n : B.Mat k r} (n' : B.Mat k r) (hn : IsUnit n.det) (Y : B.Mat k 0)
    (f : B.Mat k r → E) (μ : B.Mat k 0) :
    LdV Y (fun μ => f (phi k r c n n' μ)) μ = LdV (n⁻¹ * emb0 k r Y * n) f (phi k r c n n' μ) := by
  show deriv (fun t : ℝ => f (phi k r c n n' (NormedSpace.exp (-((t : ℂ) • Y)) * μ))) 0 =
    deriv (fun t : ℝ => f (NormedSpace.exp (-((t : ℂ) • (n⁻¹ * emb0 k r Y * n))) * phi k r c n n' μ)) 0
  simp only [phi_exp_left c n' hn]

lemma tr_rw_phi (c : Fin r → ℂ) (n : B.Mat k r) {n' : B.Mat k r} (hn' : IsUnit n'.det) :
    ∀ (v : List (B.Mat k 0)) (f : B.Mat k r → E),
      Rw v (fun μ => f (phi k r c n n' μ)) =
        fun μ => Rw (v.map fun Y => n'⁻¹ * emb0 k r Y * n') f (phi k r c n n' μ)
  | [], _ => rfl
  | Y :: v, f => by
    funext μ
    show RdV Y (Rw v (fun μ => f (phi k r c n n' μ))) μ =
      RdV (n'⁻¹ * emb0 k r Y * n') (Rw (v.map fun Y => n'⁻¹ * emb0 k r Y * n') f) (phi k r c n n' μ)
    rw [tr_rw_phi c n hn' v f, tr_rdV_phi c n hn']

lemma tr_lw_phi (c : Fin r → ℂ) {n : B.Mat k r} (n' : B.Mat k r) (hn : IsUnit n.det) :
    ∀ (u : List (B.Mat k 0)) (f : B.Mat k r → E),
      u.foldr LdV (fun μ => f (phi k r c n n' μ)) =
        fun μ => (u.map fun Y => n⁻¹ * emb0 k r Y * n).foldr LdV f (phi k r c n n' μ)
  | [], _ => rfl
  | Y :: u, f => by
    funext μ
    show LdV Y (u.foldr LdV (fun μ => f (phi k r c n n' μ))) μ =
      LdV (n⁻¹ * emb0 k r Y * n) ((u.map fun Y => n⁻¹ * emb0 k r Y * n).foldr LdV f) (phi k r c n n' μ)
    rw [tr_lw_phi c n' hn u f, tr_ldV_phi c n' hn]

theorem dLR_phi (c : Fin r → ℂ) {n n' : B.Mat k r} (hn : IsUnit n.det) (hn' : IsUnit n'.det) (f : B.Mat k r → E)
    (u v : List (B.Mat k 0)) :
    dLR u v (fun μ => f (phi k r c n n' μ)) =
      fun μ => dLR (u.map fun Y => n⁻¹ * emb0 k r Y * n) (v.map fun Y => n'⁻¹ * emb0 k r Y * n') f (phi k r c n n' μ) := by
  unfold dLR
  rw [tr_rw_phi c n hn' v f]
  exact tr_lw_phi c n' hn u (fun g => Rw (v.map fun Y => n'⁻¹ * emb0 k r Y * n') f g)

end transport

lemma tr_gN_nonneg (g : B.Mat k r) : 0 ≤ B.gN g := Real.sqrt_nonneg _

lemma gN_mul_le (X X' : B.Mat k r) : B.gN (X * X') ≤ B.gN X * B.gN X' := P.B6.gN_mul_le X X'

lemma norm_le_gN (X : B.Mat k r) : ‖X‖ ≤ B.gN X :=
  (Matrix.norm_le_iff (tr_gN_nonneg X)).2 fun i j => P.Ux5.entry_le_gN X i j

lemma tr_inv_GV {n : B.Mat k r} (hn : n ∈ B.GV k r) : n⁻¹ = Hpk k r * nᴴ * Hpk k r := by
  apply Matrix.inv_eq_left_inv
  have h : nᴴ * Hpk k r * n = Hpk k r := hn
  calc Hpk k r * nᴴ * Hpk k r * n = Hpk k r * (nᴴ * Hpk k r * n) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [h, (hpkFacts k r).2.1]

lemma gN_inv_GV {n : B.Mat k r} (hn : n ∈ B.GV k r) : B.gN n⁻¹ = B.gN n := by
  have hH1 : (Hpk k r)ᴴ = Hpk k r := (hpkFacts k r).1
  have hH2 : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have h2 : B.gN n⁻¹ ^ 2 = B.gN n ^ 2 := by
    rw [P.HermitianFormFactor.gN_sq, P.HermitianFormFactor.gN_sq, tr_inv_GV hn]
    have e : Hpk k r * nᴴ * Hpk k r * (Hpk k r * nᴴ * Hpk k r)ᴴ = Hpk k r * (nᴴ * n) * Hpk k r := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH1]
      calc Hpk k r * nᴴ * Hpk k r * (Hpk k r * (n * Hpk k r))
          = Hpk k r * nᴴ * (Hpk k r * Hpk k r) * n * Hpk k r := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hH2, Matrix.mul_one]; simp only [Matrix.mul_assoc]
    rw [e, Matrix.trace_mul_cycle, hH2, Matrix.one_mul, Matrix.trace_mul_comm]
  rw [← Real.sqrt_sq (tr_gN_nonneg n⁻¹), h2, Real.sqrt_sq (tr_gN_nonneg n)]

lemma tr_castW_zero : castW (0 : B.Mat k 0) = 0 := by
  ext i j
  simp [castW]

lemma block_embedding_skew_hermitian {Y : B.Mat k 0} (hY : B.inLie k 0 Y) : B.inLie k r (emb0 k r Y) := by
  have hY' : Yᴴ * Hpk k 0 + Hpk k 0 * Y = 0 := hY
  have hc : (castW Y)ᴴ * Hb k + Hb k * castW Y = 0 := by
    rw [tr_hb_eq, tr_castW_ct, ← tr_castW_mul, ← tr_castW_mul, ← tr_castW_add, hY', tr_castW_zero]
  show (emb0 k r Y)ᴴ * Hpk k r + Hpk k r * emb0 k r Y = 0
  rw [levelEmbed_eq_conj_cast, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, P.B2x3.EmT_conjT, P.B2x3.Em_conjT]
  calc P.B2x3.Em k r * ((castW Y)ᴴ * (P.B2x3.Em k r)ᵀ) * Hpk k r +
        Hpk k r * (P.B2x3.Em k r * castW Y * (P.B2x3.Em k r)ᵀ)
      = P.B2x3.Em k r * (castW Y)ᴴ * ((P.B2x3.Em k r)ᵀ * Hpk k r) +
        (Hpk k r * P.B2x3.Em k r) * castW Y * (P.B2x3.Em k r)ᵀ := by simp only [Matrix.mul_assoc]
    _ = P.B2x3.Em k r * ((castW Y)ᴴ * Hb k + Hb k * castW Y) * (P.B2x3.Em k r)ᵀ := by
        rw [P.B2x3.EmT_Hpk, P.B2x3.Hpk_Em]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hc, Matrix.mul_zero, Matrix.zero_mul]

lemma phi_mem {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r} (hn : n ∈ B.GV k r) (hn' : n' ∈ B.GV k r)
    {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0) : phi k r c n n' μ ∈ B.GV k r :=
  P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_inv hn) (big_cell_mem_holds k r c (castW μ) hc (tr_castW_mem hμ))) hn'

lemma tr_cd_bigCell (c : Fin r → ℂ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun μ : B.Mat k 0 => bigCell k r c (castW μ)) Set.univ := by
  rw [P.Ux10.cdm_iff]
  intro i j
  unfold bigCell castW
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
  split_ifs
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact ((contDiff_apply ℝ ℂ _).comp (contDiff_apply ℝ (Fin (2 * 0 + k + 1) → ℂ) _)).contDiffOn
  · exact contDiffOn_const
  · exact contDiffOn_const
  · exact contDiffOn_const

lemma tr_cd_phi (c : Fin r → ℂ) (n n' : B.Mat k r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (phi k r c n n') Set.univ := by
  unfold phi
  exact P.Ux10.cdm_mul (P.Ux10.cdm_mul contDiffOn_const (tr_cd_bigCell c)) contDiffOn_const

lemma continuous_phi_mu (c : Fin r → ℂ) (n n' : B.Mat k r) : Continuous (phi k r c n n') := by
  rw [← continuousOn_univ]
  exact (tr_cd_phi c n n').continuousOn

lemma ckOn_phi {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r} (hn : n ∈ B.GV k r) (hn' : n' ∈ B.GV k r)
    {m : ℕ∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn m (B.GV k r) f) : B.CkOn m (B.GV k 0) (fun μ => f (phi k r c n n' μ)) := by
  intro μ₀ hμ₀
  obtain ⟨U, f', hU, hgU, hf', hagree⟩ := hf _ (phi_mem hc hn hn' hμ₀)
  refine ⟨phi k r c n n' ⁻¹' U, fun μ => f' (phi k r c n n' μ), hU.preimage (continuous_phi_mu c n n'), hgU, ?_, ?_⟩
  · exact hf'.comp ((tr_cd_phi c n n').mono (Set.subset_univ _) |>.of_le (by exact_mod_cast le_top))
      (fun μ hμ => hμ)
  · intro μ hμ hμG
    exact hagree _ hμ (phi_mem hc hn hn' hμG)

lemma ae_mem_N {μN : Measure (Mt k r)} (hN : IsHaarOn (Nset k r) μN) :
    ∀ᵐ x ∂μN, (Matrix.of x : B.Mat k r) ∈ Nset k r :=
  P.LongWeylElement.haar_ae hN

lemma tr_f_meas (A : ℝ) : Measurable fun g : Mt k r => ENNReal.ofReal (B.gN (Matrix.of g : B.Mat k r) ^ (-A)) :=
  ENNReal.measurable_ofReal.comp ((P.HaarUniquenessConjugation.gN_meas k r).pow_const _)

lemma tr_meas_bigCell : @Measurable (Fin r → ℂ) (Mt k r) _ _ (fun c => bigCell k r c 1) := by
  refine measurable_pi_lambda (fun c : Fin r → ℂ => fun i j => bigCell k r c 1 i j) fun i => ?_
  refine measurable_pi_lambda (fun c : Fin r → ℂ => fun j => bigCell k r c 1 i j) fun j => ?_
  unfold bigCell
  split_ifs
  all_goals first
    | exact measurable_const
    | exact measurable_pi_apply (X := fun _ : Fin r => ℂ) _
    | exact (continuous_star.measurable.comp (measurable_pi_apply (X := fun _ : Fin r => ℂ) _)).inv

lemma tr_cWeight_cont : Continuous (B2.cWeight k r) := by
  unfold B2.cWeight
  exact continuous_finsetProd _ fun a _ => (continuous_norm.comp (continuous_apply a)).pow _

lemma tr_f_pos {A : ℝ} {g : B.Mat k r} (hg : g ∈ B.GV k r) : 0 < ENNReal.ofReal (B.gN g ^ (-A)) :=
  ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos (P.BetaSesquilinearity.gN_ge_one hg)) _)

lemma tr_bigCell_one_mem {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) : bigCell k r c 1 ∈ B.GV k r :=
  big_cell_mem_holds k r c 1 hc (by simp)

theorem intN_AB {μN : Measure (Mt k r)} (hN : IsHaarOn (Nset k r) μN) :
    ∫⁻ x, ENNReal.ofReal (B.gN (Matrix.of x : B.Mat k r) ^ (-(B.AB k r))) ∂μN < ⊤ := by
  classical
  haveI := P.LongWeylElement.sf hN
  obtain ⟨μG, hG⟩ := P.unitary_group_haar_exists k r
  obtain ⟨μb, hb⟩ := P.opposite_weyl_haar_exists k r
  haveI := P.LongWeylElement.sf hb
  set A := B.AB k r with hA
  have hA0 : 0 ≤ A := by
    rw [hA]; unfold B.AB; positivity
  set f : Mt k r → ENNReal := fun g => ENNReal.ofReal (B.gN (Matrix.of g : B.Mat k r) ^ (-A)) with hfdef
  have hfm : Measurable f := tr_f_meas A
  obtain ⟨C, hC, hI⟩ := P.iterated_integration_formula k r μG μN μb hG hN hb
  have hfin : (∫⁻ g, f g ∂μG) < ⊤ := P.norm_power_integrable_sharp k r μG A hG le_rfl
  rw [hI f hfm] at hfin
  set IN := ∫⁻ x, f x ∂μN with hIN
  set Ib := ∫⁻ x, f x ∂μb with hIbdef

  have hIb : Ib ≠ 0 := by
    intro h0
    have h1 := (lintegral_eq_zero_iff hfm).1 h0
    have h2 : ∀ᵐ x ∂μb, False := by
      filter_upwards [h1, P.LongWeylElement.haar_ae hb] with x hx hxU
      have := tr_f_pos (A := A) hxU.1
      simp only [Pi.zero_apply] at hx
      exact absurd hx (ne_of_gt this)
    have h3 : μb Set.univ = 0 := by
      have := ae_iff.1 h2
      simpa using this
    exact hb.ne_zero (Measure.measure_univ_eq_zero.1 h3)

  set S : Set (Fin r → ℂ) := {c | ∀ a, c a ≠ 0} with hSdef
  have hSo : IsOpen S := by
    have : S = ⋂ a : Fin r, (fun c : Fin r → ℂ => c a) ⁻¹' {0}ᶜ := by
      ext c; simp [hSdef]
    rw [this]
    exact isOpen_iInter_of_finite fun a => isOpen_compl_singleton.preimage (continuous_apply a)
  have hSm : MeasurableSet S := hSo.measurableSet

  have hinner : ∀ c ∈ S, ENNReal.ofReal (B.gN (bigCell k r c 1) ^ (-A)) * (IN * IN * Ib) ≤
      ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) := by
    intro c hc
    have hbG := tr_bigCell_one_mem (k := k) hc
    have hae1 : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.1.1 : B.Mat k r) ∈ Nset k r :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_fst.ae (P.LongWeylElement.haar_ae hN))
    have hae2 : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.1.2 : B.Mat k r) ∈ Nset k r :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae (P.LongWeylElement.haar_ae hN))
    have hae3 : ∀ᵐ p ∂((μN.prod μN).prod μb), (Matrix.of p.2 : B.Mat k r) ∈ B2.UWb k r :=
      Measure.quasiMeasurePreserving_snd.ae (P.LongWeylElement.haar_ae hb)
    set β : ENNReal := ENNReal.ofReal (B.gN (bigCell k r c 1) ^ (-A)) with hβ
    have hpt : ∀ᵐ p ∂((μN.prod μN).prod μb),
        β * ((f p.1.1 * f p.1.2) * f p.2) ≤
          f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) := by
      filter_upwards [hae1, hae2, hae3] with p h1 h2 h3
      set n : B.Mat k r := Matrix.of p.1.1
      set n' : B.Mat k r := Matrix.of p.1.2
      set m : B.Mat k r := Matrix.of p.2
      have hn : n ∈ B.GV k r := h1.1
      have hn' : n' ∈ B.GV k r := h2.1
      have hm : m ∈ B.GV k r := h3.1
      have hgG : n⁻¹ * bigCell k r c 1 * m * n' ∈ B.GV k r :=
        P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_mul (P.BetaSesquilinearity.gv_inv hn) hbG) hm) hn'
      have hgpos : 0 < B.gN (n⁻¹ * bigCell k r c 1 * m * n') :=
        lt_of_lt_of_le one_pos (P.BetaSesquilinearity.gN_ge_one hgG)
      have hle : B.gN (n⁻¹ * bigCell k r c 1 * m * n') ≤
          B.gN n * B.gN (bigCell k r c 1) * B.gN m * B.gN n' := by
        calc B.gN (n⁻¹ * bigCell k r c 1 * m * n') ≤ B.gN (n⁻¹ * bigCell k r c 1 * m) * B.gN n' := gN_mul_le _ _
          _ ≤ (B.gN (n⁻¹ * bigCell k r c 1) * B.gN m) * B.gN n' :=
              mul_le_mul_of_nonneg_right (gN_mul_le _ _) (tr_gN_nonneg _)
          _ ≤ ((B.gN n⁻¹ * B.gN (bigCell k r c 1)) * B.gN m) * B.gN n' :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (gN_mul_le _ _) (tr_gN_nonneg _))
                (tr_gN_nonneg _)
          _ = B.gN n * B.gN (bigCell k r c 1) * B.gN m * B.gN n' := by rw [gN_inv_GV hn]
      have hrp := Real.rpow_le_rpow_of_nonpos hgpos hle (by linarith : -A ≤ 0)
      have e1 : (B.gN n * B.gN (bigCell k r c 1) * B.gN m * B.gN n') ^ (-A) =
          B.gN n ^ (-A) * B.gN (bigCell k r c 1) ^ (-A) * B.gN m ^ (-A) * B.gN n' ^ (-A) := by
        rw [Real.mul_rpow (mul_nonneg (mul_nonneg (tr_gN_nonneg _) (tr_gN_nonneg _)) (tr_gN_nonneg _))
            (tr_gN_nonneg _),
          Real.mul_rpow (mul_nonneg (tr_gN_nonneg _) (tr_gN_nonneg _)) (tr_gN_nonneg _),
          Real.mul_rpow (tr_gN_nonneg _) (tr_gN_nonneg _)]
      rw [e1] at hrp
      have hnn : ∀ g : B.Mat k r, 0 ≤ B.gN g ^ (-A) := fun g => Real.rpow_nonneg (tr_gN_nonneg _) _
      calc β * ((f p.1.1 * f p.1.2) * f p.2)
          = ENNReal.ofReal (B.gN n ^ (-A) * B.gN (bigCell k r c 1) ^ (-A) * B.gN m ^ (-A) * B.gN n' ^ (-A)) := by
            rw [ENNReal.ofReal_mul (mul_nonneg (mul_nonneg (hnn _) (hnn _)) (hnn _)),
              ENNReal.ofReal_mul (mul_nonneg (hnn _) (hnn _)), ENNReal.ofReal_mul (hnn _)]
            simp only [hfdef, hβ]
            ring
        _ ≤ f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) :=
            ENNReal.ofReal_le_ofReal hrp
    refine le_trans (le_of_eq ?_) (lintegral_mono_ae hpt)
    have hm3 : Measurable (fun p : (Mt k r × Mt k r) × Mt k r => f p.1.1 * f p.1.2 * f p.2) :=
      ((hfm.comp (measurable_fst.comp measurable_fst)).mul (hfm.comp (measurable_snd.comp measurable_fst))).mul
        (hfm.comp measurable_snd)
    have hm2 : Measurable (fun q : Mt k r × Mt k r => f q.1 * f q.2) :=
      (hfm.comp measurable_fst).mul (hfm.comp measurable_snd)
    have e1 : ∫⁻ p : (Mt k r × Mt k r) × Mt k r, f p.1.1 * f p.1.2 * f p.2 ∂((μN.prod μN).prod μb) =
        (∫⁻ q : Mt k r × Mt k r, f q.1 * f q.2 ∂(μN.prod μN)) * Ib :=
      lintegral_prod_mul (f := fun q : Mt k r × Mt k r => f q.1 * f q.2) (g := f) hm2.aemeasurable hfm.aemeasurable
    have e2 : ∫⁻ q : Mt k r × Mt k r, f q.1 * f q.2 ∂(μN.prod μN) = IN * IN :=
      lintegral_prod_mul (f := f) (g := f) hfm.aemeasurable hfm.aemeasurable
    rw [lintegral_const_mul _ hm3, e1, e2]

  set F : (Fin r → ℂ) → ENNReal := fun c => ENNReal.ofReal (B2.cWeight k r c) *
    ENNReal.ofReal (B.gN (bigCell k r c 1) ^ (-A)) with hFdef
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp tr_cWeight_cont.measurable).mul (hfm.comp tr_meas_bigCell)
  set K := ∫⁻ c, S.indicator F c with hKdef
  have hK : K ≠ 0 := by
    intro h0
    have h1 := (lintegral_eq_zero_iff (hFm.indicator hSm)).1 h0
    have hpos : ∀ c ∈ S, S.indicator F c ≠ 0 := by
      intro c hc
      rw [Set.indicator_of_mem hc]
      refine ne_of_gt (ENNReal.mul_pos ?_ ?_)
      · refine ne_of_gt (ENNReal.ofReal_pos.2 ?_)
        unfold B2.cWeight
        exact Finset.prod_pos fun a _ => pow_pos (norm_pos_iff.2 (hc a)) _
      · exact ne_of_gt (tr_f_pos (tr_bigCell_one_mem hc))
    have h2 : (volume : Measure (Fin r → ℂ)) S = 0 := by
      refine measure_mono_null (fun c hc => ?_) (ae_iff.1 h1)
      exact hpos c hc
    have h3 := hSo.measure_pos (volume : Measure (Fin r → ℂ)) ⟨fun _ => 1, fun a => one_ne_zero⟩
    exact absurd h2 (ne_of_gt h3)
  have hlow : K * (IN * IN * Ib) ≤ ∫⁻ c, ENNReal.ofReal (B2.cWeight k r c) *
      ∫⁻ p : (Mt k r × Mt k r) × Mt k r,
        f ((Matrix.of p.1.1)⁻¹ * bigCell k r c 1 * Matrix.of p.2 * Matrix.of p.1.2) ∂((μN.prod μN).prod μb) := by
    rw [hKdef, ← lintegral_mul_const _ (hFm.indicator hSm)]
    refine lintegral_mono fun c => ?_
    by_cases hc : c ∈ S
    · rw [Set.indicator_of_mem hc, hFdef, mul_assoc]
      gcongr
      exact hinner c hc
    · rw [Set.indicator_of_notMem hc, zero_mul]
      exact zero_le
  have hfin2 : (C : ENNReal) * (K * (IN * IN * Ib)) < ⊤ := by
    refine lt_of_le_of_lt ?_ hfin
    gcongr
  by_contra htop
  have hIN : IN = ⊤ := not_lt_top_iff.1 htop
  have hCne : (C : ENNReal) ≠ 0 := by exact_mod_cast (ne_of_gt hC)
  rw [hIN, ENNReal.top_mul (by simp), ENNReal.top_mul hIb, ENNReal.mul_top hK, ENNReal.mul_top hCne] at hfin2
  exact lt_irrefl _ hfin2

theorem intN (k r : ℕ) (μN : Measure (Mt k r)) (hN : IsHaarOn (Nset k r) μN) (a : ℝ) (ha : B.AB k r ≤ a) :
    Integrable (fun x : Mt k r => B.gN (Matrix.of x : B.Mat k r) ^ (-a)) μN := by
  refine ⟨((P.HaarUniquenessConjugation.gN_meas k r).pow_const _).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => Real.rpow_nonneg (tr_gN_nonneg _) _)]
  refine lt_of_le_of_lt (lintegral_mono_ae ?_) (intN_AB hN)
  filter_upwards [P.LongWeylElement.haar_ae hN] with x hx
  have h1 : 1 ≤ B.gN (Matrix.of x : B.Mat k r) := P.BetaSesquilinearity.gN_ge_one hx.1
  exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le h1 (by linarith))

end Formalism.FourierDecayAlt.P.SliceLastLevel

end PartTr

section PartCd
open Matrix Filter Topology
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.SliceLastLevel

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section cdmap

variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}

def bmap (k r : ℕ) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0) (x : Fin d → ℝ) : B.Mat k r :=
  bigCell k r (cx x) (castW (μx x))

lemma cd_bmap_entry_c (hcx : ContDiffOn ℝ ∞ cx O) (a : Fin r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => cx x a) O :=
  contDiffOn_pi.1 hcx a

lemma cd_bmap_entry_ci (hcx : ContDiffOn ℝ ∞ cx O) (hx : ∀ x ∈ O, ∀ a, cx x a ≠ 0) (a : Fin r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (star (cx x a))⁻¹) O := by
  have h1 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => star (cx x a)) O := by
    have := (Complex.conjCLE.toContinuousLinearMap.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).comp_contDiffOn
      (cd_bmap_entry_c hcx a)
    refine this.congr fun x _ => ?_
    simp
  exact h1.inv fun x hxO => star_ne_zero.2 (hx x hxO a)

lemma bmap_cd (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O) (hx : ∀ x ∈ O, ∀ a, cx x a ≠ 0) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (bmap k r cx μx) O := by
  rw [Formalism.FourierDecayAlt.P.Ux10.cdm_iff]
  intro i j
  have hμe := Formalism.FourierDecayAlt.P.Ux10.cdm_iff.1 hμx
  unfold bmap bigCell
  by_cases hj : j.val < r
  · simp only [hj, dif_pos]
    by_cases hi : i = esI k r ⟨j.val, hj⟩
    · simp only [hi, if_true]
      exact cd_bmap_entry_c hcx _
    · simp only [hi, if_false]
      exact contDiffOn_const
  · simp only [hj, dif_neg, not_false_eq_true]
    by_cases hj2 : j.val ≤ r + k
    · simp only [hj2, dif_pos]
      by_cases hi : r ≤ i.val ∧ i.val ≤ r + k
      · simp only [hi, dif_pos, and_self]
        unfold castW
        simp only [Matrix.reindex_apply, Matrix.submatrix_apply]
        exact hμe _ _
      · simp only [hi, dif_neg, not_false_eq_true]
        exact contDiffOn_const
    · simp only [hj2, dif_neg, not_false_eq_true]
      by_cases hi : i.val = 2 * r + k - j.val
      · simp only [hi, if_true]
        exact cd_bmap_entry_ci hcx hx _
      · simp only [hi, if_false]
        exact contDiffOn_const

lemma bmap_mem (hx : ∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) :
    ∀ x ∈ O, bmap k r cx μx x ∈ B.GV k r := fun x hxO =>
  big_cell_mem_holds k r (cx x) (castW (μx x)) (hx x hxO).1 (tr_castW_mem (hx x hxO).2)

end cdmap

section cdmap2

variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}

lemma bmap_diff (hO : IsOpen O) (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O)
    (hx : ∀ x ∈ O, ∀ a, cx x a ≠ 0) {x : Fin d → ℝ} (hxO : x ∈ O) : DifferentiableAt ℝ (bmap k r cx μx) x :=
  ((bmap_cd hcx hμx hx).differentiableOn (by simp)).differentiableAt (hO.mem_nhds hxO)

lemma bmap_tangent (hO : IsOpen O) (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O)
    (hx : ∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) {x : Fin d → ℝ} (hxO : x ∈ O) (e : Fin d → ℝ) :
    B.inLie k r ((bmap k r cx μx x)⁻¹ * fderiv ℝ (bmap k r cx μx) x e) := by
  have hx1 : ∀ x ∈ O, ∀ a, cx x a ≠ 0 := fun x hxO => (hx x hxO).1
  set c := bmap k r cx μx x with hc
  set T := fderiv ℝ (bmap k r cx μx) x e with hT
  have hcG : c ∈ B.GV k r := bmap_mem hx x hxO
  have hcu : IsUnit c.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hcG
  set γ : ℝ → B.Mat k r := fun t => bmap k r cx μx (x + t • e) with hγ
  have hline : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    have h := ((hasDerivAt_id (0:ℝ)).smul_const e).const_add x
    rw [one_smul] at h
    exact h
  have hγd : HasDerivAt γ T 0 :=
    (bmap_diff hO hcx hμx hx1 hxO).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
  have hγ0 : γ 0 = c := by simp [hγ, hc]
  have h1 : HasDerivAt (fun t => Formalism.FourierDecayAlt.P.Ux10.cT k r (γ t)) (Formalism.FourierDecayAlt.P.Ux10.cT k r T) 0 :=
    (Formalism.FourierDecayAlt.P.Ux10.cT k r).hasFDerivAt.comp_hasDerivAt 0 hγd
  have h2 : HasDerivAt (fun t => Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r (γ t)) (Hpk k r))
      (Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r (γ 0)) 0 +
        Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r T) (Hpk k r)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h1) (fun _ => hasDerivAt_const _ _)
  have h3 : HasDerivAt (fun t => Formalism.FourierDecayAlt.P.Ux10.mulB k r
        (Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r (γ t)) (Hpk k r)) (γ t))
      (Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r (γ 0)) (Hpk k r)) T +
        Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r (γ 0)) 0 +
          Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r T) (Hpk k r)) (γ 0)) 0 :=
    ContinuousLinearMap.hasDerivAt_of_bilinear (fun _ => h2) (fun _ => hγd)
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), x + t • e ∈ O :=
    ((continuous_const.add (continuous_id.smul continuous_const)).continuousAt (x := (0:ℝ))).preimage_mem_nhds
      (hO.mem_nhds (by simpa using hxO))
  have h4 : HasDerivAt (fun t => Formalism.FourierDecayAlt.P.Ux10.mulB k r
      (Formalism.FourierDecayAlt.P.Ux10.mulB k r (Formalism.FourierDecayAlt.P.Ux10.cT k r (γ t)) (Hpk k r)) (γ t)) 0 0 := by
    refine (hasDerivAt_const (0:ℝ) (Hpk k r)).congr_of_eventuallyEq ?_
    filter_upwards [hev] with t ht
    have hm : γ t ∈ B.GV k r := bmap_mem hx _ ht
    exact hm
  have hz := h3.unique h4
  simp only [Formalism.FourierDecayAlt.P.Ux10.mulB_apply, Formalism.FourierDecayAlt.P.Ux10.cT_apply, hγ0, Matrix.mul_zero, zero_add] at hz

  have hH : cᴴ * Hpk k r * c = Hpk k r := hcG
  have hci : c * c⁻¹ = 1 := Matrix.mul_nonsing_inv _ hcu
  have hci' : (c⁻¹)ᴴ * cᴴ = 1 := by rw [← conjTranspose_mul, hci, conjTranspose_one]
  have e1 : (c⁻¹)ᴴ * Hpk k r = Hpk k r * c := by
    calc (c⁻¹)ᴴ * Hpk k r = (c⁻¹)ᴴ * (cᴴ * Hpk k r * c) := by rw [hH]
      _ = ((c⁻¹)ᴴ * cᴴ) * Hpk k r * c := by simp only [Matrix.mul_assoc]
      _ = Hpk k r * c := by rw [hci', Matrix.one_mul]
  have e2 : Hpk k r * c⁻¹ = cᴴ * Hpk k r := by
    calc Hpk k r * c⁻¹ = (cᴴ * Hpk k r * c) * c⁻¹ := by rw [hH]
      _ = cᴴ * Hpk k r * (c * c⁻¹) := by simp only [Matrix.mul_assoc]
      _ = cᴴ * Hpk k r := by rw [hci, Matrix.mul_one]
  show (c⁻¹ * T)ᴴ * Hpk k r + Hpk k r * (c⁻¹ * T) = 0
  rw [conjTranspose_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc (Hpk k r), e2]
  rw [← hz]
  simp only [Matrix.mul_assoc]
  abel

def ebd (b : Fin d) : Fin d → ℝ := fun j => if b = j then 1 else 0

def aB (k r : ℕ) (cx : (Fin d → ℝ) → Fin r → ℂ) (μx : (Fin d → ℝ) → B.Mat k 0) (i : Formalism.FourierDecayAlt.P.Ux10.J k r)
    (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  ∑ b, Formalism.FourierDecayAlt.P.Ux10.kc i ((bmap k r cx μx x)⁻¹ * fderiv ℝ (bmap k r cx μx) x (ebd b)) •
    ContinuousLinearMap.proj b

lemma aB_apply (i : Formalism.FourierDecayAlt.P.Ux10.J k r) (x e : Fin d → ℝ) :
    aB k r cx μx i x e = Formalism.FourierDecayAlt.P.Ux10.kc i ((bmap k r cx μx x)⁻¹ * fderiv ℝ (bmap k r cx μx) x e) := by
  have he : e = ∑ b, e b • ebd b := pi_eq_sum_univ e
  have e1 : (bmap k r cx μx x)⁻¹ * fderiv ℝ (bmap k r cx μx) x e =
      ∑ b, e b • ((bmap k r cx μx x)⁻¹ * fderiv ℝ (bmap k r cx μx) x (ebd b)) := by
    conv_lhs => rw [he]
    rw [map_sum, Matrix.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, Matrix.mul_smul]
  rw [e1, Formalism.FourierDecayAlt.P.Ux10.kc_sum]
  simp only [aB, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

lemma aB_cd (hO : IsOpen O) (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O)
    (hx : ∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) (i : Formalism.FourierDecayAlt.P.Ux10.J k r) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (aB k r cx μx i) O := by
  have hx1 : ∀ x ∈ O, ∀ a, cx x a ≠ 0 := fun x hxO => (hx x hxO).1
  have hb := bmap_cd (k := k) hcx hμx hx1
  have h1 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => fderiv ℝ (bmap k r cx μx) x (ebd b)) O :=
    fun b => (hb.fderiv_of_isOpen hO (by simp)).clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => (bmap k r cx μx x)⁻¹) O :=
    Formalism.FourierDecayAlt.P.Ux10.cdm_inv hb fun x hxO => Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh (bmap_mem hx x hxO)
  have h3 : ∀ b, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x => Formalism.FourierDecayAlt.P.Ux10.kc i ((bmap k r cx μx x)⁻¹ * fderiv ℝ (bmap k r cx μx) x (ebd b))) O := by
    intro b
    unfold Formalism.FourierDecayAlt.P.Ux10.kc
    exact (Formalism.FourierDecayAlt.P.Ux10.cd_co (Formalism.FourierDecayAlt.P.Ux10.cdm_mul h2 (h1 b)) i).mul contDiffOn_const
  unfold aB
  exact ContDiffOn.sum fun b _ => (h3 b).smul contDiffOn_const

end cdmap2

section cdmap3

variable {k r d : ℕ} {O : Set (Fin d → ℝ)} {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasFDeriv_slice (hO : IsOpen O) (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O)
    (hx : ∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) {H : B.Mat k r → E}
    (hH : B.CkOn ((1 : ℕ) : ℕ∞) (B.GV k r) H) {n n' : B.Mat k r} (hn : n ∈ B.GV k r) (hn' : n' ∈ B.GV k r)
    {x : Fin d → ℝ} (hxO : x ∈ O) :
    HasFDerivAt (fun y => H (n⁻¹ * bmap k r cx μx y * n'))
      (∑ i, (aB k r cx μx i x).smulRight
        (Formalism.FourierDecayAlt.P.B4.op false (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i * n') H (n⁻¹ * bmap k r cx μx x * n'))) x := by
  have hx1 : ∀ x ∈ O, ∀ a, cx x a ≠ 0 := fun x hxO => (hx x hxO).1
  set b := bmap k r cx μx x with hbdef
  have hbG : b ∈ B.GV k r := bmap_mem hx x hxO
  have hbu : IsUnit b.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hbG
  have hnu : IsUnit n'.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hn'
  set c := n⁻¹ * b * n' with hc
  have hcG : c ∈ B.GV k r := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hn) hbG) hn'
  have hγG : ∀ y ∈ O, n⁻¹ * bmap k r cx μx y * n' ∈ B.GV k r := fun y hy =>
    Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hn) (bmap_mem hx y hy)) hn'
  obtain ⟨U, h', hU, hcU, hcd, hff⟩ := hH c hcG
  have hdiff : DifferentiableAt ℝ h' c :=
    (hcd.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hcU)

  set Mc : B.Mat k r →L[ℝ] B.Mat k r :=
    (Formalism.FourierDecayAlt.P.B4.mulL (n⁻¹)).comp (Formalism.FourierDecayAlt.P.B4.mulR n') with hMc
  have hMc_apply : ∀ M, Mc M = n⁻¹ * M * n' := by
    intro M
    rw [Matrix.mul_assoc]
    rfl
  have hbd := (bmap_diff hO hcx hμx hx1 hxO).hasFDerivAt
  have hγd : HasFDerivAt (fun y => n⁻¹ * bmap k r cx μx y * n') (Mc.comp (fderiv ℝ (bmap k r cx μx) x)) x := by
    have := Mc.hasFDerivAt.comp x hbd
    refine this.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
    simp [hMc_apply]
  have hcomp : HasFDerivAt (fun y => h' (n⁻¹ * bmap k r cx μx y * n'))
      ((fderiv ℝ h' c).comp (Mc.comp (fderiv ℝ (bmap k r cx μx) x))) x :=
    hdiff.hasFDerivAt.comp x hγd
  have heq : (fun y => H (n⁻¹ * bmap k r cx μx y * n')) =ᶠ[𝓝 x] (fun y => h' (n⁻¹ * bmap k r cx μx y * n')) := by
    filter_upwards [hγd.continuousAt.preimage_mem_nhds (hU.mem_nhds hcU), hO.mem_nhds hxO] with y h1 h2
    exact hff _ h1 (hγG y h2)
  refine (hcomp.congr_of_eventuallyEq heq).congr_fderiv ?_
  ext1 e
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, _root_.sum_apply]
  simp only [ContinuousLinearMap.smulRight_apply]
  have hop : ∀ i, Formalism.FourierDecayAlt.P.B4.op false (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i * n') H c =
      fderiv ℝ h' c (c * (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i * n')) := fun i =>
    Formalism.FourierDecayAlt.P.B4.op_eq_op' 0 false hU (by simpa using hcd) hff
      (Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_conj (Formalism.FourierDecayAlt.P.Ux10.Lt_unit i).1 hn') c hcU hcG
  simp_rw [hop, ← map_smul, ← map_sum]
  congr 1
  set T := fderiv ℝ (bmap k r cx μx) x e with hT
  set Xv := b⁻¹ * T with hXv
  have hXl : B.inLie k r Xv := bmap_tangent hO hcx hμx hx hxO e
  have hA : ∀ i, aB k r cx μx i x e = Formalism.FourierDecayAlt.P.Ux10.kc i Xv := fun i => aB_apply i x e
  have hbX : b * Xv = T := by rw [hXv, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hbu, Matrix.one_mul]
  have hnn : n' * n'⁻¹ = 1 := Matrix.mul_nonsing_inv _ hnu
  rw [hMc_apply]
  calc n⁻¹ * T * n' = n⁻¹ * (b * Xv) * n' := by rw [hbX]
    _ = n⁻¹ * (b * (∑ i, Formalism.FourierDecayAlt.P.Ux10.kc i Xv • Formalism.FourierDecayAlt.P.Ux10.Lt i)) * n' := by
        rw [← Formalism.FourierDecayAlt.P.Ux10.expandL hXl]
    _ = ∑ i, aB k r cx μx i x e • (c * (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i * n')) := by
        simp only [hA, hc, Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        simp only [Matrix.mul_assoc]
        rw [← Matrix.mul_assoc n' n'⁻¹, hnn, Matrix.one_mul]

end cdmap3

end Formalism.FourierDecayAlt.P.SliceLastLevel

end PartCd

section PartM

open Matrix MeasureTheory Filter Topology

namespace Formalism.FourierDecayAlt.P.SliceLastLevel

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def Ap (r : ℕ) (A : ℝ) (m : ℕ) : ℝ := (A - 6 * (r : ℝ) * (m : ℝ)) / (9 * ((r : ℝ) + 1))

lemma thr_facts {k r : ℕ} {A : ℝ} {m : ℕ} (h : TransportedAlt k r A m) :
    0 < Ap r A m ∧ B.AB k r ≤ Ap r A m ∧ 0 < A - 6 * (r : ℝ) * m ∧
    (5 * (r : ℝ) + 1) * Ap r A m ≤ A - 6 * (r : ℝ) * m := by
  unfold TransportedAlt at h
  have hr : (0 : ℝ) < 9 * ((r : ℝ) + 1) := by positivity
  have hn : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by positivity
  have hAp : ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 < Ap r A m := h
  have hAB : B.AB k r ≤ ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 := by
    unfold B.AB; push_cast
    nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hpos : 0 < Ap r A m := lt_of_le_of_lt hn hAp
  have heq : A - 6 * (r : ℝ) * m = 9 * ((r : ℝ) + 1) * Ap r A m := by
    unfold Ap; field_simp
  refine ⟨hpos, hAB.trans hAp.le, by rw [heq]; positivity, ?_⟩
  rw [heq]; nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]

lemma nset_gv {k r : ℕ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ B.GV k r := hn.1

lemma pow_trade {G P C a b e : ℝ} (hG : 1 ≤ G) (hP : 0 < P) (hC : 1 ≤ C) (ha : 0 ≤ a) (_he : 0 ≤ e)
    (hPb : P ≤ C ^ (3 : ℝ) * G ^ e) (hab : e * a ≤ b) :
    G ^ (-b) ≤ C ^ (3 * a) * P ^ (-a) := by
  have hG0 : 0 < G := lt_of_lt_of_le one_pos hG
  have hC0 : 0 < C := lt_of_lt_of_le one_pos hC
  have h1 : G ^ (-b) ≤ G ^ (-(e * a)) := Real.rpow_le_rpow_of_exponent_le hG (by linarith)
  have h2 : P ^ a ≤ (C ^ (3 : ℝ) * G ^ e) ^ a := Real.rpow_le_rpow hP.le hPb ha
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hC0.le, ← Real.rpow_mul hG0.le] at h2
  have h3 : G ^ (-(e * a)) = (G ^ (e * a))⁻¹ := Real.rpow_neg hG0.le _
  rw [Real.rpow_neg hP.le]
  rw [h3] at h1
  refine h1.trans ?_
  have hPa : 0 < P ^ a := Real.rpow_pos_of_pos hP a
  have hGa : 0 < G ^ (e * a) := Real.rpow_pos_of_pos hG0 _
  rw [inv_le_iff_one_le_mul₀ hGa]
  have h4 : 1 ≤ (C ^ (3 * a) * G ^ (e * a)) / P ^ a := by rw [one_le_div hPa]; exact h2
  calc (1 : ℝ) ≤ (C ^ (3 * a) * G ^ (e * a)) / P ^ a := h4
    _ = C ^ (3 * a) * (P ^ a)⁻¹ * G ^ (e * a) := by ring

section bound

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma allLie_lr' {u v : List (B.Mat k r)} (hu : ∀ X ∈ u, B.inLie k r X) (hv : ∀ X ∈ v, B.inLie k r X) :
    Formalism.FourierDecayAlt.P.B4.AllLie (Formalism.FourierDecayAlt.P.B4.lr u v) := by
  intro x hx
  simp only [Formalism.FourierDecayAlt.P.B4.lr, List.mem_append, List.mem_map] at hx
  rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
  · exact hu X hX
  · exact hv X hX

theorem word_bound {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → E} {cF : ℝ} (hF : B.CCle A m F cF)
    {C κ : ℝ} (hC : 1 ≤ C) (hκ : 1 ≤ κ) {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) {n n' : B.Mat k r}
    (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r) {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0)
    (hs1 : B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r))
    (hs2 : B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r))
    (hs3 : B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    (u v : List (B.Mat k r)) (hu : ∀ X ∈ u, B.inLie k r X ∧ ‖X‖ ≤ κ * B.gN n ^ 2)
    (hv : ∀ X ∈ v, B.inLie k r X ∧ ‖X‖ ≤ κ * B.gN n' ^ 2) (hl : u.length + v.length ≤ m) :
    ‖B.dLR u v F (phi k r c n n' μ)‖ ≤
      max cF 0 * (κ * C ^ 2) ^ m *
        (C ^ (3 * Ap r A m) * ((B.gN n * B.gN n') * B.gN μ) ^ (-Ap r A m)) := by
  obtain ⟨hAp, -, hA6, hle⟩ := thr_facts hT
  set g := phi k r c n n' μ with hgdef
  have hg : g ∈ B.GV k r := phi_mem hc (nset_gv hn) (nset_gv hn') hμ
  set G := B.gN g with hGdef
  have hG : 1 ≤ G := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have hG0 : 0 < G := lt_of_lt_of_le one_pos hG
  have hn1 : 1 ≤ B.gN n := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn)
  have hn1' : 1 ≤ B.gN n' := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn')
  have hμ1 : 1 ≤ B.gN μ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ
  have hb := Formalism.FourierDecayAlt.P.B4.bound_scaled hF (Formalism.FourierDecayAlt.P.B4.lr u v) (Formalism.FourierDecayAlt.P.B4.lrt_lr u v)
    (allLie_lr' (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1))
    (by rw [Formalism.FourierDecayAlt.P.B4.length_lr]; exact hl) g hg
  rw [← Formalism.FourierDecayAlt.P.B4.dLR_eq] at hb
  set K : ℝ := κ * C ^ 2 * G ^ (4 * r) with hK
  have hK1 : 1 ≤ K := by
    have : 1 ≤ C ^ 2 := one_le_pow₀ hC
    have : 1 ≤ G ^ (4 * r) := one_le_pow₀ hG
    calc (1 : ℝ) = 1 * 1 * 1 := by ring
      _ ≤ κ * C ^ 2 * G ^ (4 * r) := by gcongr
  have hsq : ∀ x : ℝ, 0 ≤ x → x ≤ C * G ^ (2 * r) → κ * x ^ 2 ≤ K := by
    intro x hx0 hx
    have : x ^ 2 ≤ (C * G ^ (2 * r)) ^ 2 := pow_le_pow_left₀ hx0 hx 2
    calc κ * x ^ 2 ≤ κ * (C * G ^ (2 * r)) ^ 2 := by gcongr
      _ = K := by rw [hK]; ring
  have hpn : Formalism.FourierDecayAlt.P.B4.pn (Formalism.FourierDecayAlt.P.B4.lr u v) ≤ K ^ m := by
    refine (Formalism.FourierDecayAlt.P.B4.pn_le_pow _ K ?_).trans ?_
    · intro x hx
      simp only [Formalism.FourierDecayAlt.P.B4.lr, List.mem_append, List.mem_map] at hx
      rcases hx with ⟨X, hX, rfl⟩ | ⟨X, hX, rfl⟩
      · exact (hu X hX).2.trans (hsq _ (by positivity) hs1)
      · exact (hv X hX).2.trans (hsq _ (by positivity) hs2)
    · rw [Formalism.FourierDecayAlt.P.B4.length_lr]; exact pow_le_pow_right₀ hK1 hl
  have hcF : 0 ≤ max cF 0 := le_max_right _ _
  have h1 : G ^ A * ‖B.dLR u v F g‖ ≤ K ^ m * max cF 0 := by
    refine hb.trans ?_
    calc Formalism.FourierDecayAlt.P.B4.pn (Formalism.FourierDecayAlt.P.B4.lr u v) * cF ≤ Formalism.FourierDecayAlt.P.B4.pn (Formalism.FourierDecayAlt.P.B4.lr u v) * max cF 0 := by
          gcongr
          · exact Formalism.FourierDecayAlt.P.B4.pn_nonneg _
          · exact le_max_left _ _
      _ ≤ K ^ m * max cF 0 := by gcongr
  have hGA : 0 < G ^ A := Real.rpow_pos_of_pos hG0 A
  have h2 : ‖B.dLR u v F g‖ ≤ K ^ m * max cF 0 * G ^ (-A) := by
    rw [Real.rpow_neg hG0.le, ← div_eq_mul_inv, le_div_iff₀ hGA, mul_comm]
    exact h1

  have h3 : K ^ m * G ^ (-A) = (κ * C ^ 2) ^ m * G ^ (-(A - 4 * (r : ℝ) * m)) := by
    rw [hK, mul_pow, ← pow_mul, mul_assoc]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_add hG0]
    congr 1
    push_cast; ring

  have hP0 : 0 < (B.gN n * B.gN n') * B.gN μ := by positivity
  have hPb : (B.gN n * B.gN n') * B.gN μ ≤ C ^ (3 : ℝ) * G ^ (5 * (r : ℝ) + 1) := by
    have e1 : C ^ (3 : ℝ) * G ^ (5 * (r : ℝ) + 1) = (C * G ^ (2 * r)) * (C * G ^ (2 * r)) * (C * G ^ (r + 1)) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        show (5 * (r : ℝ) + 1) = ((5 * r + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [show 5 * r + 1 = 2 * r + 2 * r + (r + 1) by ring, pow_add, pow_add]; ring
    rw [e1]
    gcongr
  have h4 := pow_trade (b := A - 4 * (r : ℝ) * m) hG hP0 hC hAp.le (by positivity) hPb (by
    have : (0 : ℝ) ≤ 2 * (r : ℝ) * m := by positivity
    linarith)
  calc ‖B.dLR u v F g‖ ≤ K ^ m * max cF 0 * G ^ (-A) := h2
    _ = max cF 0 * (K ^ m * G ^ (-A)) := by ring
    _ = max cF 0 * ((κ * C ^ 2) ^ m * G ^ (-(A - 4 * (r : ℝ) * m))) := by rw [h3]
    _ ≤ max cF 0 * ((κ * C ^ 2) ^ m * (C ^ (3 * Ap r A m) * ((B.gN n * B.gN n') * B.gN μ) ^ (-Ap r A m))) := by
        gcongr
    _ = _ := by ring

end bound

section meas

variable {k r : ℕ}

def Sn (k r : ℕ) : Set (Mt k r × Mt k r) :=
  {ξ | (Matrix.of ξ.1 : B.Mat k r) ∈ Nset k r ∧ (Matrix.of ξ.2 : B.Mat k r) ∈ Nset k r}

lemma Sn_closed : IsClosed (Sn k r) := by
  have c2 : IsClosed {x : Mt k r | (Matrix.of x : B.Mat k r) ∈ Nset k r} := Formalism.FourierDecayAlt.P.B6.isClosed_Nset k r
  exact (c2.preimage continuous_fst).inter (c2.preimage continuous_snd)

lemma ae_Sn {μN : Measure (Mt k r)} (hN : IsHaarOn (Nset k r) μN) : ∀ᵐ ξ ∂(μN.prod μN), ξ ∈ Sn k r := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN
  exact (Measure.quasiMeasurePreserving_fst.ae (Formalism.FourierDecayAlt.P.B5.haar_ae hN)).and
    (Measure.quasiMeasurePreserving_snd.ae (Formalism.FourierDecayAlt.P.B5.haar_ae hN))

lemma phi_contOn (c : Fin r → ℂ) (μ : B.Mat k 0) :
    ContinuousOn (fun ξ : Mt k r × Mt k r => phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) μ) (Sn k r) :=
  Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul (Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul
    ((Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp continuous_fst.continuousOn
      (fun ξ h => Formalism.FourierDecayAlt.P.B6.Nset_sub _ _ h.1)) continuousOn_const) continuous_snd.continuousOn

def psiN {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (ξ : Mt k r × Mt k r) : ℂ :=
  psi k r D.z cStd (Matrix.of ξ.1) * star (psi k r D.z' cStd (Matrix.of ξ.2))

lemma norm_psiN {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (ξ : Mt k r × Mt k r) : ‖psiN D ξ‖ ≤ 1 := by
  unfold psiN
  rw [norm_mul, norm_star, Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.norm_psi, Formalism.FourierDecayAlt.P.SmoothnessOnGoodSet.norm_psi, one_mul]

lemma continuous_psiN {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (D : B.RealPlaceData k r Wp Wq) : Continuous (psiN D) := by
  have hp : ∀ (z : Fin (2 * r + k + 1) → ℂ) (f : Mt k r × Mt k r → Mt k r), Continuous f →
      Continuous fun p => psi k r z cStd (Matrix.of (f p)) := by
    intro z f hf
    have hl := Formalism.FourierDecayAlt.P.B7.continuous_ell (k := k) (r := r) z
    unfold psi
    exact Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (continuous_const.mul (hl.comp hf)))))
  unfold psiN
  exact (hp D.z _ continuous_fst).mul (continuous_star.comp (hp D.z' _ continuous_snd))

end meas

section clause2

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def hS (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) (ξ : Mt k r × Mt k r) (μ : B.Mat k 0) : Wq →L[ℂ] Wp :=
  Set.indicator (Sn k r) (fun ξ => F (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) μ)) ξ

lemma hS_mem {F : B.Mat k r → (Wq →L[ℂ] Wp)} {c : Fin r → ℂ} {ξ : Mt k r × Mt k r} (hξ : ξ ∈ Sn k r) :
    hS F c ξ = fun μ => F (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) μ) := by
  funext μ; unfold hS; rw [Set.indicator_of_mem hξ]

lemma hS_not {F : B.Mat k r → (Wq →L[ℂ] Wp)} {c : Fin r → ℂ} {ξ : Mt k r × Mt k r} (hξ : ξ ∉ Sn k r) :
    hS F c ξ = 0 := by
  funext μ; unfold hS; simp [Set.indicator, hξ]

lemma sliceR_eq (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (c : Fin r → ℂ) :
    sliceR D F c = fun μ => ∫ ξ, psiN D ξ • hS F c ξ μ ∂(D.μN.prod D.μN) := by
  funext μ
  unfold sliceR
  refine integral_congr_ae ?_
  filter_upwards [ae_Sn D.haarN] with ξ hξ
  rw [hS_mem hξ]
  rfl

lemma levelEmbed_entry_bound {Y : B.Mat k 0} (hY : B.unitLie k 0 Y) : Formalism.FourierDecayAlt.P.Ux5.EB (emb0 k r Y) 1 := by
  intro i j
  unfold emb0
  split_ifs
  · exact hY.2 _ _
  · simp

lemma letter_bound {n : B.Mat k r} (hn : n ∈ Nset k r) {Y : B.Mat k 0} (hY : B.unitLie k 0 Y) :
    B.inLie k r (n⁻¹ * emb0 k r Y * n) ∧
      ‖n⁻¹ * emb0 k r Y * n‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n ^ 2 := by
  refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_conj (block_embedding_skew_hermitian hY.1) (nset_gv hn), ?_⟩
  have h1 := norm_le_gN (n⁻¹ * emb0 k r Y * n)
  have h2 := gN_mul_le (n⁻¹ * emb0 k r Y) n
  have h3 := gN_mul_le n⁻¹ (emb0 k r Y)
  have h4 : B.gN (emb0 k r Y) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * 1 :=
    Formalism.FourierDecayAlt.P.Ux5.gN_le_of_EB (emb0 k r Y) (levelEmbed_entry_bound hY) zero_le_one
  rw [gN_inv_GV (nset_gv hn)] at h3
  have hn0 : 0 ≤ B.gN n := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn))
  calc ‖n⁻¹ * emb0 k r Y * n‖ ≤ B.gN (n⁻¹ * emb0 k r Y) * B.gN n := h1.trans h2
    _ ≤ (B.gN n * B.gN (emb0 k r Y)) * B.gN n := by gcongr
    _ ≤ (B.gN n * (((2 * r + k + 1 : ℕ) : ℝ) * 1)) * B.gN n := by gcongr
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n ^ 2 := by ring

theorem integrand_bound {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cF : ℝ}
    (hF : B.CCle A m F cF) {K : Set (Fin r → ℂ)} {C : ℝ} (hC : 1 ≤ C)
    (hs : ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    {c : Fin r → ℂ} (hcK : c ∈ K) (hc : ∀ a, c a ≠ 0)
    (u v : List (B.Mat k 0)) (hu : ∀ X ∈ u, B.unitLie k 0 X) (hv : ∀ X ∈ v, B.unitLie k 0 X)
    (hl : u.length + v.length ≤ m) (μ : B.Mat k 0) (hμ : μ ∈ B.GV k 0) (ξ : Mt k r × Mt k r) :
    ‖B.dLR u v (hS F c ξ) μ‖ ≤
      (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) *
        (B.gN (Matrix.of ξ.1 : B.Mat k r) ^ (-Ap r A m) * B.gN (Matrix.of ξ.2 : B.Mat k r) ^ (-Ap r A m)) *
        B.gN μ ^ (-Ap r A m) := by
  obtain ⟨hAp, -, -, -⟩ := thr_facts hT
  have hκ : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + k + 1 := by omega
    exact_mod_cast this
  by_cases hξ : ξ ∈ Sn k r
  · rw [hS_mem hξ]
    set n : B.Mat k r := Matrix.of ξ.1
    set n' : B.Mat k r := Matrix.of ξ.2
    have hn : n ∈ Nset k r := hξ.1
    have hn' : n' ∈ Nset k r := hξ.2
    rw [dLR_phi c (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (nset_gv hn)) (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_unit (nset_gv hn')) F u v]
    obtain ⟨h1, h2, h3⟩ := hs c hcK n hn n' hn' μ hμ
    have hw := word_bound hT hF hC hκ hc hn hn' hμ h1 h2 h3
      (u.map fun Y => n⁻¹ * emb0 k r Y * n) (v.map fun Y => n'⁻¹ * emb0 k r Y * n')
      (by
        intro X hX
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact letter_bound hn (hu Y hY))
      (by
        intro X hX
        obtain ⟨Y, hY, rfl⟩ := List.mem_map.1 hX
        exact letter_bound hn' (hv Y hY))
      (by simpa using hl)
    refine hw.trans (le_of_eq ?_)
    have hn0 : 0 ≤ B.gN n := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn))
    have hn0' : 0 ≤ B.gN n' := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn'))
    have hμ0 : 0 ≤ B.gN μ := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ)
    rw [Real.mul_rpow (mul_nonneg hn0 hn0') hμ0, Real.mul_rpow hn0 hn0']
    ring
  · rw [hS_not hξ, Formalism.FourierDecayAlt.P.BetaSesquilinearity.dLR_zero]
    simp only [Pi.zero_apply, norm_zero]
    have hC0 : 0 ≤ C := le_trans zero_le_one hC
    have h0 : 0 ≤ max cF 0 := le_max_right _ _
    have hg : ∀ M : B.Mat k r, 0 ≤ B.gN M ^ (-Ap r A m) := fun M => Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hg0 : 0 ≤ B.gN μ ^ (-Ap r A m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
    have hC3 : 0 ≤ C ^ (3 * Ap r A m) := Real.rpow_nonneg hC0 _
    have hk : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg h0 (pow_nonneg hk m)) hC3)
      (mul_nonneg (hg _) (hg _))) hg0

end clause2

section clause12

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma sizes1 (k r : ℕ) (K : Set (Fin r → ℂ)) (hK : IsCompact K) (hK0 : ∀ c ∈ K, ∀ a, c a ≠ 0) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1) := by
  obtain ⟨C0, -, hsz⟩ := sizes k r K hK hK0
  refine ⟨max C0 1, le_max_right _ _, ?_⟩
  intro c hc n hn n' hn' μ hμ
  obtain ⟨h1, h2, h3⟩ := hsz c hc n hn n' hn' μ hμ
  have hg : 0 ≤ B.gN (phi k r c n n' μ) := Real.sqrt_nonneg _
  have hCC : C0 ≤ max C0 1 := le_max_left _ _
  exact ⟨h1.trans (by gcongr), h2.trans (by gcongr), h3.trans (by gcongr)⟩

def beta0 (M a : ℝ) (ξ : Mt k r × Mt k r) : ℝ :=
  M * (B.gN (Matrix.of ξ.1 : B.Mat k r) ^ (-a) * B.gN (Matrix.of ξ.2 : B.Mat k r) ^ (-a))

lemma slice_weight_nonneg {M a : ℝ} (hM : 0 ≤ M) (ξ : Mt k r × Mt k r) : 0 ≤ beta0 (k := k) (r := r) M a ξ :=
  mul_nonneg hM (mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _) (Real.rpow_nonneg (Real.sqrt_nonneg _) _))

lemma integrable_slice_weight {μN : Measure (Mt k r)} (hN : IsHaarOn (Nset k r) μN) (M : ℝ) {a : ℝ} (ha : B.AB k r ≤ a) :
    Integrable (beta0 (k := k) (r := r) M a) (μN.prod μN) := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite hN
  exact (MeasureTheory.Integrable.mul_prod (intN k r μN hN a ha) (intN k r μN hN a ha)).const_mul M

lemma hS_meas {F : B.Mat k r → (Wq →L[ℂ] Wp)} {m : ℕ∞} (hF : B.CkOn m (B.GV k r) F) {c : Fin r → ℂ}
    (hc : ∀ a, c a ≠ 0) (μN : Measure (Mt k r × Mt k r)) {g : B.Mat k 0} (hg : g ∈ B.GV k 0) :
    AEStronglyMeasurable (fun ξ => hS F c ξ g) μN := by
  have hcont : ContinuousOn (fun ξ : Mt k r × Mt k r => F (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) g)) (Sn k r) :=
    (Formalism.FourierDecayAlt.P.B6.continuousOn_of_contDiffOn_group hF).comp (phi_contOn c g)
      (fun ξ hξ => phi_mem hc (nset_gv hξ.1) (nset_gv hξ.2) hg)
  exact (aestronglyMeasurable_indicator_iff Sn_closed.measurableSet).2
    (hcont.aestronglyMeasurable Sn_closed.measurableSet)

lemma hS_ck {F : B.Mat k r → (Wq →L[ℂ] Wp)} {m : ℕ∞} (hF : B.CkOn m (B.GV k r) F) {c : Fin r → ℂ}
    (hc : ∀ a, c a ≠ 0) (ξ : Mt k r × Mt k r) : B.CkOn m (B.GV k 0) (hS F c ξ) := by
  by_cases hξ : ξ ∈ Sn k r
  · rw [hS_mem hξ]; exact ckOn_phi hc (nset_gv hξ.1) (nset_gv hξ.2) hF
  · rw [hS_not hξ]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero

theorem slice_integrable_finite_class [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {A : ℝ} {m : ℕ}
    {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : B.InCC A m F) {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    (∀ μ ∈ B.GV k 0, Integrable (fun nn : Mt k r × Mt k r =>
        F ((Matrix.of nn.1)⁻¹ * bigCell k r c (castW μ) * Matrix.of nn.2)) (D.μN.prod D.μN)) ∧
    B.InCC (k := k) (r := 0) (Ap r A m) m (sliceR D F c) := by
  obtain ⟨cF, hcF⟩ := hF
  obtain ⟨hAp, hAB, -, -⟩ := thr_facts hT
  obtain ⟨C, hC, hs⟩ := sizes1 k r {c} isCompact_singleton
    (by intro c' hc'; rw [Set.mem_singleton_iff.1 hc']; exact hc)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  set M := max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m) with hMdef
  have hM : 0 ≤ M := by
    have : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg this m))
      (Real.rpow_nonneg (le_trans zero_le_one hC) _)
  have hβ : Integrable (beta0 (k := k) (r := r) M (Ap r A m)) (D.μN.prod D.μN) := integrable_slice_weight D.haarN M hAB
  have hbd := integrand_bound hT hcF hC hs (Set.mem_singleton c) hc
  have hg1 : ∀ μ ∈ B.GV k 0, B.gN μ ^ (-Ap r A m) ≤ 1 := fun μ hμ =>
    Real.rpow_le_one_of_one_le_of_nonpos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ) (by linarith)
  have hbd' : ∀ u v : List (B.Mat k 0), (∀ X ∈ u, B.unitLie k 0 X) → (∀ X ∈ v, B.unitLie k 0 X) →
      u.length + v.length ≤ m → ∀ g ∈ B.GV k 0, ∀ ξ, ‖B.dLR u v (hS F c ξ) g‖ ≤ beta0 M (Ap r A m) ξ := by
    intro u v hu hv hl g hg ξ
    refine (hbd u v hu hv hl g hg ξ).trans ?_
    calc beta0 M (Ap r A m) ξ * B.gN g ^ (-Ap r A m) ≤ beta0 M (Ap r A m) ξ * 1 :=
          mul_le_mul_of_nonneg_left (hg1 g hg) (slice_weight_nonneg hM ξ)
      _ = beta0 M (Ap r A m) ξ := mul_one _
  have hψ := norm_psiN D
  have hψm := (continuous_psiN D).aestronglyMeasurable (μ := D.μN.prod D.μN)
  have hh := hS_ck hcF.1 hc
  have hm : ∀ g ∈ B.GV k 0, AEStronglyMeasurable (fun ξ => hS F c ξ g) (D.μN.prod D.μN) :=
    fun g hg => hS_meas hcF.1 hc _ hg
  refine ⟨?_, ?_⟩
  · intro μ hμ
    have hI : Integrable (fun ξ => hS F c ξ μ) (D.μN.prod D.μN) := by
      refine Integrable.mono' hβ (hm μ hμ) (Eventually.of_forall fun ξ => ?_)
      have := hbd' [] [] (by simp) (by simp) (by simp) μ hμ ξ
      simpa [B.dLR, B.Rw] using this
    refine hI.congr ?_
    filter_upwards [ae_Sn D.haarN] with ξ hξ
    rw [hS_mem hξ]
    rfl
  · have hck := Formalism.FourierDecayAlt.P.Ux10.int_ck (psiN D) hψ hψm (hS F c) m hh hm _ hβ hbd'
    have hex := Formalism.FourierDecayAlt.P.Ux10.exch_dLR (psiN D) hψ hψm (hS F c) m hh hm _ hβ hbd'
    refine ⟨∫ ξ, beta0 M (Ap r A m) ξ ∂(D.μN.prod D.μN), ?_, ?_⟩
    · rw [sliceR_eq]; exact hck
    · intro u v hu hv hl g hg
      rw [sliceR_eq, hex u v hu hv hl g hg]
      have hgp : 0 < B.gN g := lt_of_lt_of_le one_pos (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg)
      have hint : Integrable (fun ξ => beta0 M (Ap r A m) ξ * B.gN g ^ (-Ap r A m)) (D.μN.prod D.μN) :=
        hβ.mul_const _
      have hn : ‖∫ ξ, psiN D ξ • B.dLR u v (hS F c ξ) g ∂(D.μN.prod D.μN)‖ ≤
          ∫ ξ, beta0 M (Ap r A m) ξ * B.gN g ^ (-Ap r A m) ∂(D.μN.prod D.μN) :=
        norm_integral_le_of_norm_le hint (Eventually.of_forall fun ξ => by
          rw [norm_smul (psiN D ξ) (B.dLR u v (hS F c ξ) g)]
          exact (mul_le_of_le_one_left (norm_nonneg _) (hψ ξ)).trans (hbd u v hu hv hl g hg ξ))
      rw [integral_mul_const] at hn
      have hpow : B.gN g ^ (Ap r A m) * B.gN g ^ (-Ap r A m) = 1 := by
        rw [Real.rpow_neg hgp.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos hgp _).ne']
      calc B.gN g ^ (Ap r A m) * ‖∫ ξ, psiN D ξ • B.dLR u v (hS F c ξ) g ∂(D.μN.prod D.μN)‖
          ≤ B.gN g ^ (Ap r A m) * ((∫ ξ, beta0 M (Ap r A m) ξ ∂(D.μN.prod D.μN)) * B.gN g ^ (-Ap r A m)) :=
            mul_le_mul_of_nonneg_left hn (Real.rpow_nonneg hgp.le _)
        _ = ∫ ξ, beta0 M (Ap r A m) ξ ∂(D.μN.prod D.μN) := by
            rw [mul_comm, mul_assoc, mul_comm (B.gN g ^ (-Ap r A m)), hpow, mul_one]

end clause12

end Formalism.FourierDecayAlt.P.SliceLastLevel

end PartM

section PartE

open Matrix MeasureTheory Filter Topology
open scoped ContDiff

set_option linter.style.haveILetI false

namespace Formalism.FourierDecayAlt.P.SliceLastLevel

lemma mexp_cont (n : ℕ) : Continuous (fun X : Matrix (Fin n) (Fin n) ℂ => NormedSpace.exp X) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
  exact NormedSpace.exp_continuous

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.JF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section words

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def adR (n' : B.Mat k r) (i : Formalism.FourierDecayAlt.P.Ux10.J k r) : B.Mat k r := n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i * n'

def Gw (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ξ : Mt k r × Mt k r) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) :
    B.Mat k r → (Wq →L[ℂ] Wp) :=
  B.Rw (w.map (adR (Matrix.of ξ.2))) F

lemma adR_lie {n' : B.Mat k r} (hn' : n' ∈ B.GV k r) (i : Formalism.FourierDecayAlt.P.Ux10.J k r) : B.inLie k r (adR n' i) :=
  Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_conj (Formalism.FourierDecayAlt.P.Ux10.Lt_unit i).1 hn'

lemma adR_norm {n' : B.Mat k r} (hn' : n' ∈ B.GV k r) (i : Formalism.FourierDecayAlt.P.Ux10.J k r) :
    ‖adR n' i‖ ≤ ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n' ^ 2 := by
  have hEB : Formalism.FourierDecayAlt.P.Ux5.EB (Formalism.FourierDecayAlt.P.Ux10.Lt i) 1 := fun a b => (Formalism.FourierDecayAlt.P.Ux10.Lt_unit i).2 a b
  have h1 := norm_le_gN (adR n' i)
  have h2 := gN_mul_le (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i) n'
  have h3 := gN_mul_le n'⁻¹ (Formalism.FourierDecayAlt.P.Ux10.Lt i)
  have h4 : B.gN (Formalism.FourierDecayAlt.P.Ux10.Lt i) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * 1 :=
    Formalism.FourierDecayAlt.P.Ux5.gN_le_of_EB _ hEB zero_le_one
  rw [gN_inv_GV hn'] at h3
  have hn0 : 0 ≤ B.gN n' := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hn')
  calc ‖adR n' i‖ ≤ B.gN (n'⁻¹ * Formalism.FourierDecayAlt.P.Ux10.Lt i) * B.gN n' := h1.trans h2
    _ ≤ (B.gN n' * B.gN (Formalism.FourierDecayAlt.P.Ux10.Lt i)) * B.gN n' := by gcongr
    _ ≤ (B.gN n' * (((2 * r + k + 1 : ℕ) : ℝ) * 1)) * B.gN n' := by gcongr
    _ = ((2 * r + k + 1 : ℕ) : ℝ) * B.gN n' ^ 2 := by ring

lemma Gw_ck {m : ℕ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn (m : ℕ∞) (B.GV k r) F) {ξ : Mt k r × Mt k r}
    (hn' : (Matrix.of ξ.2 : B.Mat k r) ∈ B.GV k r) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) (hw : w.length ≤ m) :
    B.CkOn ((m - w.length : ℕ) : ℕ∞) (B.GV k r) (Gw F ξ w) := by
  have hL : Formalism.FourierDecayAlt.P.B4.AllLie (Formalism.FourierDecayAlt.P.B4.lr [] (w.map (adR (Matrix.of ξ.2)))) :=
    allLie_lr' (by simp) (by
      intro X hX
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX
      exact adR_lie hn' i)
  have h := Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives (Formalism.FourierDecayAlt.P.B4.lr [] (w.map (adR (Matrix.of ξ.2)))) hL (m - w.length)
    (by
      rw [Formalism.FourierDecayAlt.P.B4.length_lr]
      simp only [List.length_nil, List.length_map, zero_add]
      rw [Nat.sub_add_cancel hw]
      exact hF)
  rw [← Formalism.FourierDecayAlt.P.B4.dLR_eq] at h
  exact h

lemma Gw_meas {m : ℕ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hF : B.CkOn (m : ℕ∞) (B.GV k r) F)
    (μS : Measure (Mt k r × Mt k r)) :
    ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ∀ P : Mt k r × Mt k r → B.Mat k r,
      ContinuousOn P (Sn k r) → (∀ ξ ∈ Sn k r, P ξ ∈ B.GV k r) →
      AEStronglyMeasurable (fun ξ => Set.indicator (Sn k r) (fun ξ => Gw F ξ w (P ξ)) ξ) μS := by
  intro w
  induction w with
  | nil =>
    intro _ P hP hPG
    have hc : ContinuousOn (fun ξ => Gw F ξ [] (P ξ)) (Sn k r) :=
      (Formalism.FourierDecayAlt.P.B6.continuousOn_of_contDiffOn_group hF).comp hP hPG
    exact (aestronglyMeasurable_indicator_iff Sn_closed.measurableSet).2
      (hc.aestronglyMeasurable Sn_closed.measurableSet)
  | cons i w ih =>
    intro hl P hP hPG
    have hl' : w.length + 1 ≤ m := by simpa using hl
    set X : Mt k r × Mt k r → B.Mat k r := fun ξ => adR (Matrix.of ξ.2) i with hXdef
    have hX : ContinuousOn X (Sn k r) :=
      Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul (Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul
        ((Formalism.FourierDecayAlt.P.B6.inv_continuousOn k r).comp continuous_snd.continuousOn
          (fun ξ h => Formalism.FourierDecayAlt.P.B6.Nset_sub _ _ h.2)) continuousOn_const) continuous_snd.continuousOn
    have hd : ∀ ξ, HasDerivAt
        (fun t : ℝ => Set.indicator (Sn k r)
          (fun ξ => Gw F ξ w (P ξ * NormedSpace.exp ((t : ℂ) • X ξ))) ξ)
        (Set.indicator (Sn k r) (fun ξ => Gw F ξ (i :: w) (P ξ)) ξ) 0 := by
      intro ξ
      by_cases hξ : ξ ∈ Sn k r
      · simp only [Set.indicator_of_mem hξ]
        have hn' : (Matrix.of ξ.2 : B.Mat k r) ∈ B.GV k r := nset_gv hξ.2
        have hck : B.CkOn (((0 : ℕ) + 1 : ℕ) : ℕ∞) (B.GV k r) (Gw F ξ w) := by
          have := Gw_ck hF hn' w (by omega)
          exact Formalism.FourierDecayAlt.P.B4.ckOn_mono (by omega) this
        have hdiff := Formalism.FourierDecayAlt.P.B4.ckOn_diff 0 false hck (adR_lie hn' i) (hPG ξ hξ)
        exact hdiff.hasDerivAt
      · simp only [Set.indicator_of_notMem hξ]
        exact hasDerivAt_const _ _
    refine Formalism.FourierDecayAlt.P.Ux10.aesm_deriv hd (Eventually.of_forall fun t => ?_)
    refine ih (by omega) (fun ξ => P ξ * NormedSpace.exp ((t : ℂ) • X ξ)) ?_ ?_
    · exact Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul hP
        ((mexp_cont _).comp_continuousOn (hX.const_smul ((t : ℂ))))
    · intro ξ hξ
      exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (hPG ξ hξ)
        (Formalism.FourierDecayAlt.P.BetaSesquilinearity.exp_mem (Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_rsmul (adR_lie (nset_gv hξ.2) i) t))

end words

section clause3

variable {k r d : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma Gw_bound {A : ℝ} {m : ℕ} (hT : TransportedAlt k r A m) {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cF : ℝ}
    (hF : B.CCle A m F cF) {K : Set (Fin r → ℂ)} {C : ℝ} (hC : 1 ≤ C)
    (hs : ∀ c ∈ K, ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r, ∀ μ ∈ B.GV k 0,
      B.gN n ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN n' ≤ C * B.gN (phi k r c n n' μ) ^ (2 * r) ∧
      B.gN μ ≤ C * B.gN (phi k r c n n' μ) ^ (r + 1))
    {c : Fin r → ℂ} (hcK : c ∈ K) (hc : ∀ a, c a ≠ 0) {ξ : Mt k r × Mt k r} (hξ : ξ ∈ Sn k r)
    {μ : B.Mat k 0} (hμ : μ ∈ B.GV k 0) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) (hw : w.length ≤ m) :
    ‖Gw F ξ w (phi k r c (Matrix.of ξ.1) (Matrix.of ξ.2) μ)‖ ≤
      beta0 (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) (Ap r A m) ξ := by
  obtain ⟨hAp, -, -, -⟩ := thr_facts hT
  have hκ : (1 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) := by
    have : 1 ≤ 2 * r + k + 1 := by omega
    exact_mod_cast this
  set n : B.Mat k r := Matrix.of ξ.1
  set n' : B.Mat k r := Matrix.of ξ.2
  have hn : n ∈ Nset k r := hξ.1
  have hn' : n' ∈ Nset k r := hξ.2
  obtain ⟨h1, h2, h3⟩ := hs c hcK n hn n' hn' μ hμ
  have hw' := word_bound hT hF hC hκ hc hn hn' hμ h1 h2 h3 [] (w.map (adR n')) (by simp)
    (by
      intro X hX
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hX
      exact ⟨adR_lie (nset_gv hn') i, adR_norm (nset_gv hn') i⟩)
    (by simpa using hw)
  have hn0 : 0 ≤ B.gN n := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn))
  have hn0' : 0 ≤ B.gN n' := le_trans zero_le_one (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one (nset_gv hn'))
  have hμ1 : 1 ≤ B.gN μ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hμ
  have hμp : B.gN μ ^ (-Ap r A m) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hμ1 (by linarith)
  have hM : 0 ≤ max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m) := by
    have : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg this m))
      (Real.rpow_nonneg (le_trans zero_le_one hC) _)
  have hb0 : 0 ≤ B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m) :=
    mul_nonneg (Real.rpow_nonneg hn0 _) (Real.rpow_nonneg hn0' _)
  refine hw'.trans ?_
  rw [Real.mul_rpow (mul_nonneg hn0 hn0') (le_trans zero_le_one hμ1), Real.mul_rpow hn0 hn0']
  unfold beta0
  calc max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m *
        (C ^ (3 * Ap r A m) * (B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m) * B.gN μ ^ (-Ap r A m)))
      = (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) *
          (B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m)) * B.gN μ ^ (-Ap r A m) := by ring
    _ ≤ (max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m)) *
          (B.gN n ^ (-Ap r A m) * B.gN n' ^ (-Ap r A m)) * 1 := by gcongr
    _ = _ := by rw [mul_one]

def Fw (D : B.RealPlaceData k r Wp Wq) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (cx : (Fin d → ℝ) → Fin r → ℂ)
    (μx : (Fin d → ℝ) → B.Mat k 0) (w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)) (x : Fin d → ℝ)
    (ξ : Mt k r × Mt k r) : Wq →L[ℂ] Wp :=
  psiN D ξ • Set.indicator (Sn k r)
    (fun ξ => Gw F ξ w (phi k r (cx x) (Matrix.of ξ.1) (Matrix.of ξ.2) (μx x))) ξ

lemma Fw_mem {D : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cx : (Fin d → ℝ) → Fin r → ℂ}
    {μx : (Fin d → ℝ) → B.Mat k 0} {w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)} {ξ : Mt k r × Mt k r}
    (hξ : ξ ∈ Sn k r) :
    (fun x => Fw D F cx μx w x ξ) = fun x =>
      psiN D ξ • Gw F ξ w ((Matrix.of ξ.1 : B.Mat k r)⁻¹ * bmap k r cx μx x * Matrix.of ξ.2) := by
  funext x; unfold Fw; rw [Set.indicator_of_mem hξ]; rfl

lemma Fw_not {D : B.RealPlaceData k r Wp Wq} {F : B.Mat k r → (Wq →L[ℂ] Wp)} {cx : (Fin d → ℝ) → Fin r → ℂ}
    {μx : (Fin d → ℝ) → B.Mat k 0} {w : List (Formalism.FourierDecayAlt.P.Ux10.J k r)} {ξ : Mt k r × Mt k r}
    (hξ : ξ ∉ Sn k r) : (fun x => Fw D F cx μx w x ξ) = fun _ => 0 := by
  funext x; unfold Fw; rw [Set.indicator_of_notMem hξ, smul_zero]

end clause3

section clause3b

variable {k r d : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

lemma smul_sum_smulRight {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup V]
    [NormedSpace ℂ V] {ι : Type*} (s : Finset ι) (a : ι → X →L[ℝ] ℝ) (v : ι → V) (z : ℂ) :
    z • ∑ i ∈ s, (a i).smulRight (v i) = ∑ i ∈ s, (a i).smulRight (z • v i) := by
  ext e
  simp only [FunLike.coe_smul, Pi.smul_apply, FunLike.coe_sum, Finset.sum_apply,
    ContinuousLinearMap.smulRight_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_comm]

theorem clause3_local [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) {A : ℝ}
    {m : ℕ} {F : B.Mat k r → (Wq →L[ℂ] Wp)} (hT : TransportedAlt k r A m) (hF : B.InCC A m F) {O : Set (Fin d → ℝ)}
    {cx : (Fin d → ℝ) → Fin r → ℂ} {μx : (Fin d → ℝ) → B.Mat k 0} (hO : IsOpen O)
    (hcx : ContDiffOn ℝ ∞ cx O) (hμx : ContDiffOn ℝ ∞ μx O)
    (hx : ∀ x ∈ O, (∀ a, cx x a ≠ 0) ∧ μx x ∈ B.GV k 0) {x₀ : Fin d → ℝ} (hx₀ : x₀ ∈ O) :
    ∃ u, IsOpen u ∧ x₀ ∈ u ∧ ContDiffOn ℝ (m : WithTop ℕ∞) (fun x => sliceR D F (cx x) (μx x)) (O ∩ u) := by
  obtain ⟨cF, hcF⟩ := hF
  obtain ⟨hAp, hAB, -, -⟩ := thr_facts hT
  obtain ⟨δ, hδ, hball⟩ : ∃ δ > 0, Metric.closedBall x₀ δ ⊆ O :=
    Metric.nhds_basis_closedBall.mem_iff.1 (hO.mem_nhds hx₀)
  set Ω := Metric.ball x₀ δ with hΩdef
  have hΩO : Ω ⊆ O := Metric.ball_subset_closedBall.trans hball
  have hKX : IsCompact (Metric.closedBall x₀ δ) := isCompact_closedBall _ _
  set K := cx '' Metric.closedBall x₀ δ with hKdef
  have hK : IsCompact K := hKX.image_of_continuousOn (hcx.continuousOn.mono hball)
  have hK0 : ∀ c ∈ K, ∀ a, c a ≠ 0 := by
    rintro c ⟨x, hxK, rfl⟩
    exact (hx x (hball hxK)).1
  obtain ⟨C, hC, hs⟩ := sizes1 k r K hK hK0
  set M := max cF 0 * (((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2) ^ m * C ^ (3 * Ap r A m) with hMdef
  have hM : 0 ≤ M := by
    have : (0 : ℝ) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * C ^ 2 := by positivity
    exact mul_nonneg (mul_nonneg (le_max_right _ _) (pow_nonneg this m))
      (Real.rpow_nonneg (le_trans zero_le_one hC) _)
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite D.haarN
  have hβ : Integrable (beta0 (k := k) (r := r) M (Ap r A m)) (D.μN.prod D.μN) := integrable_slice_weight D.haarN M hAB
  have hβ0 : ∀ ξ, 0 ≤ beta0 (k := k) (r := r) M (Ap r A m) ξ := slice_weight_nonneg hM

  have hacont : ContinuousOn (fun x => ∑ i, ‖aB k r cx μx i x‖) (Metric.closedBall x₀ δ) :=
    continuousOn_finsetSum _ fun i _ => ((aB_cd hO hcx hμx hx i).continuousOn.mono hball).norm
  obtain ⟨Ba, hBa⟩ := hKX.exists_bound_of_continuousOn hacont
  have hBa' : ∀ x ∈ Metric.closedBall x₀ δ, ∑ i, ‖aB k r cx μx i x‖ ≤ Ba := by
    intro x hx'
    have h1 := hBa x hx'
    rwa [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1

  have hbd : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ∀ x ∈ Metric.closedBall x₀ δ, ∀ ξ,
      ‖Fw D F cx μx w x ξ‖ ≤ beta0 M (Ap r A m) ξ := by
    intro w hw x hxK ξ
    by_cases hξ : ξ ∈ Sn k r
    · have e := congrFun (Fw_mem (D := D) (F := F) (cx := cx) (μx := μx) (w := w) hξ) x
      rw [e, norm_smul]
      refine (mul_le_of_le_one_left (norm_nonneg _) (norm_psiN D ξ)).trans ?_
      exact Gw_bound hT hcF hC hs ⟨x, hxK, rfl⟩ (hx x (hball hxK)).1 hξ (hx x (hball hxK)).2 w hw
    · have e := congrFun (Fw_not (D := D) (F := F) (cx := cx) (μx := μx) (w := w) hξ) x
      rw [e, norm_zero]
      exact hβ0 ξ
  have hmeas : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ∀ x ∈ O,
      AEStronglyMeasurable (Fw D F cx μx w x) (D.μN.prod D.μN) := by
    intro w hw x hxO
    exact (continuous_psiN D).aestronglyMeasurable.smul
      (Gw_meas hcF.1 _ w hw _ (phi_contOn (cx x) (μx x))
        (fun ξ hξ => phi_mem (hx x hxO).1 (nset_gv hξ.1) (nset_gv hξ.2) (hx x hxO).2))
  have hbm : ∀ x ∈ O, bmap k r cx μx x ∈ B.GV k r := bmap_mem hx
  have hbc : ContinuousOn (bmap k r cx μx) O := (bmap_cd hcx hμx (fun x hx' => (hx x hx').1)).continuousOn
  have hcont : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ∀ ξ,
      ContinuousOn (fun x => Fw D F cx μx w x ξ) O := by
    intro w hw ξ
    by_cases hξ : ξ ∈ Sn k r
    · rw [Fw_mem hξ]
      have hn : (Matrix.of ξ.1 : B.Mat k r) ∈ B.GV k r := nset_gv hξ.1
      have hn' : (Matrix.of ξ.2 : B.Mat k r) ∈ B.GV k r := nset_gv hξ.2
      have hG := Formalism.FourierDecayAlt.P.B6.continuousOn_of_contDiffOn_group (Gw_ck hcF.1 hn' w hw)
      have hγ : ContinuousOn (fun x => (Matrix.of ξ.1 : B.Mat k r)⁻¹ * bmap k r cx μx x * Matrix.of ξ.2) O :=
        Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul (Formalism.FourierDecayAlt.P.B6.continuousOn_matrix_mul continuousOn_const hbc)
          continuousOn_const
      exact (hG.comp hγ (fun x hxO => Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_mul
        (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gv_inv hn) (hbm x hxO)) hn')).const_smul (psiN D ξ)
    · rw [Fw_not hξ]; exact continuousOn_const
  have hderiv : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length < m → ∀ x ∈ O, ∀ ξ,
      HasFDerivAt (fun y => Fw D F cx μx w y ξ)
        (∑ i, (aB k r cx μx i x).smulRight (Fw D F cx μx (i :: w) x ξ)) x := by
    intro w hw x hxO ξ
    by_cases hξ : ξ ∈ Sn k r
    · rw [Fw_mem hξ]
      have hn : (Matrix.of ξ.1 : B.Mat k r) ∈ B.GV k r := nset_gv hξ.1
      have hn' : (Matrix.of ξ.2 : B.Mat k r) ∈ B.GV k r := nset_gv hξ.2
      have hck : B.CkOn ((1 : ℕ) : ℕ∞) (B.GV k r) (Gw F ξ w) :=
        Formalism.FourierDecayAlt.P.B4.ckOn_mono (by omega) (Gw_ck hcF.1 hn' w hw.le)
      have h1 := (hasFDeriv_slice hO hcx hμx hx hck hn hn' hxO).const_smul (psiN D ξ)
      refine h1.congr_fderiv ?_
      rw [smul_sum_smulRight]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e := congrFun (Fw_mem (D := D) (F := F) (cx := cx) (μx := μx) (w := i :: w) hξ) x
      rw [e]
      rfl
    · rw [Fw_not hξ]
      have : (∑ i, (aB k r cx μx i x).smulRight (Fw D F cx μx (i :: w) x ξ)) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        have e := congrFun (Fw_not (D := D) (F := F) (cx := cx) (μx := μx) (w := i :: w) hξ) x
        rw [e]
        ext; simp
      rw [this]
      exact hasFDerivAt_const _ _

  set L : List (Formalism.FourierDecayAlt.P.Ux10.J k r) → (Fin d → ℝ) → (Wq →L[ℂ] Wp) :=
    fun w x => ∫ ξ, Fw D F cx μx w x ξ ∂(D.μN.prod D.μN) with hLdef
  have hΩK : ∀ x ∈ Ω, x ∈ Metric.closedBall x₀ δ := fun x hx' => Metric.ball_subset_closedBall hx'
  have hLc : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length ≤ m → ContinuousOn (L w) Ω := by
    intro w hw
    exact continuousOn_of_dominated (bound := beta0 M (Ap r A m))
      (fun x hxΩ => hmeas w hw x (hΩO hxΩ))
      (fun x hxΩ => Eventually.of_forall fun ξ => hbd w hw x (hΩK x hxΩ) ξ) hβ
      (Eventually.of_forall fun ξ => (hcont w hw ξ).mono hΩO)
  have hLd : ∀ w : List (Formalism.FourierDecayAlt.P.Ux10.J k r), w.length < m → ∀ Y ∈ Ω,
      HasFDerivAt (L w) (∑ i, (aB k r cx μx i Y).smulRight (L (i :: w) Y)) Y := by
    intro w hw Y hY
    have hYO : Y ∈ O := hΩO hY
    have hεp : 0 < δ - dist Y x₀ := by
      have := Metric.mem_ball.1 hY
      linarith
    have hsub : Metric.ball Y (δ - dist Y x₀) ⊆ Metric.closedBall x₀ δ := by
      intro y hy
      rw [Metric.mem_ball] at hy
      rw [Metric.mem_closedBall]
      calc dist y x₀ ≤ dist y Y + dist Y x₀ := dist_triangle _ _ _
        _ ≤ δ := by linarith
    have hw1 : (∀ i : Formalism.FourierDecayAlt.P.Ux10.J k r, (i :: w).length ≤ m) := fun i => by simpa using hw
    have hint : ∀ i, Integrable (Fw D F cx μx (i :: w) Y) (D.μN.prod D.μN) := fun i =>
      hβ.mono' (hmeas (i :: w) (hw1 i) Y hYO)
        (Eventually.of_forall fun ξ => hbd (i :: w) (hw1 i) Y (hΩK Y hY) ξ)
    have hint' : ∀ i, Integrable (fun ξ => (aB k r cx μx i Y).smulRight (Fw D F cx μx (i :: w) Y ξ))
        (D.μN.prod D.μN) := fun i =>
      (ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) (Wq →L[ℂ] Wp) (aB k r cx μx i Y)).integrable_comp (hint i)
    have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := D.μN.prod D.μN)
      (F := fun y ξ => Fw D F cx μx w y ξ)
      (F' := fun y ξ => ∑ i, (aB k r cx μx i y).smulRight (Fw D F cx μx (i :: w) y ξ))
      (bound := fun ξ => Ba * beta0 M (Ap r A m) ξ) (Metric.ball_mem_nhds Y hεp)
      (by filter_upwards [hO.mem_nhds hYO] with y hy using hmeas w hw.le y hy)
      (hβ.mono' (hmeas w hw.le Y hYO) (Eventually.of_forall fun ξ => hbd w hw.le Y (hΩK Y hY) ξ))
      (Finset.aestronglyMeasurable_fun_sum _ fun i _ => (hint' i).aestronglyMeasurable)
      (Eventually.of_forall fun ξ y hy => by
        have hyK := hsub hy
        refine (norm_sum_le _ _).trans ?_
        calc ∑ i, ‖(aB k r cx μx i y).smulRight (Fw D F cx μx (i :: w) y ξ)‖
            ≤ ∑ i, ‖aB k r cx μx i y‖ * beta0 M (Ap r A m) ξ := by
              refine Finset.sum_le_sum fun i _ => ?_
              rw [ContinuousLinearMap.norm_smulRight_apply]
              exact mul_le_mul_of_nonneg_left (hbd (i :: w) (hw1 i) y hyK ξ) (norm_nonneg _)
          _ = (∑ i, ‖aB k r cx μx i y‖) * beta0 M (Ap r A m) ξ := by rw [Finset.sum_mul]
          _ ≤ Ba * beta0 M (Ap r A m) ξ := mul_le_mul_of_nonneg_right (hBa' y hyK) (hβ0 ξ))
      (hβ.const_mul Ba)
      (Eventually.of_forall fun ξ y hy => hderiv w hw y (hball (hsub hy)) ξ)
    refine key.congr_fderiv ?_
    rw [integral_finsetSum _ fun i _ => hint' i]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact ContinuousLinearMap.integral_comp_comm
      (ContinuousLinearMap.smulRightL ℝ (Fin d → ℝ) (Wq →L[ℂ] Wp) (aB k r cx μx i Y)) (hint i)
  have hALd := Formalism.FourierDecayAlt.P.Ux10.ALd (Ω := Ω) Metric.isOpen_ball (fun i => aB k r cx μx i)
    (fun i => (aB_cd hO hcx hμx hx i).mono hΩO) m L hLc hLd
  refine ⟨Ω, Metric.isOpen_ball, Metric.mem_ball_self hδ, ?_⟩
  refine (hALd.mono Set.inter_subset_right).congr fun x _ => ?_
  simp only [hLdef]
  rw [sliceR_eq]
  rfl

end clause3b

theorem _root_.Formalism.FourierDecayAlt.P.slice_at_last_level_diagonal : Formalism.FourierDecayAlt.JF.LastLevelDiagonalSlice := by
  intro k r Wp Wq _ _ _ _ _ _ D A m F hT hF
  refine ⟨fun c hc μ hμ => (slice_integrable_finite_class D hT hF hc).1 μ hμ, fun c hc => (slice_integrable_finite_class D hT hF hc).2, ?_⟩
  intro d O cx μx hO hcx hμx hx
  exact contDiffOn_of_locally_contDiffOn fun x₀ hx₀ => clause3_local D hT hF hO hcx hμx hx hx₀

end Formalism.FourierDecayAlt.P.SliceLastLevel

end PartE
