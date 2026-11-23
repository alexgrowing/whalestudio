import Formalism.HermitianCurvature.HermitianCurvatureProofs.KloostDensOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TopCellsOfParts

open Matrix MeasureTheory Formalism.QuantumDeterminants Formalism.FourierDecayAlt

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBJ.Fub

variable {p s : ℕ}

def sigQ (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s)) : Equiv.Perm (Fin (p + s)) :=
  (finSumFinEquiv.symm.trans (Equiv.sumCongr σh σb)).trans finSumFinEquiv

section perm
variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s))

theorem sigQ_castAdd (i : Fin p) : sigQ σh σb (Fin.castAdd s i) = Fin.castAdd s (σh i) := by simp [sigQ]

theorem sigQ_natAdd (i : Fin s) : sigQ σh σb (Fin.natAdd p i) = Fin.natAdd p (σb i) := by simp [sigQ]

theorem sigQ_symm_castAdd (i : Fin p) : (sigQ σh σb).symm (Fin.castAdd s i) = Fin.castAdd s (σh.symm i) := by
  rw [Equiv.symm_apply_eq, sigQ_castAdd, Equiv.apply_symm_apply]

theorem sigQ_symm_natAdd (i : Fin s) : (sigQ σh σb).symm (Fin.natAdd p i) = Fin.natAdd p (σb.symm i) := by
  rw [Equiv.symm_apply_eq, sigQ_natAdd, Equiv.apply_symm_apply]

theorem sigQ_symm : (sigQ σh σb).symm = sigQ σh.symm σb.symm := by
  ext x
  induction x using Fin.addCases with
  | left i => rw [sigQ_symm_castAdd, sigQ_castAdd]
  | right i => rw [sigQ_symm_natAdd, sigQ_natAdd]

end perm

def dQ (dh : Fin p → ℂ) (db : Fin s → ℂ) : Fin (p + s) → ℂ := Fin.addCases dh db

section index
variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s))

def lwIn : (U.LW σh ⊕ (Fin s × Fin p)) ⊕ U.LW σb → U.LW (sigQ σh σb)
  | Sum.inl (Sum.inl q) => ⟨(Fin.castAdd s q.1.1, Fin.castAdd s q.1.2), by
      refine ⟨q.2.1, ?_⟩
      show (sigQ σh σb).symm (Fin.castAdd s q.1.2) < (sigQ σh σb).symm (Fin.castAdd s q.1.1)
      rw [sigQ_symm_castAdd, sigQ_symm_castAdd]; exact q.2.2⟩
  | Sum.inl (Sum.inr (i, j)) => ⟨(Fin.natAdd p i, Fin.castAdd s j), by
      refine ⟨show j.val < p + i.val by omega, ?_⟩
      show (sigQ σh σb).symm (Fin.castAdd s j) < (sigQ σh σb).symm (Fin.natAdd p i)
      rw [sigQ_symm_castAdd, sigQ_symm_natAdd]
      show (σh.symm j).val < p + (σb.symm i).val
      have := (σh.symm j).isLt; omega⟩
  | Sum.inr q => ⟨(Fin.natAdd p q.1.1, Fin.natAdd p q.1.2), by
      refine ⟨show p + q.1.2.val < p + q.1.1.val by have : q.1.2.val < q.1.1.val := q.2.1; omega, ?_⟩
      show (sigQ σh σb).symm (Fin.natAdd p q.1.2) < (sigQ σh σb).symm (Fin.natAdd p q.1.1)
      rw [sigQ_symm_natAdd, sigQ_symm_natAdd]
      show p + (σb.symm q.1.2).val < p + (σb.symm q.1.1).val
      have : (σb.symm q.1.2).val < (σb.symm q.1.1).val := q.2.2; omega⟩

theorem lwIn_bij : Function.Bijective (lwIn σh σb) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨i, j⟩) | ⟨⟨a, b⟩, h⟩) ((⟨⟨a', b'⟩, h'⟩ | ⟨i', j'⟩) | ⟨⟨a', b'⟩, h'⟩) e <;>
      simp only [lwIn, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at e
    all_goals first
      | omega
      | (have e1 : a = a' := Fin.ext (by omega)
         have e2 : b = b' := Fin.ext (by omega)
         subst e1 e2; rfl)
      | (have e1 : i = i' := Fin.ext (by omega)
         have e2 : j = j' := Fin.ext (by omega)
         subst e1 e2; rfl)
  · rintro ⟨⟨a, b⟩, hab, hs⟩
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j =>
        rw [sigQ_symm_castAdd, sigQ_symm_castAdd] at hs
        exact ⟨Sum.inl (Sum.inl ⟨(i, j), hab, hs⟩), rfl⟩
      | right j => exfalso; rw [Fin.lt_def] at hab; simp only [Fin.val_natAdd, Fin.val_castAdd] at hab; omega
    | right i =>
      induction b using Fin.addCases with
      | left j => exact ⟨Sum.inl (Sum.inr (i, j)), rfl⟩
      | right j =>
        have hab' : p + j.val < p + i.val := hab
        have hs' : (sigQ σh σb).symm (Fin.natAdd p j) < (sigQ σh σb).symm (Fin.natAdd p i) := hs
        rw [sigQ_symm_natAdd, sigQ_symm_natAdd] at hs'
        have hs'' : p + (σb.symm j).val < p + (σb.symm i).val := hs'
        exact ⟨Sum.inr ⟨(i, j), show j.val < i.val by omega, show (σb.symm j).val < (σb.symm i).val by omega⟩, rfl⟩

def lwEquiv : U.LW (sigQ σh σb) ≃ (U.LW σh ⊕ (Fin s × Fin p)) ⊕ U.LW σb :=
  (Equiv.ofBijective _ (lwIn_bij σh σb)).symm

end index

def utIn (p s : ℕ) : (G.UT p ⊕ (Fin p × Fin s)) ⊕ G.UT s → G.UT (p + s)
  | Sum.inl (Sum.inl q) => ⟨(Fin.castAdd s q.1.1, Fin.castAdd s q.1.2), by exact q.2⟩
  | Sum.inl (Sum.inr (i, j)) => ⟨(Fin.castAdd s i, Fin.natAdd p j), show i.val < p + j.val by omega⟩
  | Sum.inr q => ⟨(Fin.natAdd p q.1.1, Fin.natAdd p q.1.2), show p + q.1.1.val < p + q.1.2.val by
      have : q.1.1.val < q.1.2.val := q.2; omega⟩

theorem utIn_bij (p s : ℕ) : Function.Bijective (utIn p s) := by
  constructor
  · rintro ((⟨⟨a, b⟩, h⟩ | ⟨i, j⟩) | ⟨⟨a, b⟩, h⟩) ((⟨⟨a', b'⟩, h'⟩ | ⟨i', j'⟩) | ⟨⟨a', b'⟩, h'⟩) e <;>
      simp only [utIn, Subtype.mk.injEq, Prod.mk.injEq, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd] at e
    all_goals first
      | omega
      | (have e1 : a = a' := Fin.ext (by omega)
         have e2 : b = b' := Fin.ext (by omega)
         subst e1 e2; rfl)
      | (have e1 : i = i' := Fin.ext (by omega)
         have e2 : j = j' := Fin.ext (by omega)
         subst e1 e2; rfl)
  · rintro ⟨⟨a, b⟩, hab⟩
    induction a using Fin.addCases with
    | left i =>
      induction b using Fin.addCases with
      | left j => exact ⟨Sum.inl (Sum.inl ⟨(i, j), hab⟩), rfl⟩
      | right j => exact ⟨Sum.inl (Sum.inr (i, j)), rfl⟩
    | right i =>
      induction b using Fin.addCases with
      | left j => exfalso; rw [Fin.lt_def] at hab; simp only [Fin.val_natAdd, Fin.val_castAdd] at hab; omega
      | right j => exact ⟨Sum.inr ⟨(i, j), show i.val < j.val by have : p + i.val < p + j.val := hab; omega⟩, rfl⟩

def utEquiv (p s : ℕ) : G.UT (p + s) ≃ (G.UT p ⊕ (Fin p × Fin s)) ⊕ G.UT s :=
  (Equiv.ofBijective _ (utIn_bij p s)).symm

section blocks
variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s))

theorem permutationMatrix_sumCongr : U.wP (sigQ σh σb) = U.blk2 (U.wP σh) 0 0 (U.wP σb) := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j => rw [Dx2.SL.b_cc]; simp [U.wP, sigQ_castAdd, Fin.castAdd_inj]
    | right j =>
      rw [Dx2.SL.b_cn]; simp only [U.wP, Matrix.of_apply, sigQ_castAdd, Matrix.zero_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; simp at this; omega
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_nc]; simp only [U.wP, Matrix.of_apply, sigQ_natAdd, Matrix.zero_apply]
      rw [if_neg]; intro h; have := congrArg Fin.val h; simp at this; omega
    | right j => rw [Dx2.SL.b_nn]; simp [U.wP, sigQ_natAdd, Fin.natAdd_inj]

theorem diag_dQ (dh : Fin p → ℂ) (db : Fin s → ℂ) :
    Matrix.diagonal (dQ dh db) = U.blk2 (Matrix.diagonal dh) 0 0 (Matrix.diagonal db) := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j => rw [Dx2.SL.b_cc]; simp [Matrix.diagonal_apply, dQ, Fin.castAdd_inj]
    | right j =>
      rw [Dx2.SL.b_cn, Matrix.diagonal_apply_ne]
      · rfl
      · intro h; have := congrArg Fin.val h; simp at this; omega
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_nc, Matrix.diagonal_apply_ne]
      · rfl
      · intro h; have := congrArg Fin.val h; simp at this; omega
    | right j => rw [Dx2.SL.b_nn]; simp [Matrix.diagonal_apply, dQ, Fin.natAdd_inj]

theorem hMat_sigQ (dh : Fin p → ℂ) (db : Fin s → ℂ) :
    U.hMat (sigQ σh σb) (dQ dh db) = U.blk2 (U.hMat σh dh) 0 0 (U.hMat σb db) := by
  unfold U.hMat
  rw [permutationMatrix_sumCongr, diag_dQ, Ux2.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

def v1 (v : U.LW (sigQ σh σb) → ℂ) : U.LW σh → ℂ := fun q => v (lwIn σh σb (Sum.inl (Sum.inl q)))
def Am (v : U.LW (sigQ σh σb) → ℂ) : Matrix (Fin s) (Fin p) ℂ :=
  Matrix.of fun i j => v (lwIn σh σb (Sum.inl (Sum.inr (i, j))))
def v2 (v : U.LW (sigQ σh σb) → ℂ) : U.LW σb → ℂ := fun q => v (lwIn σh σb (Sum.inr q))

theorem lowW_sigQ (v : U.LW (sigQ σh σb) → ℂ) :
    U.lowW (sigQ σh σb) v = U.blk2 (U.lowW σh (v1 σh σb v)) 0 (Am σh σb v) (U.lowW σb (v2 σh σb v)) := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_cc]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, Dx2.SL.one_cc]
      congr 1
      by_cases h : j < i ∧ σh.symm j < σh.symm i
      · have h' : Fin.castAdd s j < Fin.castAdd s i ∧
            (sigQ σh σb).symm (Fin.castAdd s j) < (sigQ σh σb).symm (Fin.castAdd s i) := by
          rw [sigQ_symm_castAdd, sigQ_symm_castAdd]; exact h
        rw [dif_pos h, dif_pos h']; rfl
      · have h' : ¬ (Fin.castAdd s j < Fin.castAdd s i ∧
            (sigQ σh σb).symm (Fin.castAdd s j) < (sigQ σh σb).symm (Fin.castAdd s i)) := by
          rw [sigQ_symm_castAdd, sigQ_symm_castAdd]; exact h
        rw [dif_neg h, dif_neg h']
    | right j =>
      rw [Dx2.SL.b_cn]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, Dx2.SL.one_cn, Matrix.zero_apply, zero_add]
      rw [dif_neg]; intro h; have : p + j.val < i.val := h.1; omega
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_nc]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, Dx2.SL.one_nc, zero_add]
      have h' : Fin.castAdd s j < Fin.natAdd p i ∧
          (sigQ σh σb).symm (Fin.castAdd s j) < (sigQ σh σb).symm (Fin.natAdd p i) := by
        refine ⟨show j.val < p + i.val by omega, ?_⟩
        rw [sigQ_symm_castAdd, sigQ_symm_natAdd]
        show (σh.symm j).val < p + (σb.symm i).val
        have := (σh.symm j).isLt; omega
      rw [dif_pos h']; rfl
    | right j =>
      rw [Dx2.SL.b_nn]
      simp only [U.lowW, Matrix.add_apply, Matrix.of_apply, Dx2.SL.one_nn]
      congr 1
      by_cases h : j < i ∧ σb.symm j < σb.symm i
      · have h' : Fin.natAdd p j < Fin.natAdd p i ∧
            (sigQ σh σb).symm (Fin.natAdd p j) < (sigQ σh σb).symm (Fin.natAdd p i) := by
          rw [sigQ_symm_natAdd, sigQ_symm_natAdd]
          exact ⟨show p + j.val < p + i.val by have : j.val < i.val := h.1; omega,
            show p + (σb.symm j).val < p + (σb.symm i).val by
              have : (σb.symm j).val < (σb.symm i).val := h.2; omega⟩
        rw [dif_pos h, dif_pos h']; rfl
      · have h' : ¬ (Fin.natAdd p j < Fin.natAdd p i ∧
            (sigQ σh σb).symm (Fin.natAdd p j) < (sigQ σh σb).symm (Fin.natAdd p i)) := by
          rw [sigQ_symm_natAdd, sigQ_symm_natAdd]
          rintro ⟨h1, h2⟩
          apply h
          exact ⟨show j.val < i.val by have : p + j.val < p + i.val := h1; omega,
            show (σb.symm j).val < (σb.symm i).val by
              have : p + (σb.symm j).val < p + (σb.symm i).val := h2; omega⟩
        rw [dif_neg h, dif_neg h']

end blocks

section ublocks
variable (p s)

def u1 (u : G.UT (p + s) → ℂ) : G.UT p → ℂ := fun q => u (utIn p s (Sum.inl (Sum.inl q)))
def Bm (u : G.UT (p + s) → ℂ) : Matrix (Fin p) (Fin s) ℂ :=
  Matrix.of fun i j => u (utIn p s (Sum.inl (Sum.inr (i, j))))
def u2 (u : G.UT (p + s) → ℂ) : G.UT s → ℂ := fun q => u (utIn p s (Sum.inr q))

theorem upper_split (u : G.UT (p + s) → ℂ) :
    G.upper u = U.blk2 (G.upper (u1 p s u)) (Bm p s u) 0 (G.upper (u2 p s u)) := by
  ext a b
  induction a using Fin.addCases with
  | left i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_cc]; simp only [G.upper, Matrix.add_apply, Dx2.SL.one_cc, G.strictUpper, Matrix.of_apply]
      congr 1
    | right j =>
      rw [Dx2.SL.b_cn]; simp only [G.upper, Matrix.add_apply, Dx2.SL.one_cn, G.strictUpper, Matrix.of_apply, zero_add]
      rw [dif_pos (show Fin.castAdd s i < Fin.natAdd p j from show i.val < p + j.val by omega)]; rfl
  | right i =>
    induction b using Fin.addCases with
    | left j =>
      rw [Dx2.SL.b_nc]; simp only [G.upper, Matrix.add_apply, Dx2.SL.one_nc, G.strictUpper, Matrix.of_apply,
        zero_add, Matrix.zero_apply]
      rw [dif_neg]; intro h; have : p + i.val < j.val := h; omega
    | right j =>
      rw [Dx2.SL.b_nn]; simp only [G.upper, Matrix.add_apply, Dx2.SL.one_nn, G.strictUpper, Matrix.of_apply]
      congr 1
      by_cases h : i < j
      · rw [dif_pos h, dif_pos (show Fin.natAdd p i < Fin.natAdd p j from show p + i.val < p + j.val by
          have : i.val < j.val := h; omega)]; rfl
      · rw [dif_neg h, dif_neg (show ¬ (Fin.natAdd p i < Fin.natAdd p j) from fun h' => h (show i.val < j.val by
          have : p + i.val < p + j.val := h'; omega))]

end ublocks

section ident
variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s)) (dh : Fin p → ℂ) (db : Fin s → ℂ)

def aN (v : U.LW (sigQ σh σb) → ℂ) : Matrix (Fin s) (Fin p) ℂ :=
  U.wP σb * Am σh σb v * ((U.lowW σh (v1 σh σb v))⁻¹ * (U.wP σh)⁻¹)
def bN (p s : ℕ) (u : G.UT (p + s) → ℂ) : Matrix (Fin p) (Fin s) ℂ := (G.upper (u1 p s u))⁻¹ * Bm p s u

theorem headH_split (v : U.LW (sigQ σh σb) → ℂ) (u : G.UT (p + s) → ℂ) :
    U.headH (sigQ σh σb) (dQ dh db) v u =
      U.blk2 (U.wP σh * U.lowW σh (v1 σh σb v) * Matrix.diagonal dh * G.upper (u1 p s u))
        (U.wP σh * U.lowW σh (v1 σh σb v) * Matrix.diagonal dh * Bm p s u)
        (U.wP σb * Am σh σb v * Matrix.diagonal dh * G.upper (u1 p s u))
        (U.wP σb * Am σh σb v * Matrix.diagonal dh * Bm p s u +
          U.wP σb * U.lowW σb (v2 σh σb v) * Matrix.diagonal db * G.upper (u2 p s u)) := by
  unfold U.headH
  rw [permutationMatrix_sumCongr, lowW_sigQ, diag_dQ, upper_split]
  simp only [Ux2.symmetricScalarBlockMatrix_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]

theorem zj_split (v : U.LW (sigQ σh σb) → ℂ) (u : G.UT (p + s) → ℂ) :
    U.headH (sigQ σh σb) (dQ dh db) v u =
      U.Zj (Matrix.of.symm (aN σh σb v)) (Matrix.of.symm (bN p s u)) (U.headH σh dh (v1 σh σb v) (u1 p s u))
        (U.headH σb db (v2 σh σb v) (u2 p s u)) := by
  have hL := Matrix.nonsing_inv_mul _ (Dx2.SL.isUnit_low σh (v1 σh σb v))
  have hW := Matrix.nonsing_inv_mul _ (Dx2.SL.isUnit_wP σh)
  have hU := Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_up (u1 p s u))
  have hHb : U.headH σh dh (v1 σh σb v) (u1 p s u) * bN p s u =
      U.wP σh * U.lowW σh (v1 σh σb v) * Matrix.diagonal dh * Bm p s u := by
    unfold U.headH bN
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.upper (u1 p s u)), hU, Matrix.one_mul]
  have hAH : aN σh σb v * U.headH σh dh (v1 σh σb v) (u1 p s u) =
      U.wP σb * Am σh σb v * Matrix.diagonal dh * G.upper (u1 p s u) := by
    unfold U.headH aN
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP σh)⁻¹ (U.wP σh), hW, Matrix.one_mul,
      ← Matrix.mul_assoc (U.lowW σh (v1 σh σb v))⁻¹, hL, Matrix.one_mul]
  have hAHb : aN σh σb v * U.headH σh dh (v1 σh σb v) (u1 p s u) * bN p s u =
      U.wP σb * Am σh σb v * Matrix.diagonal dh * Bm p s u := by
    rw [hAH]
    unfold bN
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (G.upper (u1 p s u)), hU, Matrix.one_mul]
  rw [headH_split, Ux4.ux_zjAffine]
  simp only [Equiv.apply_symm_apply]
  rw [hHb, hAHb, hAH]
  rfl

end ident

section chars
variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s))

theorem conj_split (v : U.LW (sigQ σh σb) → ℂ) :
    U.wP (sigQ σh σb) * U.lowW (sigQ σh σb) v * (U.wP (sigQ σh σb))⁻¹ =
      U.blk2 1 0 (Matrix.of (Matrix.of.symm (aN σh σb v))) 1 *
        U.blk2 (U.wP σh * U.lowW σh (v1 σh σb v) * (U.wP σh)⁻¹) 0 0
          (U.wP σb * U.lowW σb (v2 σh σb v) * (U.wP σb)⁻¹) := by
  have hL := Matrix.nonsing_inv_mul _ (Dx2.SL.isUnit_low σh (v1 σh σb v))
  have hW : U.wP σh.symm * U.wP σh = 1 := Ux2.permutationMatrix_symm_mul σh
  have hC : aN σh σb v * (U.wP σh * U.lowW σh (v1 σh σb v) * U.wP σh.symm) =
      U.wP σb * Am σh σb v * U.wP σh.symm := by
    unfold aN
    rw [Ux2.permutationMatrix_inv]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP σh.symm) (U.wP σh), hW, Matrix.one_mul,
      ← Matrix.mul_assoc (U.lowW σh (v1 σh σb v))⁻¹, hL, Matrix.one_mul]
  rw [Ux2.permutationMatrix_inv, sigQ_symm, permutationMatrix_sumCongr, permutationMatrix_sumCongr, lowW_sigQ, Ux2.permutationMatrix_inv, Ux2.permutationMatrix_inv]
  simp only [Ux2.symmetricScalarBlockMatrix_mul, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul,
    Equiv.apply_symm_apply]
  rw [hC]

theorem upper_fact (u : G.UT (p + s) → ℂ) :
    G.upper u = U.blk2 (G.upper (u1 p s u)) 0 0 (G.upper (u2 p s u)) *
      U.blk2 1 (Matrix.of (Matrix.of.symm (bN p s u))) 0 1 := by
  rw [upper_split, Ux2.symmetricScalarBlockMatrix_mul]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one,
    Equiv.apply_symm_apply]
  unfold bN
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_up (u1 p s u)), Matrix.one_mul]

theorem psiH_split (β : ℂ) (a0 : Fin 0 → Fin (p + s) → ℂ) (b0 : Fin (p + s) → Fin 0 → ℂ)
    (e1 : (Fin 0 → Fin s → ℂ) × (Fin s → Fin 0 → ℂ)) (v : U.LW (sigQ σh σb) → ℂ) (u : G.UT (p + s) → ℂ) :
    U.psiH (s := 0) β (sigQ σh σb) ((a0, b0), (v, u)) =
      U.psiH (s := s) β σh ((Matrix.of.symm (aN σh σb v), Matrix.of.symm (bN p s u)), (v1 σh σb v, u1 p s u)) *
        U.psiH (s := 0) β σb (e1, (v2 σh σb v, u2 p s u)) := by
  unfold U.psiH
  simp only
  rw [← Dx2.SL.psi_add, conj_split, upper_fact u, Dx2.SL.cornerA_zero, Dx2.SL.cornerB_zero,
    Dx2.SL.cornerA_zero, Dx2.SL.cornerB_zero]
  have hlow := ((Formalism.FourierDecayAlt.P.low_weight_specialisation p σh (U.lowW σh (v1 σh σb v))).mpr ⟨v1 σh σb v, rfl⟩)
  have hlowb := ((Formalism.FourierDecayAlt.P.low_weight_specialisation s σb (U.lowW σb (v2 σh σb v))).mpr ⟨v2 σh σb v, rfl⟩)
  have huh : G.IsUpperUni (G.upper (u1 p s u)) := (Ux2.upper_iff _).mpr (Ux2.upper_uni _)
  have hu2 : G.IsUpperUni (G.upper (u2 p s u)) := (Ux2.upper_iff _).mpr (Ux2.upper_uni _)
  obtain ⟨cA, cB⟩ := Formalism.FourierDecayAlt.P.character_on_blocks p s (Matrix.of.symm (aN σh σb v)) (Matrix.of.symm (bN p s u))
    (U.wP σh * U.lowW σh (v1 σh σb v) * (U.wP σh)⁻¹) (G.upper (u1 p s u))
    (U.wP σb * U.lowW σb (v2 σh σb v) * (U.wP σb)⁻¹) (G.upper (u2 p s u)) hlow.2 hlowb.2 huh hu2
  rw [cA, cB]
  congr 1
  ring

end chars

section shear

theorem fa_mp' (τ : Equiv.Perm (Fin s)) (N : Matrix (Fin p) (Fin p) ℂ) (hN : Complex.normSq N.det = 1) :
    MeasurePreserving (fun y : Fin s → Fin p → ℂ => Matrix.of.symm (U.wP τ * Matrix.of y * N)) volume volume := by
  have h1 := Dx2.SL.reindex_mp (X := Fin p → ℂ) τ
  have h2 : MeasurePreserving (fun (y : Fin s → Fin p → ℂ) (i : Fin s) => Matrix.vecMul (y i) N) volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume) (f := fun _ x => Matrix.vecMul x N)
      (fun _ => Dx2.SL.row_mp N hN)
  have e : (fun y : Fin s → Fin p → ℂ => Matrix.of.symm (U.wP τ * Matrix.of y * N)) =
      (fun (y : Fin s → Fin p → ℂ) (i : Fin s) => Matrix.vecMul (y i) N) ∘
        (fun (y : Fin s → Fin p → ℂ) (i : Fin s) => y (τ i)) := by
    funext y i j
    simp only [Function.comp, Matrix.of_symm_apply, Matrix.mul_assoc]
    simp [U.wP, Matrix.mul_apply, Matrix.vecMul, dotProduct]
  rw [e]; exact h2.comp h1

theorem fb_mp' (M : Matrix (Fin p) (Fin p) ℂ) (hM : Complex.normSq M.det = 1) :
    MeasurePreserving (fun y : Fin p → Fin s → ℂ => Matrix.of.symm (M * Matrix.of y)) volume volume := by
  have h1 := Dx2.SL.swap_mp p s
  have h2 : MeasurePreserving (fun (y : Fin s → Fin p → ℂ) (j : Fin s) => Matrix.vecMul (y j) Mᵀ)
      volume volume :=
    measurePreserving_pi (fun _ => volume) (fun _ => volume) (f := fun _ x => Matrix.vecMul x Mᵀ)
      (fun _ => Dx2.SL.row_mp Mᵀ (by rw [Matrix.det_transpose]; exact hM))
  have h3 := Dx2.SL.swap_mp s p
  have e : (fun y : Fin p → Fin s → ℂ => Matrix.of.symm (M * Matrix.of y)) =
      (fun (y : Fin s → Fin p → ℂ) (i : Fin p) (j : Fin s) => y j i) ∘
        (fun (y : Fin s → Fin p → ℂ) (j : Fin s) => Matrix.vecMul (y j) Mᵀ) ∘
          (fun (y : Fin p → Fin s → ℂ) (j : Fin s) (i : Fin p) => y i j) := by
    funext y i j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, mul_comm]
  rw [e]; exact h3.comp (h2.comp h1)

variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s))

def shF (x : (U.LW σh → ℂ) × (G.UT p → ℂ)) (y : (Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) :
    (Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ) :=
  (Matrix.of.symm (U.wP σb * Matrix.of y.1 * ((U.lowW σh x.1)⁻¹ * (U.wP σh)⁻¹)),
   Matrix.of.symm ((G.upper x.2)⁻¹ * Matrix.of y.2))

def shG (x : (U.LW σh → ℂ) × (G.UT p → ℂ)) (y : (Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) :
    (Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ) :=
  (Matrix.of.symm (U.wP σb.symm * Matrix.of y.1 * (U.wP σh * U.lowW σh x.1)),
   Matrix.of.symm (G.upper x.2 * Matrix.of y.2))

theorem shG_shF (x) (y : (Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) : shG σh σb x (shF σh σb x y) = y := by
  have hL := Matrix.nonsing_inv_mul _ (Dx2.SL.isUnit_low σh x.1)
  have hW := Matrix.nonsing_inv_mul _ (Dx2.SL.isUnit_wP σh)
  have hU := Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_up x.2)
  ext1
  · simp only [shG, shF, Equiv.apply_symm_apply]
    apply (Matrix.of).symm.injective.eq_iff.mpr
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP σb.symm) (U.wP σb), Ux2.permutationMatrix_symm_mul, Matrix.one_mul]
    rw [← Matrix.mul_assoc (U.wP σh)⁻¹ (U.wP σh), hW, Matrix.one_mul, hL, Matrix.mul_one]; rfl
  · simp only [shG, shF, Equiv.apply_symm_apply]
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]; rfl

theorem shF_shG (x) (y : (Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) : shF σh σb x (shG σh σb x y) = y := by
  have hL := Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_low σh x.1)
  have hW := Matrix.mul_nonsing_inv _ (Dx2.SL.isUnit_wP σh)
  have hU := Matrix.nonsing_inv_mul _ (Dx2.SL.isUnit_up x.2)
  ext1
  · simp only [shG, shF, Equiv.apply_symm_apply]
    apply (Matrix.of).symm.injective.eq_iff.mpr
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (U.wP σb) (U.wP σb.symm), Ux2.permutationMatrix_mul_symm, Matrix.one_mul]
    rw [← Matrix.mul_assoc (U.lowW σh x.1) (U.lowW σh x.1)⁻¹, hL, Matrix.one_mul, hW, Matrix.mul_one]; rfl
  · simp only [shG, shF, Equiv.apply_symm_apply]
    rw [← Matrix.mul_assoc, hU, Matrix.one_mul]; rfl

theorem cont_shF : Continuous (fun q : ((U.LW σh → ℂ) × (G.UT p → ℂ)) ×
    ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) => shF σh σb q.1 q.2) := by
  have e : (fun q : ((U.LW σh → ℂ) × (G.UT p → ℂ)) ×
      ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) => shF σh σb q.1 q.2) =
      fun q => (Matrix.of.symm (U.wP σb * Matrix.of q.2.1 * ((U.lowW σh q.1.1).adjugate * (U.wP σh)⁻¹)),
        Matrix.of.symm ((G.upper q.1.2).adjugate * Matrix.of q.2.2)) := by
    funext q
    simp only [shF, Dx2.SL.inv_adj _ (Ux3.det_lowW σh q.1.1), Dx2.SL.inv_adj _ (Ux3.det_upper q.1.2)]
  rw [e]
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_const.matrix_mul (continuous_snd.fst : Continuous fun q : ((U.LW σh → ℂ) × (G.UT p → ℂ)) ×
      ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) => (Matrix.of q.2.1 : Matrix _ _ ℂ))).matrix_mul
      (((Dx2.SL.cont_lowW σh).comp continuous_fst.fst).matrix_adjugate.matrix_mul continuous_const)
  · exact ((Dx2.SL.cont_upper.comp continuous_fst.snd).matrix_adjugate).matrix_mul
      (continuous_snd.snd : Continuous fun q : ((U.LW σh → ℂ) × (G.UT p → ℂ)) ×
      ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) => (Matrix.of q.2.2 : Matrix _ _ ℂ))

theorem cont_shG : Continuous (fun q : ((U.LW σh → ℂ) × (G.UT p → ℂ)) ×
    ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) => shG σh σb q.1 q.2) := by
  refine Continuous.prodMk ?_ ?_
  · exact (continuous_const.matrix_mul (continuous_snd.fst : Continuous fun q : ((U.LW σh → ℂ) × (G.UT p → ℂ)) ×
      ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) => (Matrix.of q.2.1 : Matrix _ _ ℂ))).matrix_mul
      (continuous_const.matrix_mul ((Dx2.SL.cont_lowW σh).comp continuous_fst.fst))
  · exact (Dx2.SL.cont_upper.comp continuous_fst.snd).matrix_mul
      (continuous_snd.snd : Continuous fun q : ((U.LW σh → ℂ) × (G.UT p → ℂ)) ×
      ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) => (Matrix.of q.2.2 : Matrix _ _ ℂ))

def shearE : ((U.LW σh → ℂ) × (G.UT p → ℂ)) × ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) ≃ᵐ
    ((U.LW σh → ℂ) × (G.UT p → ℂ)) × ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ)) where
  toFun q := (q.1, shF σh σb q.1 q.2)
  invFun q := (q.1, shG σh σb q.1 q.2)
  left_inv q := by simp only [shG_shF]
  right_inv q := by simp only [shF_shG]
  measurable_toFun := measurable_fst.prodMk (cont_shF σh σb).measurable
  measurable_invFun := measurable_fst.prodMk (cont_shG σh σb).measurable

theorem shearE_mp : MeasurePreserving (shearE σh σb) volume volume := by
  have hx : ∀ x : (U.LW σh → ℂ) × (G.UT p → ℂ), MeasurePreserving (shF σh σb x) volume volume := by
    intro x
    have hN : Complex.normSq (((U.lowW σh x.1)⁻¹ * (U.wP σh)⁻¹)).det = 1 := by
      rw [Matrix.det_mul, Dx2.SL.det_inv_low, one_mul, Ux2.permutationMatrix_inv, Dx2.SL.normSq_det_wP]
    have hM : Complex.normSq ((G.upper x.2)⁻¹).det = 1 := by rw [Dx2.SL.det_inv_up]; simp
    exact (fa_mp' σb _ hN).prod (fb_mp' _ hM)
  have s1 : SFinite (volume : Measure ((U.LW σh → ℂ) × (G.UT p → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have i1 : SigmaFinite (volume : Measure (Fin s → Fin p → ℂ)) := inferInstance
  have i2 : SigmaFinite (volume : Measure (Fin p → Fin s → ℂ)) := inferInstance
  have s2 : SFinite (volume : Measure ((Fin s → Fin p → ℂ) × (Fin p → Fin s → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Measure.volume_eq_prod (α := (U.LW σh → ℂ) × (G.UT p → ℂ))]
  exact MeasurePreserving.skew_product (f := id) (MeasurePreserving.id _) (cont_shF σh σb).measurable
    (Filter.Eventually.of_forall fun x => (hx x).map_eq)

end shear

section split
variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s))

def lwSplit : (U.LW (sigQ σh σb) → ℂ) ≃ᵐ ((U.LW σh → ℂ) × (Fin s → Fin p → ℂ)) × (U.LW σb → ℂ) :=
  (Dx2.SL.reE (X := ℂ) (lwEquiv σh σb).symm).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
    (MeasurableEquiv.prodCongr ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin s) (Fin p) ℂ)))
      (MeasurableEquiv.refl _)))

theorem lwSplit_apply (v : U.LW (sigQ σh σb) → ℂ) :
    lwSplit σh σb v = ((v1 σh σb v, Matrix.of.symm (Am σh σb v)), v2 σh σb v) := by
  rfl

theorem lwSplit_mp : MeasurePreserving (lwSplit σh σb) volume ((volume.prod volume).prod volume) := by
  have h1 := Dx2.SL.reindex_mp (X := ℂ) (lwEquiv σh σb).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : (U.LW σh ⊕ (Fin s × Fin p)) ⊕ U.LW σb => (volume : Measure ℂ))
  have h3 := measurePreserving_sumPiEquivProdPi (fun _ : U.LW σh ⊕ (Fin s × Fin p) => (volume : Measure ℂ))
  have h4 : MeasurePreserving (MeasurableEquiv.prodCongr ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin s) (Fin p) ℂ)))
      (MeasurableEquiv.refl (U.LW σb → ℂ)))
      ((Measure.pi fun _ : U.LW σh ⊕ (Fin s × Fin p) => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : U.LW σb => (volume : Measure ℂ)))
      ((volume.prod volume).prod volume) :=
    (((MeasurePreserving.id _).prod (Dx2.SL.curry_mp (Fin s) (Fin p))).comp h3).prod (MeasurePreserving.id _)
  exact h4.comp (h2.comp h1)

variable (p s) in

def utSplit : (G.UT (p + s) → ℂ) ≃ᵐ ((G.UT p → ℂ) × (Fin p → Fin s → ℂ)) × (G.UT s → ℂ) :=
  (Dx2.SL.reE (X := ℂ) (utEquiv p s).symm).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
    (MeasurableEquiv.prodCongr ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin p) (Fin s) ℂ)))
      (MeasurableEquiv.refl _)))

theorem utSplit_apply (u : G.UT (p + s) → ℂ) :
    utSplit p s u = ((u1 p s u, Matrix.of.symm (Bm p s u)), u2 p s u) := by
  rfl

theorem utSplit_mp : MeasurePreserving (utSplit p s) volume ((volume.prod volume).prod volume) := by
  have h1 := Dx2.SL.reindex_mp (X := ℂ) (utEquiv p s).symm
  have h2 := measurePreserving_sumPiEquivProdPi
    (fun _ : (G.UT p ⊕ (Fin p × Fin s)) ⊕ G.UT s => (volume : Measure ℂ))
  have h3 := measurePreserving_sumPiEquivProdPi (fun _ : G.UT p ⊕ (Fin p × Fin s) => (volume : Measure ℂ))
  have h4 : MeasurePreserving (MeasurableEquiv.prodCongr ((MeasurableEquiv.sumPiEquivProdPi (fun _ => ℂ)).trans
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.curry (Fin p) (Fin s) ℂ)))
      (MeasurableEquiv.refl (G.UT s → ℂ)))
      ((Measure.pi fun _ : G.UT p ⊕ (Fin p × Fin s) => (volume : Measure ℂ)).prod
        (Measure.pi fun _ : G.UT s => (volume : Measure ℂ)))
      ((volume.prod volume).prod volume) :=
    (((MeasurePreserving.id _).prod (Dx2.SL.curry_mp (Fin p) (Fin s))).comp h3).prod (MeasurePreserving.id _)
  exact h4.comp (h2.comp h1)

end split

section xi
variable (σh : Equiv.Perm (Fin p)) (σb : Equiv.Perm (Fin s))

def xiE : U.XiH (p + s) 0 (sigQ σh σb) ≃ᵐ U.XiH p s σh × U.XiH s 0 σb :=
  (Dx2.SL.dropE ((Fin 0 → Fin (p + s) → ℂ) × (Fin (p + s) → Fin 0 → ℂ)) _).trans
    ((MeasurableEquiv.prodCongr (lwSplit σh σb) (utSplit p s)).trans
      (Dx2.SL.swap4.trans (MeasurableEquiv.prodCongr
        (Dx2.SL.swap4.trans ((shearE σh σb).trans MeasurableEquiv.prodComm))
        (Dx2.SL.dropE ((Fin 0 → Fin s → ℂ) × (Fin s → Fin 0 → ℂ)) _).symm)))

theorem xiE_apply (η : U.XiH (p + s) 0 (sigQ σh σb)) :
    xiE σh σb η = (((Matrix.of.symm (aN σh σb η.2.1), Matrix.of.symm (bN p s η.2.2)),
      (v1 σh σb η.2.1, u1 p s η.2.2)), ((Dx2.SL.uniqueT s).toInhabited.default, (v2 σh σb η.2.1, u2 p s η.2.2))) := by
  rfl

theorem xiE_mp : MeasurePreserving (xiE σh σb) volume (volume.prod volume) := by
  have hT := Dx2.SL.probT (p + s)
  have hTb := Dx2.SL.probT s
  have i1 : SigmaFinite (volume : Measure (Fin s → Fin p → ℂ)) := inferInstance
  have i2 : SigmaFinite (volume : Measure (Fin p → Fin s → ℂ)) := inferInstance
  have i3 : SigmaFinite (volume : Measure (U.LW σh → ℂ)) := inferInstance
  have i4 : SigmaFinite (volume : Measure (G.UT p → ℂ)) := inferInstance
  have i5 : SigmaFinite (volume : Measure (G.UT s → ℂ)) := inferInstance
  have i6 : SigmaFinite (volume : Measure (U.LW σb → ℂ)) := inferInstance
  have h1 : MeasurePreserving (Dx2.SL.dropE ((Fin 0 → Fin (p + s) → ℂ) × (Fin (p + s) → Fin 0 → ℂ))
      ((U.LW (sigQ σh σb) → ℂ) × (G.UT (p + s) → ℂ))) volume (volume.prod volume) :=
    Dx2.SL.dropE_mp _ _ volume _
  have h2 := (lwSplit_mp σh σb).prod (utSplit_mp (p := p) (s := s))
  have h3 := Dx2.SL.measurePreserving_prod_middle_swap ((volume : Measure (U.LW σh → ℂ)).prod (volume : Measure (Fin s → Fin p → ℂ)))
    (volume : Measure (U.LW σb → ℂ)) ((volume : Measure (G.UT p → ℂ)).prod (volume : Measure (Fin p → Fin s → ℂ)))
    (volume : Measure (G.UT s → ℂ))
  have h4a := Dx2.SL.measurePreserving_prod_middle_swap (volume : Measure (U.LW σh → ℂ)) (volume : Measure (Fin s → Fin p → ℂ))
    (volume : Measure (G.UT p → ℂ)) (volume : Measure (Fin p → Fin s → ℂ))
  have h4b := shearE_mp σh σb
  have h4c := Measure.measurePreserving_swap
    (μ := ((volume : Measure (U.LW σh → ℂ)).prod (volume : Measure (G.UT p → ℂ))))
    (ν := ((volume : Measure (Fin s → Fin p → ℂ)).prod (volume : Measure (Fin p → Fin s → ℂ))))
  have h5 := (Dx2.SL.dropE_mp ((Fin 0 → Fin s → ℂ) × (Fin s → Fin 0 → ℂ)) ((U.LW σb → ℂ) × (G.UT s → ℂ)) volume
    ((volume : Measure (U.LW σb → ℂ)).prod (volume : Measure (G.UT s → ℂ)))).symm _
  exact ((h4c.comp (h4b.comp h4a)).prod h5).comp (h3.comp (h2.comp h1))

end xi

section core

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem sfXiH (P S : ℕ) (σ : Equiv.Perm (Fin P)) : SFinite (volume : Measure (U.XiH P S σ)) := by
  have c1 : SigmaFinite (volume : Measure (Fin S → Fin P → ℂ)) := inferInstance
  have c2 : SigmaFinite (volume : Measure (Fin P → Fin S → ℂ)) := inferInstance
  have c3 : SigmaFinite (volume : Measure (U.LW σ → ℂ)) := inferInstance
  have c4 : SigmaFinite (volume : Measure (G.UT P → ℂ)) := inferInstance
  have c5 : SigmaFinite (volume : Measure ((Fin S → Fin P → ℂ) × (Fin P → Fin S → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  have c6 : SigmaFinite (volume : Measure ((U.LW σ → ℂ) × (G.UT P → ℂ))) := by
    rw [Measure.volume_eq_prod]; infer_instance
  rw [Measure.volume_eq_prod]; infer_instance

theorem fub_core (β : ℂ) (σh : Equiv.Perm (Fin p)) (dh : Fin p → ℂ) (σb : Equiv.Perm (Fin s)) (db : Fin s → ℂ)
    (Ψ : G.Mat (p + s) → V)
    (hint : Integrable (fun η : U.XiH (p + s) 0 (sigQ σh σb) =>
      U.psiH β (sigQ σh σb) η • Ψ (U.ZjH (p := p + s) (s := 0) (sigQ σh σb) (dQ dh db) η (fun x => x.elim0)))
      (U.muXiH (p + s) 0 (sigQ σh σb))) :
    U.PhiTop (p := p + s) (s := 0) β (sigQ σh σb) (dQ dh db) Ψ (fun x => x.elim0) =
      U.PhiTop (p := s) (s := 0) β σb db (U.PhiTop (p := p) (s := s) β σh dh Ψ) (fun x => x.elim0) := by
  let g : U.XiH p s σh × U.XiH s 0 σb → V := fun y =>
    U.psiH β σb y.2 • (U.psiH β σh y.1 •
      Ψ (U.ZjH (p := p) (s := s) σh dh y.1 (U.ZjH (p := s) (s := 0) σb db y.2 (fun x => x.elim0))))
  have hfg : (fun η : U.XiH (p + s) 0 (sigQ σh σb) =>
      U.psiH β (sigQ σh σb) η • Ψ (U.ZjH (p := p + s) (s := 0) (sigQ σh σb) (dQ dh db) η (fun x => x.elim0))) =
      g ∘ xiE σh σb := by
    funext η
    obtain ⟨⟨a0, b0⟩, v, u⟩ := η
    rw [Function.comp_apply, xiE_apply]
    simp only [g, U.ZjH, Dx2.SL.zj_zero]
    rw [zj_split σh σb dh db v u, psiH_split σh σb β a0 b0 (Dx2.SL.uniqueT s).toInhabited.default v u, mul_comm]
    exact (smul_smul _ _ _).symm
  have hΦ := xiE_mp σh σb
  have s1 := sfXiH p s σh
  have s2 := sfXiH s 0 σb
  have hg : Integrable g ((volume : Measure (U.XiH p s σh)).prod (volume : Measure (U.XiH s 0 σb))) := by
    have := hint
    rw [hfg] at this
    exact (hΦ.integrable_comp_emb (xiE σh σb).measurableEmbedding).mp this
  have hL : U.PhiTop (p := p + s) (s := 0) β (sigQ σh σb) (dQ dh db) Ψ (fun x => x.elim0) =
      ∫ y, g y ∂((volume : Measure (U.XiH p s σh)).prod (volume : Measure (U.XiH s 0 σb))) := by
    unfold U.PhiTop
    rw [show U.muXiH (p + s) 0 (sigQ σh σb) = volume from rfl, hfg]
    exact hΦ.integral_comp' g
  rw [hL, MeasureTheory.integral_prod_symm g hg]
  unfold U.PhiTop
  rw [show U.muXiH s 0 σb = volume from rfl]
  congr 1
  funext y
  simp only [g]
  rw [integral_smul]
  rfl

end core

section integ

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem integrable_cls {n : ℕ} (β : ℂ) (σ : Equiv.Perm (Fin n)) (d : Fin n → ℂ) (hd : ∀ i, d i ≠ 0)
    (Ψ : G.Mat n → V) (hΨ : KCls Ψ) :
    Integrable (fun η : U.XiH n 0 σ => U.psiH β σ η • Ψ (U.ZjH σ d η (fun x => x.elim0))) (U.muXiH n 0 σ) := by
  obtain ⟨hs, hc, _⟩ := hΨ
  have : OpensMeasurableSpace (U.XiH n 0 σ) := by unfold U.XiH; exact Prod.opensMeasurableSpace
  have : IsFiniteMeasureOnCompacts (volume : Measure (U.XiH n 0 σ)) := by
    unfold U.XiH; infer_instance
  change Integrable _ (volume : Measure (U.XiH n 0 σ))
  have hcont : Continuous (fun η : U.XiH n 0 σ => U.psiH β σ η • Ψ (U.ZjH σ d η (fun x => x.elim0))) :=
    (Ux13.continuous_psiH β σ).smul (hs.continuous.comp (Ux13.continuous_zjH σ d _))
  obtain ⟨C, hC⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 n 0 σ d hd
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport Ψ) from hc).isBounded.exists_norm_le
  have hR0 : 0 ≤ max R 0 := le_max_right _ _
  refine hcont.integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (isCompact_closedBall (0 : U.XiH n 0 σ) (|C| * (max R 0) ^ n)) ?_
  intro η hη
  by_contra hne
  have hΨne : Ψ (U.ZjH σ d η (fun x => x.elim0)) ≠ 0 := fun h0 => hne (by rw [h0, smul_zero])
  have hmem : (U.ZjH σ d η (fun x => x.elim0) : G.Mat n) ∈ tsupport Ψ :=
    subset_tsupport _ (Function.mem_support.mpr hΨne)
  have hmx : U.mx (U.ZjH σ d η (fun x => x.elim0)) ≤ max R 0 :=
    le_trans (hR _ hmem) (le_max_left _ _)
  have hmx0 : 0 ≤ U.mx (U.ZjH σ d η (fun x => x.elim0)) := norm_nonneg _
  have hpow : U.mx (U.ZjH σ d η (fun x => x.elim0)) ^ n ≤ (max R 0) ^ n := pow_le_pow_left₀ hmx0 hmx n
  obtain ⟨h1, h2, h3, h4, _⟩ := hC η (fun x => x.elim0)
  have hb : ∀ t : ℝ, t ≤ C * U.mx (U.ZjH σ d η (fun x => x.elim0)) ^ n → t ≤ |C| * (max R 0) ^ n := by
    intro t ht
    refine le_trans ht (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C) (pow_nonneg hmx0 n)) ?_)
    exact mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
  apply hη
  rw [Metric.mem_closedBall, dist_zero_right]
  refine norm_prod_le_iff.mpr ⟨norm_prod_le_iff.mpr ⟨hb _ h1, hb _ h2⟩, norm_prod_le_iff.mpr ⟨hb _ h3, hb _ h4⟩⟩

end integ

theorem hMat_inj {m : ℕ} (σ σ' : Equiv.Perm (Fin m)) (d d' : Fin m → ℂ) (hd' : ∀ i, d' i ≠ 0)
    (h : U.hMat σ d = U.hMat σ' d') : σ = σ' ∧ d = d' := by
  have happ : ∀ (τ : Equiv.Perm (Fin m)) (e : Fin m → ℂ) (a b : Fin m),
      U.hMat τ e a b = if τ a = b then e b else 0 := by
    intro τ e a b
    simp [U.hMat, U.wP, Matrix.mul_diagonal]
  have hσ : σ = σ' := by
    ext a
    have := congrFun (congrFun h a) (σ' a)
    rw [happ, happ, if_pos rfl] at this
    by_contra hne
    rw [if_neg (fun e => hne (congrArg Fin.val e))] at this
    exact hd' _ this.symm
  subst hσ
  refine ⟨rfl, funext fun b => ?_⟩
  have := congrFun (congrFun h (σ.symm b)) b
  simp only [happ, Equiv.apply_symm_apply, if_true] at this
  exact this

end Formalism.FourierDecayAlt.P.PBJ.Fub

namespace Formalism.FourierDecayAlt.P.PBJ

open Formalism.FourierDecayAlt.P.PBJ.Fub

theorem fubini_head_last_part : FubTop := by
  intro β p s σ d σh dh σb db V _ _ _ Ψ hdh hdb hM hΨ
  have hd : ∀ i, dQ dh db i ≠ 0 := by
    intro i
    induction i using Fin.addCases with
    | left j => simp only [dQ, Fin.addCases_left]; exact hdh j
    | right j => simp only [dQ, Fin.addCases_right]; exact hdb j
  obtain ⟨rfl, rfl⟩ := hMat_inj σ (sigQ σh σb) d (dQ dh db) hd (hM.trans (hMat_sigQ σh σb dh db).symm)
  exact fub_core β σh dh σb db Ψ (integrable_cls β _ _ hd Ψ hΨ)

end Formalism.FourierDecayAlt.P.PBJ
