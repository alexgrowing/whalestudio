import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGVol
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHLie
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHGlue
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstBHDim
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselFrame

noncomputable section

open MeasureTheory Filter Topology Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def pW (k r : ℕ) (c : Fin k) : Fin (2 * r + k + 1) := ⟨r + c.val, by omega⟩

theorem pW_inj : Function.Injective (pW k r) := fun a b h => by
  apply Fin.ext
  have := congrArg Fin.val h
  simp only [pW, Fin.val_mk] at this
  omega

def Ew (k r : ℕ) : Matrix (Fin (2 * r + k + 1)) (Fin k) ℂ := fun i c => if i = pW k r c then 1 else 0

theorem EwT_Ew : (Ew k r)ᵀ * Ew k r = 1 := by
  ext c d
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Ew, Matrix.one_apply]
  rw [Finset.sum_eq_single (pW k r c)]
  · simp [pW_inj.eq_iff]
  · intro b _ hb
    simp [hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem Ew_conjT : (Ew k r)ᴴ = (Ew k r)ᵀ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Ew]
  split_ifs <;> simp

def iota (A : Matrix (Fin k) (Fin k) ℂ) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  1 - Ew k r * (Ew k r)ᵀ + Ew k r * A * (Ew k r)ᵀ

theorem iota_mul (A B : Matrix (Fin k) (Fin k) ℂ) : iota (r := r) (A * B) = iota (r := r) A * iota (r := r) B := by
  have h := EwT_Ew (k := k) (r := r)
  have h1 : ∀ X : Matrix (Fin k) (Fin k) ℂ, (Ew k r)ᵀ * (Ew k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  have h2 : ∀ X : Matrix (Fin k) (Fin (2 * r + k + 1)) ℂ, (Ew k r)ᵀ * (Ew k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  simp only [iota, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h1, h2]
  abel

theorem iota_one : iota (k := k) (r := r) 1 = 1 := by
  simp [iota]

theorem iota_conjT (A : Matrix (Fin k) (Fin k) ℂ) : (iota (r := r) A)ᴴ = iota (r := r) Aᴴ := by
  have h2 : ((Ew k r)ᵀ)ᴴ = Ew k r := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Ew]
    split_ifs <;> simp
  simp only [iota, Matrix.conjTranspose_add, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_mul, Ew_conjT, h2, Matrix.mul_assoc]

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem tau_pW (c : Fin k) : tau k r (pW k r c) = pW k r c := by
  have := c.isLt
  have hv : (pW k r c).val = r + c.val := rfl
  apply Fin.ext
  show (if (pW k r c).val < r ∨ r + k < (pW k r c).val then 2 * r + k - (pW k r c).val
    else (pW k r c).val) = (pW k r c).val
  rw [if_neg (by rw [hv]; omega)]

theorem sgn_pW (c : Fin k) : sgn k r (pW k r c) = 1 := by
  have := c.isLt
  have hv : (pW k r c).val = r + c.val := rfl
  show (if (pW k r c).val = r + k then (-1 : ℂ) else 1) = 1
  rw [if_neg (by rw [hv]; omega)]

private lemma hpk_apply_of_outer_index (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = tau k r i then sgn k r i else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, tau, sgn, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega | norm_num

theorem hpk_mul_apply' {X : Type*} (A : Matrix (Fin (2 * r + k + 1)) X ℂ) (i : Fin (2 * r + k + 1)) (j : X) :
    (Hpk k r * A) i j = sgn k r i * A (tau k r i) j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (tau k r i)]
  · rw [hpk_apply_of_outer_index, if_pos rfl]
  · intro b _ hb
    rw [hpk_apply_of_outer_index, if_neg hb, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem hpk_Ew : Hpk k r * Ew k r = Ew k r := by
  ext i c
  rw [hpk_mul_apply']
  have hi := i.isLt
  have hc := c.isLt
  simp only [Ew, sgn, tau, pW, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | omega | (simp; done) | norm_num

theorem EwT_hpk : (Ew k r)ᵀ * Hpk k r = (Ew k r)ᵀ := by
  have h := congrArg Matrix.conjTranspose (hpk_Ew (k := k) (r := r))
  rw [Matrix.conjTranspose_mul, (hpkFacts k r).1, Ew_conjT] at h
  exact h

theorem EwT_bvec (j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) : (Ew k r)ᵀ *ᵥ bvec j = 0 := by
  ext c
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Ew, bvec, Pi.zero_apply]
  apply Finset.sum_eq_zero
  intro i _
  split_ifs with h
  · subst h
    rw [Pi.single_apply, if_neg (hj c).symm, mul_zero]
  · rw [zero_mul]

theorem iota_fix (A : Matrix (Fin k) (Fin k) ℂ) (j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) :
    iota (r := r) A *ᵥ bvec j = bvec j := by
  simp only [iota, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
    EwT_bvec j hj, Matrix.mulVec_zero, sub_zero, add_zero]

private lemma hpk_mul_iota_comm (A : Matrix (Fin k) (Fin k) ℂ) :
    Hpk k r * iota (r := r) A = iota (r := r) A * Hpk k r := by
  simp only [iota, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, ← Matrix.mul_assoc, hpk_Ew]
  simp only [Matrix.mul_assoc, EwT_hpk]

theorem iota_UH {A : Matrix (Fin k) (Fin k) ℂ} (hA : Aᴴ * A = 1) : iota (r := r) A ∈ UH (Hpk k r) := by
  show (iota (r := r) A)ᴴ * Hpk k r * iota (r := r) A = Hpk k r
  rw [Matrix.mul_assoc, hpk_mul_iota_comm, ← Matrix.mul_assoc, iota_conjT, ← iota_mul, hA, iota_one, Matrix.one_mul]

def wLastV (k r : ℕ) : Fin (2 * r + k + 1) → ℂ := bvec (wI k r (Fin.last k))

theorem iota_mem {A : Matrix (Fin k) (Fin k) ℂ} (hA : Aᴴ * A = 1) : iota (r := r) A ∈ UWset k r (wLastV k r) := by
  have hl := (Fin.last k).isLt
  refine ⟨iota_UH hA, fun a => ⟨?_, ?_⟩, ?_⟩
  · have ha := a.isLt
    refine iota_fix A _ (fun c h => ?_)
    have hc := c.isLt
    have := congrArg Fin.val h
    simp only [eI, pW, Fin.val_mk] at this
    omega
  · have ha := a.isLt
    refine iota_fix A _ (fun c h => ?_)
    have hc := c.isLt
    have := congrArg Fin.val h
    simp only [esI, pW, Fin.val_mk] at this
    omega
  · refine iota_fix A (wI k r (Fin.last k)) (fun c h => ?_)
    have hc := c.isLt
    have := congrArg Fin.val h
    simp only [wI, pW, Fin.val_mk, Fin.val_last] at this
    omega

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

variable {k r : ℕ}

theorem Ew_pW (c b : Fin k) : Ew k r (pW k r c) b = if c = b then 1 else 0 := by
  simp only [Ew, pW_inj.eq_iff]

theorem wEmbeddingConj_apply_wPositions (M : Matrix (Fin k) (Fin k) ℂ) (c d : Fin k) :
    (Ew k r * M * (Ew k r)ᵀ) (pW k r c) (pW k r d) = M c d := by
  simp [Matrix.mul_apply, Ew_pW]

theorem EMET_out_row (M : Matrix (Fin k) (Fin k) ℂ) (i j : Fin (2 * r + k + 1)) (hi : ∀ c, i ≠ pW k r c) :
    (Ew k r * M * (Ew k r)ᵀ) i j = 0 := by
  have h0 : ∀ x, Ew k r i x = 0 := fun x => if_neg (hi x)
  simp [Matrix.mul_apply, h0]

theorem EMET_out_col (M : Matrix (Fin k) (Fin k) ℂ) (i j : Fin (2 * r + k + 1)) (hj : ∀ c, j ≠ pW k r c) :
    (Ew k r * M * (Ew k r)ᵀ) i j = 0 := by
  have h0 : ∀ x, Ew k r j x = 0 := fun x => if_neg (hj x)
  simp [Matrix.mul_apply, Matrix.transpose_apply, h0]

theorem nonW (i : Fin (2 * r + k + 1)) (hi : ∀ c, i ≠ pW k r c) :
    (∃ a : Fin r, i = eI k r a) ∨ (∃ a : Fin r, i = esI k r a) ∨ i = wI k r (Fin.last k) := by
  have hl := i.isLt
  by_cases h1 : i.val < r
  · left
    exact ⟨⟨i.val, h1⟩, Fin.ext (by simp only [eI, Fin.val_mk])⟩
  · by_cases h2 : r + k < i.val
    · right; left
      refine ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext ?_⟩
      simp only [esI, Fin.val_mk]
      omega
    · by_cases h3 : i.val = r + k
      · right; right
        exact Fin.ext (by simp only [wI, Fin.val_mk, Fin.val_last]; omega)
      · exfalso
        exact hi ⟨i.val - r, by omega⟩ (Fin.ext (by simp only [pW, Fin.val_mk]; omega))

theorem tau_nonW (i : Fin (2 * r + k + 1)) (hi : ∀ c, i ≠ pW k r c) : ∀ c, tau k r i ≠ pW k r c := by
  intro c h
  have hc := c.isLt
  have hl := i.isLt
  have hv := congrArg Fin.val h
  simp only [tau, pW, Fin.val_mk] at hv
  split_ifs at hv with h1
  · omega
  · exact hi c (Fin.ext (by simp only [pW, Fin.val_mk]; omega))

private lemma Ew_transpose_mul_iota (A : Matrix (Fin k) (Fin k) ℂ) :
    (Ew k r)ᵀ * iota (r := r) A * Ew k r = A := by
  have h := EwT_Ew (k := k) (r := r)
  have h' : ∀ X : Matrix (Fin k) (Fin k) ℂ, (Ew k r)ᵀ * (Ew k r * X) = X := fun X => by
    rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  simp only [iota, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, h, h', sub_self, zero_add]

theorem iota_surj {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hg : g ∈ UWset k r (wLastV k r)) :
    g = iota (r := r) ((Ew k r)ᵀ * g * Ew k r) ∧
      ((Ew k r)ᵀ * g * Ew k r)ᴴ * ((Ew k r)ᵀ * g * Ew k r) = 1 := by
  obtain ⟨hU, hfix, hw⟩ := hg
  have hU' : gᴴ * Hpk k r * g = Hpk k r := hU
  have hH2 : Hpk k r * Hpk k r = 1 := (hpkFacts k r).2.1
  have hcol : ∀ j : Fin (2 * r + k + 1), (∀ c, j ≠ pW k r c) → ∀ i, g i j = if i = j then 1 else 0 := by
    intro j hj i
    have hv : g *ᵥ bvec j = bvec j := by
      rcases nonW j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
      · exact (hfix a).1
      · exact (hfix a).2
      · exact hw
    have := congrFun hv i
    simpa [bvec, Matrix.mulVec, dotProduct, Pi.single_apply] using this
  have hEEcol : ∀ l d, (Ew k r * (Ew k r)ᵀ) l (pW k r d) = if l = pW k r d then 1 else 0 := by
    intro l d
    rw [Matrix.mul_apply, Finset.sum_eq_single d]
    · rw [Matrix.transpose_apply, Ew_pW, if_pos rfl, mul_one]
      rfl
    · intro b _ hb
      rw [Matrix.transpose_apply, Ew_pW, if_neg (Ne.symm hb), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hgQ : g * (1 - Ew k r * (Ew k r)ᵀ) = 1 - Ew k r * (Ew k r)ᵀ := by
    ext i j
    by_cases hj : ∀ c, j ≠ pW k r c
    · have h0 : ∀ l, (Ew k r * (Ew k r)ᵀ) l j = 0 := fun l => by
        have := EMET_out_col (k := k) (r := r) 1 l j hj
        rwa [Matrix.mul_one] at this
      have hz : (g * (Ew k r * (Ew k r)ᵀ)) i j = 0 := by
        rw [Matrix.mul_apply]
        exact Finset.sum_eq_zero (fun l _ => by rw [h0, mul_zero])
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]
      rw [hz, h0 i, hcol j hj i, Matrix.one_apply]
    · push_neg at hj
      obtain ⟨d, rfl⟩ := hj
      have hz : (g * (Ew k r * (Ew k r)ᵀ)) i (pW k r d) = g i (pW k r d) := by
        rw [Matrix.mul_apply, Finset.sum_eq_single (pW k r d)]
        · rw [hEEcol, if_pos rfl, mul_one]
        · intro b _ hb
          rw [hEEcol, if_neg hb, mul_zero]
        · intro h
          exact absurd (Finset.mem_univ _) h
      simp only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_apply]
      rw [hz, hEEcol, Matrix.one_apply]
      simp only [sub_self]
  have hQ0 : iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) = 1 - Ew k r * (Ew k r)ᵀ := by
    simp [iota]
  have hgQ' : g * iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) =
      iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) := by
    rw [hQ0]
    exact hgQ
  have h1 : gᴴ * iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) * Hpk k r =
      iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) * Hpk k r := by
    calc gᴴ * iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) * Hpk k r
        = gᴴ * (Hpk k r * iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ)) := by
          rw [Matrix.mul_assoc, hpk_mul_iota_comm]
      _ = gᴴ * Hpk k r * (g * iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ)) := by
          rw [hgQ', Matrix.mul_assoc]
      _ = Hpk k r * iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) := by
          rw [← Matrix.mul_assoc, hU']
      _ = iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) * Hpk k r := hpk_mul_iota_comm _
  have h2 : gᴴ * iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) =
      iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) := by
    have := congrArg (· * Hpk k r) h1
    simpa only [Matrix.mul_assoc, hH2, Matrix.mul_one] using this
  have hQg : iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) * g =
      iota (r := r) (0 : Matrix (Fin k) (Fin k) ℂ) := by
    have := congrArg Matrix.conjTranspose h2
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, iota_conjT,
      Matrix.conjTranspose_zero] at this
  rw [hQ0] at hQg
  set P := Ew k r * (Ew k r)ᵀ with hP
  have e1 : g * P = g - 1 + P := by
    rw [Matrix.mul_sub, Matrix.mul_one] at hgQ
    calc g * P = g - (g - g * P) := (sub_sub_cancel _ _).symm
      _ = g - (1 - P) := by rw [hgQ]
      _ = g - 1 + P := by abel
  have e2 : P * g = g - 1 + P := by
    rw [Matrix.sub_mul, Matrix.one_mul] at hQg
    calc P * g = g - (g - P * g) := (sub_sub_cancel _ _).symm
      _ = g - (1 - P) := by rw [hQg]
      _ = g - 1 + P := by abel
  have e3 : P * P = P := by
    rw [hP, Matrix.mul_assoc, ← Matrix.mul_assoc (Ew k r)ᵀ, EwT_Ew, Matrix.one_mul]
  have e4 : P * g * P = g - 1 + P := by
    rw [Matrix.mul_assoc, e1, Matrix.mul_add, Matrix.mul_sub, Matrix.mul_one, e2, e3]
    abel
  have hgi : g = iota (r := r) ((Ew k r)ᵀ * g * Ew k r) := by
    have e5 : Ew k r * ((Ew k r)ᵀ * g * Ew k r) * (Ew k r)ᵀ = P * g * P := by
      rw [hP]
      simp only [Matrix.mul_assoc]
    show g = 1 - P + Ew k r * ((Ew k r)ᵀ * g * Ew k r) * (Ew k r)ᵀ
    rw [e5, e4]
    abel
  refine ⟨hgi, ?_⟩
  set M := (Ew k r)ᵀ * g * Ew k r with hM
  have hU2 : (iota (r := r) M)ᴴ * Hpk k r * iota (r := r) M = Hpk k r := by
    rw [← hgi]
    exact hU'
  have h3 : iota (r := r) (Mᴴ * M) * Hpk k r = Hpk k r := by
    rw [iota_mul, ← iota_conjT, Matrix.mul_assoc, ← hpk_mul_iota_comm, ← Matrix.mul_assoc, hU2]
  have h4 : iota (r := r) (Mᴴ * M) = 1 := by
    have := congrArg (· * Hpk k r) h3
    simpa only [Matrix.mul_assoc, hH2, Matrix.mul_one] using this
  calc Mᴴ * M = (Ew k r)ᵀ * iota (r := r) (Mᴴ * M) * Ew k r := (Ew_transpose_mul_iota _).symm
    _ = 1 := by rw [h4, Matrix.mul_one, EwT_Ew]

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.MainNotions.S

variable {k r : ℕ}

def cE (k r : ℕ) : Matrix (Fin k) (Fin k) ℂ →ₗ[ℝ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ where
  toFun Y := Ew k r * Y * (Ew k r)ᵀ
  map_add' X Y := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c X := by
    rw [RingHom.id_apply, ← Complex.coe_smul, ← Complex.coe_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem cE_apply (Y : Matrix (Fin k) (Fin k) ℂ) : cE k r Y = Ew k r * Y * (Ew k r)ᵀ := rfl

theorem sum_eq_sum_wPositions (f : Fin (2 * r + k + 1) → ℝ) (hf : ∀ i, (∀ c, i ≠ pW k r c) → f i = 0) :
    ∑ i, f i = ∑ c, f (pW k r c) := by
  symm
  rw [show (∑ c, f (pW k r c)) = ∑ i ∈ Finset.univ.map ⟨pW k r, pW_inj⟩, f i from
    (Finset.sum_map Finset.univ ⟨pW k r, pW_inj⟩ f).symm]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  apply hf
  intro c hc
  exact hi (Finset.mem_map.mpr ⟨c, Finset.mem_univ _, hc.symm⟩)

theorem norm_cE (Y : Matrix (Fin k) (Fin k) ℂ) : ‖Formalism.MainNotions.BridgeCSB.RL (cE k r Y)‖ = ‖RLk Y‖ := by
  have h1 := Formalism.L2.SG.Pf.BH.Sw.RL_sq (k := k) (r := r) (cE k r Y)
  have h2 := RLk_sq Y
  have key : ∑ i, ∑ j, ‖(cE k r Y) i j‖ ^ 2 = ∑ c, ∑ d, ‖Y c d‖ ^ 2 := by
    rw [sum_eq_sum_wPositions (fun i => ∑ j, ‖(cE k r Y) i j‖ ^ 2) (fun i hi => Finset.sum_eq_zero (fun j _ => by
      rw [cE_apply, EMET_out_row _ _ _ hi, norm_zero]; ring))]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [sum_eq_sum_wPositions (fun j => ‖(cE k r Y) (pW k r c) j‖ ^ 2) (fun j hj => by
      rw [cE_apply, EMET_out_col _ _ _ hj, norm_zero]; ring)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [cE_apply, wEmbeddingConj_apply_wPositions]
  have h3 : ‖Formalism.MainNotions.BridgeCSB.RL (cE k r Y)‖ ^ 2 = ‖RLk Y‖ ^ 2 := by
    rw [h1, h2, key]
  rw [← Real.sqrt_sq (norm_nonneg (Formalism.MainNotions.BridgeCSB.RL (cE k r Y))),
    ← Real.sqrt_sq (norm_nonneg (RLk Y)), h3]

theorem EwT_conjT : ((Ew k r)ᵀ)ᴴ = Ew k r := by
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply, Ew]
  split_ifs <;> simp

theorem cE_conjT (Y : Matrix (Fin k) (Fin k) ℂ) : (cE k r Y)ᴴ = cE k r Yᴴ := by
  rw [cE_apply, cE_apply]
  simp only [Matrix.conjTranspose_mul, Ew_conjT, EwT_conjT, Matrix.mul_assoc]

theorem adjH_cE' (Y : Matrix (Fin k) (Fin k) ℂ) : Formalism.MainNotions.BridgeCSB.adjH (cE k r Y) = cE k r Yᴴ := by
  show Hpk k r * (cE k r Y)ᴴ * Hpk k r = cE k r Yᴴ
  rw [cE_conjT, cE_apply]
  simp only [← Matrix.mul_assoc, hpk_Ew]
  simp only [Matrix.mul_assoc, EwT_hpk]

theorem adjH_cE {Y : Matrix (Fin k) (Fin k) ℂ} (hY : Yᴴ = -Y) :
    Hpk k r * (cE k r Y)ᴴ * Hpk k r + cE k r Y = 0 := by
  have h := adjH_cE' (k := k) (r := r) Y
  show Formalism.MainNotions.BridgeCSB.adjH (cE k r Y) + cE k r Y = 0
  rw [h, hY, map_neg, neg_add_cancel]

theorem lieOf_S : lieOf (UWset k r (wLastV k r)) = cE k r '' (skewH k : Set (Matrix (Fin k) (Fin k) ℂ)) := by
  ext X
  constructor
  · intro hX
    have hadj := Formalism.L2.SG.Pf.BH.adj_of_lie fun t => (hX t).1
    have hadj' : Formalism.MainNotions.BridgeCSB.adjH X = -X := eq_neg_of_add_eq_zero_left hadj
    have hkill : ∀ j, (∀ c, j ≠ pW k r c) → X *ᵥ bvec j = 0 := by
      intro j hj
      rcases nonW j hj with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
      · exact Formalism.L2.SG.Pf.BH.col_zero _ fun t => ((hX t).2.1 a).1
      · exact Formalism.L2.SG.Pf.BH.col_zero _ fun t => ((hX t).2.1 a).2
      · exact Formalism.L2.SG.Pf.BH.col_zero _ fun t => (hX t).2.2
    have hcol : ∀ i j, (∀ c, j ≠ pW k r c) → X i j = 0 := by
      intro i j hj
      have := congrFun (hkill j hj) i
      rwa [Formalism.L2.SG.Pf.BH.Sw.mulVec_bvec] at this
    have hrow : ∀ i j, (∀ c, i ≠ pW k r c) → X i j = 0 := by
      intro i j hi
      have e : X i j = -Formalism.MainNotions.BridgeCSB.adjH X i j := by rw [hadj', Matrix.neg_apply, neg_neg]
      rw [e, Formalism.MainNotions.BridgeCSB.adjH_apply, hcol _ _ (tau_nonW i hi), star_zero]; simp
    set Y := (Ew k r)ᵀ * X * Ew k r with hY
    have hYe : ∀ c d, Y c d = X (pW k r c) (pW k r d) := by
      intro c d
      rw [hY, Matrix.mul_apply, Finset.sum_eq_single (pW k r d)]
      · rw [Matrix.mul_apply, Finset.sum_eq_single (pW k r c)]
        · rw [Matrix.transpose_apply, Ew_pW, if_pos rfl, one_mul, Ew_pW, if_pos rfl, mul_one]
        · intro b _ hb; rw [Matrix.transpose_apply, Ew, if_neg hb, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · intro b _ hb; rw [Ew, if_neg hb, mul_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hXY : cE k r Y = X := by
      ext i j
      rw [cE_apply]
      by_cases hi : ∃ c, i = pW k r c
      · obtain ⟨c, rfl⟩ := hi
        by_cases hj : ∃ d, j = pW k r d
        · obtain ⟨d, rfl⟩ := hj
          rw [wEmbeddingConj_apply_wPositions, hYe]
        · push_neg at hj
          rw [EMET_out_col _ _ _ hj, hcol _ _ hj]
      · push_neg at hi
        rw [EMET_out_row _ _ _ hi, hrow _ _ hi]
    refine ⟨Y, ?_, hXY⟩
    show Yᴴ = -Y
    ext c d
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply, hYe, hYe]
    have := congrFun (congrFun hadj' (pW k r c)) (pW k r d)
    rw [Formalism.MainNotions.BridgeCSB.adjH_apply, tau_pW, tau_pW, sgn_pW, sgn_pW, one_mul, mul_one, Matrix.neg_apply] at this
    exact this
  · rintro ⟨Y, hY, rfl⟩ t
    have hsk : ((t : ℂ) • Y)ᴴ = -((t : ℂ) • Y) := by
      have hY' : Yᴴ = -Y := hY
      rw [Matrix.conjTranspose_smul, hY', Complex.star_def, Complex.conj_ofReal, smul_neg]
    have hX : (t : ℂ) • cE k r Y = cE k r ((t : ℂ) • Y) := by
      rw [cE_apply, cE_apply, Matrix.mul_smul, Matrix.smul_mul]
    rw [hX]
    refine ⟨Formalism.L2.SG.Pf.BH.exp_mem_UH (adjH_cE hsk) 1 |> fun h => by simpa using h, fun a => ⟨?_, ?_⟩, ?_⟩
    · exact Formalism.L2.SG.Pf.BH.exp_mulVec_of_zero _ _ (by rw [cE_apply, ← Matrix.mulVec_mulVec,
        EwT_bvec _ (fun c h => by have := congrArg Fin.val h; simp [eI, pW] at this; omega), Matrix.mulVec_zero])
    · exact Formalism.L2.SG.Pf.BH.exp_mulVec_of_zero _ _ (by rw [cE_apply, ← Matrix.mulVec_mulVec,
        EwT_bvec _ (fun c h => by have := congrArg Fin.val h; simp [esI, pW] at this; have := a.isLt; have := c.isLt; omega),
        Matrix.mulVec_zero])
    · exact Formalism.L2.SG.Pf.BH.exp_mulVec_of_zero _ _ (by rw [cE_apply, ← Matrix.mulVec_mulVec, wLastV,
        EwT_bvec _ (fun c h => by have := congrArg Fin.val h; simp [wI, pW] at this; have := c.isLt; omega),
        Matrix.mulVec_zero])

theorem lieE_S : lieE (UWset k r (wLastV k r)) = (skewH k).map (Formalism.MainNotions.BridgeCSB.RL ∘ₗ cE k r) := by
  have hspan : lieE (UWset k r (wLastV k r)) =
      Submodule.span ℝ ((Formalism.MainNotions.BridgeCSB.RL ∘ₗ cE k r) '' (skewH k : Set (Matrix (Fin k) (Fin k) ℂ))) := by
    unfold lieE
    rw [lieOf_S, Set.image_image]
    rfl
  rw [hspan, Submodule.span_image, Submodule.span_eq]

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.MainNotions.S

variable {k r : ℕ}

theorem cE_pow (Y : Matrix (Fin k) (Fin k) ℂ) (m : ℕ) :
    (cE k r Y) ^ m = Ew k r * Y ^ m * (Ew k r)ᵀ + (if m = 0 then 1 - Ew k r * (Ew k r)ᵀ else 0) := by
  induction m with
  | zero => simp [cE_apply]
  | succ m ih =>
    rw [pow_succ, ih, cE_apply, if_neg (Nat.succ_ne_zero m), add_zero]
    have h := EwT_Ew (k := k) (r := r)
    have h1 : ∀ X : Matrix (Fin k) (Fin (2 * r + k + 1)) ℂ, (Ew k r)ᵀ * (Ew k r * X) = X := fun X => by
      rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    split_ifs with hm
    · subst hm
      simp only [zero_add, pow_zero, pow_one, Matrix.mul_one, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul,
        Matrix.mul_assoc, h1]
      abel
    · simp only [add_zero, pow_succ, Matrix.mul_assoc, h1]

theorem exp_cE (Y : Matrix (Fin k) (Fin k) ℂ) : NormedSpace.exp (cE k r Y) = iota (r := r) (NormedSpace.exp Y) := by
  letI : SeminormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin k) (Fin k) ℂ) := Matrix.linftyOpNormedAlgebra
  letI : SeminormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpSemiNormedRing
  letI : NormedRing (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := Matrix.linftyOpNormedAlgebra
  let L0 : Matrix (Fin k) (Fin k) ℂ →ₗ[ℂ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    { toFun := fun M => Ew k r * M * (Ew k r)ᵀ
      map_add' := fun M N => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c M => by rw [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul] }
  let L : Matrix (Fin k) (Fin k) ℂ →L[ℂ] Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
    LinearMap.toContinuousLinearMap L0
  have hL : ∀ M, L M = Ew k r * M * (Ew k r)ᵀ := fun M => rfl
  set Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := 1 - Ew k r * (Ew k r)ᵀ with hQ
  rw [NormedSpace.exp_eq_tsum (𝕂 := ℂ), NormedSpace.exp_eq_tsum (𝕂 := ℂ)]
  have hs := NormedSpace.expSeries_summable' (𝕂 := ℂ) Y
  simp_rw [cE_pow, smul_add]
  have hs1 : Summable fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (Ew k r * Y ^ m * (Ew k r)ᵀ) := by
    have := (L.summable hs)
    simpa [hL, Matrix.mul_smul, Matrix.smul_mul] using this
  have hs2 : Summable fun m : ℕ => ((m.factorial : ℂ)⁻¹) • (if m = 0 then Q else 0) := by
    refine summable_of_ne_finset_zero (s := {0}) fun m hm => ?_
    rw [Finset.mem_singleton] at hm
    rw [if_neg hm, smul_zero]
  rw [hs1.tsum_add hs2]
  have t2 : ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • (if m = 0 then Q else 0) = Q := by
    rw [tsum_eq_single 0]
    · simp
    · intro m hm; rw [if_neg hm, smul_zero]
  have t1 : ∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • (Ew k r * Y ^ m * (Ew k r)ᵀ) =
      Ew k r * (∑' m : ℕ, ((m.factorial : ℂ)⁻¹) • Y ^ m) * (Ew k r)ᵀ := by
    rw [← hL, L.map_tsum hs]
    refine tsum_congr fun m => ?_
    rw [map_smul, hL]
  rw [t1, t2, hQ]
  unfold iota
  abel

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.MainNotions.S

variable {k r : ℕ}

theorem uMat_unitary (g : ↥(Formalism.REAL.UJ (εT k))) : (uMat g)ᴴ * uMat g = 1 := by
  have h : Formalism.REAL.inUJ (εT k) ((g : (Matrix (Fin k) (Fin k) ℂ)ˣ) : Matrix (Fin k) (Fin k) ℂ) := g.2
  have hJ : Formalism.REAL.Jm (εT k) = 1 := by
    simp [Formalism.REAL.Jm]
  unfold Formalism.REAL.inUJ at h
  rw [hJ, Matrix.mul_one] at h
  exact h

def phi (k r : ℕ) (g : ↥(Formalism.REAL.UJ (εT k))) : Mt k r :=
  (iota (r := r) (uMat g) : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)

theorem phi_mem (g : ↥(Formalism.REAL.UJ (εT k))) : Matrix.of (phi k r g) ∈ UWset k r (wLastV k r) := iota_mem (uMat_unitary g)

theorem phi_mul (g h : ↥(Formalism.REAL.UJ (εT k))) :
    phi k r (g * h) = (fun i j => (Matrix.of (phi k r g) * Matrix.of (phi k r h)) i j : Mt k r) := by
  funext i j
  show iota (r := r) (uMat (g * h)) i j = (iota (r := r) (uMat g) * iota (r := r) (uMat h)) i j
  rw [← iota_mul]
  rfl

theorem iota_linv (A : Matrix (Fin k) (Fin k) ℂ) : (Ew k r)ᵀ * iota (r := r) A * Ew k r = A := Ew_transpose_mul_iota A

theorem iota_inj {A B : Matrix (Fin k) (Fin k) ℂ} (h : iota (r := r) A = iota (r := r) B) : A = B := by
  calc A = (Ew k r)ᵀ * iota (r := r) A * Ew k r := (iota_linv A).symm
    _ = B := by rw [h, iota_linv]

theorem cont_phi : Continuous (phi k r) := by
  show Continuous fun g : ↥(Formalism.REAL.UJ (εT k)) =>
    (1 - Ew k r * (Ew k r)ᵀ + Ew k r * uMat g * (Ew k r)ᵀ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
  exact continuous_const.add ((continuous_const.matrix_mul
    (Units.continuous_val.comp continuous_subtype_val)).matrix_mul continuous_const)

theorem phi_surj {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hs : s ∈ UWset k r (wLastV k r)) :
    ∃ g : ↥(Formalism.REAL.UJ (εT k)), Matrix.of (phi k r g) = s := by
  obtain ⟨hs1, hs2⟩ := iota_surj hs
  have hJ : Formalism.REAL.Jm (εT k) = 1 := by
    simp [Formalism.REAL.Jm]
  let u : (Matrix (Fin k) (Fin k) ℂ)ˣ :=
    ⟨(Ew k r)ᵀ * s * Ew k r, ((Ew k r)ᵀ * s * Ew k r)ᴴ, (by first | exact mul_eq_one_comm.mp hs2 | exact Matrix.mul_eq_one_comm.mp hs2 | exact (Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _)).mp hs2), hs2⟩
  have hu : u ∈ Formalism.REAL.UJ (εT k) := by
    show Formalism.REAL.inUJ (εT k) (u : Matrix (Fin k) (Fin k) ℂ)
    unfold Formalism.REAL.inUJ
    rw [hJ, Matrix.mul_one]
    exact hs2
  refine ⟨⟨u, hu⟩, ?_⟩
  show iota (r := r) ((Ew k r)ᵀ * s * Ew k r) = s
  exact hs1.symm

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.MainNotions.S

variable {k r : ℕ}

abbrev SW (k r : ℕ) : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) := UWset k r (wLastV k r)

theorem mem_lieE_S (Y0 : Matrix (Fin k) (Fin k) ℂ) (hY : Y0 ∈ skewH k) :
    Formalism.MainNotions.BridgeCSB.RL (cE k r Y0) ∈ lieE (SW k r) := by
  show Formalism.MainNotions.BridgeCSB.RL (cE k r Y0) ∈ lieE (UWset k r (wLastV k r))
  rw [lieE_S]
  exact Submodule.mem_map_of_mem hY

theorem mem_gLie (Y0 : Matrix (Fin k) (Fin k) ℂ) (hY : Y0 ∈ skewH k) : RLk Y0 ∈ Gauge.gLie (εT k) := by
  rw [gLie_eq]
  exact Submodule.mem_map_of_mem hY

theorem phi_preimage (ρ : ℝ) :
    phi k r ⁻¹' expBall (k := k) (r := r) (SW k r) ρ = Gauge.expSet (εT k) (Metric.ball 0 ρ) := by
  ext g
  simp only [Set.mem_preimage, expBall, Set.mem_image, Gauge.expSet, Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq]
  constructor
  · rintro ⟨Y, hY, hYg⟩
    have hY2 : (Y : EuclideanSpace ℝ _) ∈ (skewH k).map (Formalism.MainNotions.BridgeCSB.RL ∘ₗ cE k r) := by rw [← lieE_S]; exact Y.2
    obtain ⟨Y0, hY0, hYY⟩ := hY2
    have hu : Formalism.MainNotions.S.unrealify (Y : EuclideanSpace ℝ _) = cE k r Y0 := by
      rw [← hYY]; exact Formalism.MainNotions.BridgeCSB.unrealify_RL _
    have hmat : iota (r := r) (NormedSpace.exp Y0) = iota (r := r) (uMat g) := by
      have := congrArg (fun x : Mt k r => (Matrix.of x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)) hYg
      rw [← exp_cE, ← hu]
      exact this
    refine ⟨⟨RLk Y0, mem_gLie Y0 hY0⟩, ?_, ?_⟩
    · show ‖RLk Y0‖ < ρ
      rw [← norm_cE (r := r) Y0]
      have : ‖(Y : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ < ρ := hY
      rwa [← hYY] at this
    · show uMat g = NormedSpace.exp (Formalism.MainNotions.S.unrealify (RLk Y0))
      rw [unrealify_RLk]; exact (iota_inj hmat).symm
  · rintro ⟨Y', hY', hg⟩
    have hY2 : (Y' : EuclideanSpace ℝ _) ∈ (skewH k).map RLk := by rw [← gLie_eq]; exact Y'.2
    obtain ⟨Y0, hY0, hYY⟩ := hY2
    have hg' : uMat g = NormedSpace.exp Y0 := by rw [hg, ← hYY, unrealify_RLk]
    refine ⟨⟨Formalism.MainNotions.BridgeCSB.RL (cE k r Y0), mem_lieE_S Y0 hY0⟩, ?_, ?_⟩
    · show ‖Formalism.MainNotions.BridgeCSB.RL (cE k r Y0)‖ < ρ
      rw [norm_cE, hYY]; exact hY'
    · show (fun i j => NormedSpace.exp (Formalism.MainNotions.S.unrealify (Formalism.MainNotions.BridgeCSB.RL (cE k r Y0))) i j : Mt k r) = phi k r g
      rw [Formalism.MainNotions.BridgeCSB.unrealify_RL, exp_cE]
      unfold phi; rw [hg']

theorem cE_inj : Function.Injective (cE k r) := by
  intro X Y h
  have h0 := EwT_Ew (k := k) (r := r)
  have key : ∀ Z : Matrix (Fin k) (Fin k) ℂ, (Ew k r)ᵀ * cE k r Z * Ew k r = Z := fun Z => by
    rw [cE_apply]
    simp only [Matrix.mul_assoc, h0, Matrix.mul_one]
    rw [← Matrix.mul_assoc, h0, Matrix.one_mul]
  rw [← key X, h, key]

def eqG (k : ℕ) : ↥(skewH k) ≃ₗ[ℝ] ↥(Gauge.gLie (εT k)) :=
  (Submodule.equivMapOfInjective _ RLk_injective (skewH k)).trans (LinearEquiv.ofEq _ _ gLie_eq.symm)

def eqS (k r : ℕ) : ↥(skewH k) ≃ₗ[ℝ] ↥(lieE (SW k r)) :=
  (Submodule.equivMapOfInjective (Formalism.MainNotions.BridgeCSB.RL ∘ₗ cE k r)
    (Formalism.MainNotions.BridgeCSB.RL_injective.comp cE_inj) (skewH k)).trans (LinearEquiv.ofEq _ _ lieE_S.symm)

theorem eqG_apply (Y : ↥(skewH k)) : ((eqG k Y : ↥(Gauge.gLie (εT k))) : EuclideanSpace ℝ (Fin k × Fin k × Bool)) =
    RLk (Y : Matrix (Fin k) (Fin k) ℂ) := rfl
theorem eqS_apply (Y : ↥(skewH k)) :
    ((eqS k r Y : ↥(lieE (SW k r))) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)) =
    Formalism.MainNotions.BridgeCSB.RL (cE k r (Y : Matrix (Fin k) (Fin k) ℂ)) := rfl

def isoT (k r : ℕ) : ↥(Gauge.gLie (εT k)) ≃ₗᵢ[ℝ] ↥(lieE (SW k r)) :=
  { (eqG k).symm.trans (eqS k r) with
    norm_map' := fun y => by
      obtain ⟨Y, rfl⟩ := (eqG k).surjective y
      show ‖(eqS k r ((eqG k).symm (eqG k Y)))‖ = ‖eqG k Y‖
      rw [LinearEquiv.symm_apply_apply]
      show ‖((eqS k r Y : ↥(lieE (SW k r))) : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool))‖ =
        ‖((eqG k Y : ↥(Gauge.gLie (εT k))) : EuclideanSpace ℝ (Fin k × Fin k × Bool))‖
      rw [eqS_apply, eqG_apply, norm_cE] }

theorem vol_ball_eq (ρ : ℝ) : volume (Metric.ball (0 : ↥(lieE (SW k r))) ρ) =
    volume (Metric.ball (0 : ↥(Gauge.gLie (εT k))) ρ) := by
  have hmp := (isoT k r).measurePreserving
  have hpre : (isoT k r) ⁻¹' Metric.ball (0 : ↥(lieE (SW k r))) ρ = Metric.ball (0 : ↥(Gauge.gLie (εT k))) ρ := by
    ext x
    simp only [Set.mem_preimage, Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map]
  rw [← hpre]
  first
    | exact (hmp.measure_preimage measurableSet_ball.nullMeasurableSet).symm
    | exact (hmp.measure_preimage measurableSet_ball).symm

end Formalism.L2.SG.Pf.GV

namespace Formalism.L2.SG.Pf.GV

open Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts Formalism.MainNotions.S

variable {k r : ℕ}

def nu0 (k r : ℕ) : Measure (Mt k r) := (Gauge.muGauge (εT k)).map (phi k r)

instance (k : ℕ) : (Gauge.muGauge (εT k)).IsMulLeftInvariant := by
  unfold Gauge.muGauge; infer_instance

instance (k : ℕ) : IsFiniteMeasure (Gauge.muGauge (εT k)) := by
  unfold Gauge.muGauge
  exact ⟨by rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩

theorem volU_pos (k : ℕ) : 0 < Formalism.MainNotions.S.UnitaryVolumeMass.volU k := by
  unfold Formalism.MainNotions.S.UnitaryVolumeMass.volU
  exact Finset.prod_pos fun i _ => by positivity

theorem gauge_measure_univ : nu0 k r Set.univ = ENNReal.ofReal (Formalism.MainNotions.S.UnitaryVolumeMass.volU k) := by
  rw [nu0, Measure.map_apply cont_phi.measurable MeasurableSet.univ, Set.preimage_univ, (gaugeVolU k).2]

theorem gauge_measure_is_haar : IsHaarOn (SW k r) (nu0 k r) := by
  have c1 : Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => gᴴ * Hpk k r * g :=
    (continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id
  have c2 : ∀ v : Fin (2 * r + k + 1) → ℂ,
      Continuous fun g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ => g *ᵥ v :=
    fun v => continuous_id.matrix_mulVec continuous_const
  have hclosed : IsClosed (SW k r) := by
    have e : SW k r = {g | gᴴ * Hpk k r * g = Hpk k r} ∩
        ((⋂ a : Fin r, ({g | g *ᵥ bvec (eI k r a) = bvec (eI k r a)} ∩
          {g | g *ᵥ bvec (esI k r a) = bvec (esI k r a)})) ∩ {g | g *ᵥ wLastV k r = wLastV k r}) := by
      ext g
      simp only [SW, UWset, UH, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
    rw [e]
    exact (isClosed_eq c1 continuous_const).inter ((isClosed_iInter fun a =>
      (isClosed_eq (c2 _) continuous_const).inter (isClosed_eq (c2 _) continuous_const)).inter
      (isClosed_eq (c2 _) continuous_const))
  have hmeas : MeasurableSet {x : Mt k r | Matrix.of x ∉ SW k r} := by
    have : IsOpen {x : Mt k r | Matrix.of x ∉ SW k r} := hclosed.isOpen_compl
    exact this.measurableSet
  haveI : IsFiniteMeasure (nu0 k r) := by
    unfold nu0
    infer_instance
  have hpos : 0 < ENNReal.ofReal (Formalism.MainNotions.S.UnitaryVolumeMass.volU k) := ENNReal.ofReal_pos.mpr (volU_pos k)
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · intro h
    have hu := gauge_measure_univ (k := k) (r := r)
    rw [h] at hu
    simp only [Measure.coe_zero, Pi.zero_apply] at hu
    exact hpos.ne' hu.symm
  · rw [nu0, Measure.map_apply cont_phi.measurable hmeas]
    convert measure_empty (μ := Gauge.muGauge (εT k))
    ext g
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact phi_mem g
  · intro s hs
    obtain ⟨g0, rfl⟩ := phi_surj hs
    have hlm : Measurable (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (Matrix.of (phi k r g0))) := by
      have : Continuous (Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (Matrix.of (phi k r g0))) := by
        unfold Formalism.QuantumDeterminants.lmulM
        exact continuous_const.matrix_mul continuous_id
      exact this.measurable
    have hcomp : Formalism.QuantumDeterminants.lmulM (k := k) (r := r) (Matrix.of (phi k r g0)) ∘ phi k r =
        phi k r ∘ (fun g => g0 * g) := by
      funext g
      simp only [Function.comp, Formalism.QuantumDeterminants.lmulM]
      rw [phi_mul]
    have hml : Measurable (fun g : ↥(Formalism.REAL.UJ (εT k)) => g0 * g) := (continuous_mul_left g0).measurable
    rw [nu0, Measure.map_map hlm cont_phi.measurable, hcomp,
      ← Measure.map_map cont_phi.measurable hml]
    congr 1
    first
      | exact MeasureTheory.map_mul_left_eq_self _ g0
      | exact MeasureTheory.Measure.map_mul_left_eq_self _ g0

theorem gauge_measure_ball_ratio : Tendsto (fun ρ : ℝ => (nu0 k r (expBall (k := k) (r := r) (SW k r) ρ)).toReal /
    (volume (Metric.ball (0 : ↥(lieE (SW k r))) ρ)).toReal) (𝓝[>] 0) (𝓝 1) := by
  obtain ⟨hdens, hpos⟩ := (gaugeVolU k).1
  have heq : ∀ ρ : ℝ, 0 < ρ → (nu0 k r (expBall (k := k) (r := r) (SW k r) ρ)).toReal /
      (volume (Metric.ball (0 : ↥(lieE (SW k r))) ρ)).toReal =
      (Gauge.gaugeU (εT k))⁻¹ * Gauge.ratioAt (εT k) ρ := by
    intro ρ hρ
    rw [nu0, Measure.map_apply cont_phi.measurable (Formalism.L2.SG.Pf.BH.measurableSet_expBall _ ρ hρ),
      phi_preimage, vol_ball_eq, Gauge.muGauge, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le), Gauge.ratioAt, mul_div_assoc]
  have hlim : Tendsto (fun ρ => (Gauge.gaugeU (εT k))⁻¹ * Gauge.ratioAt (εT k) ρ) (𝓝[>] 0)
      (𝓝 ((Gauge.gaugeU (εT k))⁻¹ * Gauge.gaugeU (εT k))) := tendsto_const_nhds.mul hdens
  rw [inv_mul_cancel₀ hpos.ne'] at hlim
  exact hlim.congr' (eventually_nhdsWithin_of_forall fun ρ hρ => (heq ρ hρ).symm)

theorem gauge_measure_is_gauge : IsGaugeOn (k := k) (r := r) (SW k r) (nu0 k r) := by
  unfold IsGaugeOn
  exact ⟨gauge_measure_is_haar, gauge_measure_ball_ratio⟩

end Formalism.L2.SG.Pf.GV
