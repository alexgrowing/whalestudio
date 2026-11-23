import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff

noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands

namespace DiscreteGroups.sglob.DzRed

variable {R : Type} [CommRing R]

theorem val_longElt (n : ℕ) (i j : Fin n) :
    (longElt n R : Matrix (Fin n) (Fin n) R) i j = if j = i.rev then 1 else 0 := rfl

theorem longElt_inv (n : ℕ) : (longElt n R)⁻¹ = longElt n R := Units.ext rfl

theorem val_invT (a : ℕ) (g : GL (Fin a) R) :
    ((GlobalTheory.CuspRep.invT a R g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) = ((g⁻¹ : GL (Fin a) R) : Matrix _ _ R)ᵀ :=
  rfl

theorem mul_longElt_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    (A * (longElt n R : Matrix (Fin n) (Fin n) R)) i j = A i j.rev := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j.rev]
  · simp [val_longElt]
  · intro b _ hb
    have : j ≠ b.rev := fun h => hb (by rw [h, Fin.rev_rev])
    simp [val_longElt, this]
  · simp

theorem longElt_mul_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    ((longElt n R : Matrix (Fin n) (Fin n) R) * A) i j = A i.rev j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp [val_longElt]
  · intro b _ hb
    simp [val_longElt, hb]
  · simp

theorem val_conjT {n : ℕ} (a : GL (Fin n) R) (i j : Fin n) :
    ((longElt n R * GlobalTheory.CuspRep.invT n R a * (longElt n R)⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((a⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) j.rev i.rev := by
  rw [longElt_inv, Units.val_mul, Units.val_mul, mul_longElt_apply, longElt_mul_apply, val_invT,
    Matrix.transpose_apply]

theorem conjT_mem {n : ℕ} {a : GL (Fin n) R} (ha : a ∈ unipB R (Fin n)) :
    longElt n R * GlobalTheory.CuspRep.invT n R a * (longElt n R)⁻¹ ∈ unipB R (Fin n) := by
  have h := (mem_unipB R).1 (inv_mem ha)
  refine (mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [val_conjT]
    exact h.1 _ _ (Fin.rev_lt_rev.2 hji)
  · rw [val_conjT]
    exact h.2 _

theorem superDiag_conjT {n : ℕ} (a : GL (Fin n) R) :
    superDiag (longElt n R * GlobalTheory.CuspRep.invT n R a * (longElt n R)⁻¹) = superDiag a⁻¹ := by
  simp only [superDiag, val_conjT, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun j => ?_)
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun i => ?_)
  have := i.isLt
  have := j.isLt
  simp only [Fin.revPerm_apply, Fin.val_rev]
  split_ifs with h1 h2 <;> first | rfl | (exfalso; omega)

theorem val_corner {m : ℕ} (g : GL (Fin m) R) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) =
      Matrix.reindex (stdSum (rfl : m + 1 = m + 1)) (stdSum (rfl : m + 1 = m + 1))
        (fromBlocks (g : Matrix (Fin m) (Fin m) R) 0 0 ((1 : GL (Fin 1) R) : Matrix (Fin 1) (Fin 1) R)) :=
  val_emb₂ (R := R) _ _

theorem corner_cs_cs {m : ℕ} (g : GL (Fin m) R) (i j : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i.castSucc j.castSucc = (g : Matrix (Fin m) (Fin m) R) i j := by
  simp [val_corner, stdSum]

theorem corner_cs_last {m : ℕ} (g : GL (Fin m) R) (i : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) i.castSucc (Fin.last m) = 0 := by
  simp [val_corner, stdSum]

theorem corner_last_cs {m : ℕ} (g : GL (Fin m) R) (j : Fin m) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) j.castSucc = 0 := by
  simp [val_corner, stdSum]

theorem corner_last_last {m : ℕ} (g : GL (Fin m) R) :
    (corner g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) (Fin.last m) = 1 := by
  simp [val_corner, stdSum]

theorem corner_mul {m : ℕ} (x y : GL (Fin m) R) : corner (x * y) = corner x * corner y := by
  simp only [corner, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem corner_one {m : ℕ} : corner (1 : GL (Fin m) R) = 1 := by
  simp only [corner, Prod.mk_one_one, map_one]

theorem corner_inv {m : ℕ} (x : GL (Fin m) R) : corner x⁻¹ = (corner x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← corner_mul, inv_mul_cancel, corner_one])

theorem corner_mem {m : ℕ} {b : GL (Fin m) R} (hb : b ∈ unipB R (Fin m)) : corner b ∈ unipB R (Fin (m + 1)) := by
  have h := (mem_unipB R).1 hb
  refine (mem_unipB R).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd hji (lt_irrefl _)
      | cast j => exact corner_last_cs b j
    | cast i =>
      induction j using Fin.lastCases with
      | last => exact absurd hji (not_lt.2 (Fin.le_last _))
      | cast j => rw [corner_cs_cs]; exact h.1 i j (Fin.castSucc_lt_castSucc_iff.1 hji)
  · induction i using Fin.lastCases with
    | last => exact corner_last_last b
    | cast i => rw [corner_cs_cs]; exact h.2 i

theorem superDiag_corner {m : ℕ} (b : GL (Fin m) R) : superDiag (corner b) = superDiag b := by
  simp [superDiag, Finset.sum_filter, Fin.sum_univ_castSucc, corner_cs_cs, corner_cs_last, corner_last_cs]

theorem tilde_mul {n : ℕ} (x y : GL (Fin n) R) : tilde (x * y) = tilde x * GlobalTheory.CuspRep.invT n R y := by
  simp only [tilde, map_mul, mul_assoc]

theorem tilde_mul_left {n : ℕ} (u x : GL (Fin n) R) :
    tilde (u * x) = (longElt n R * GlobalTheory.CuspRep.invT n R u * (longElt n R)⁻¹) * tilde x := by
  simp only [tilde, map_mul, mul_assoc, inv_mul_cancel_left]

theorem tilde_corner_unip {m : ℕ} {u : GL (Fin m) R} (hu : u ∈ unipB R (Fin m)) (x : GL (Fin m) R) :
    ∃ u₁ ∈ unipB R (Fin (m + 1)), ∃ u₂ ∈ unipB R (Fin m),
      tilde (corner (u * x)) = u₁ * tilde (corner x) ∧ tilde (u * x) = u₂ * tilde x ∧
        superDiag u₁ = superDiag u₂ := by
  refine ⟨_, conjT_mem (corner_mem hu), _, conjT_mem hu, ?_, tilde_mul_left u x, ?_⟩
  · rw [corner_mul, tilde_mul_left]
  · rw [superDiag_conjT, superDiag_conjT, ← corner_inv, superDiag_corner]

theorem val_map {S : Type} [CommRing S] (f : R →+* S) {n : ℕ} (g : GL (Fin n) R) :
    (GeneralLinearGroup.map f g : Matrix (Fin n) (Fin n) S) = (g : Matrix (Fin n) (Fin n) R).map f := rfl

theorem map_longElt {S : Type} [CommRing S] (f : R →+* S) (n : ℕ) :
    GeneralLinearGroup.map f (longElt n R) = longElt n S := by
  ext i j
  simp [val_longElt, apply_ite f]

theorem map_invT {S : Type} [CommRing S] (f : R →+* S) {n : ℕ} (x : GL (Fin n) R) :
    GeneralLinearGroup.map f (GlobalTheory.CuspRep.invT n R x) = GlobalTheory.CuspRep.invT n S (GeneralLinearGroup.map f x) := by
  ext i j
  rw [val_map, val_invT, val_invT, show (GeneralLinearGroup.map f x)⁻¹ = GeneralLinearGroup.map f x⁻¹ from
    (map_inv _ x).symm, val_map]
  rfl

theorem map_tilde {S : Type} [CommRing S] (f : R →+* S) {n : ℕ} (x : GL (Fin n) R) :
    GeneralLinearGroup.map f (tilde x) = tilde (GeneralLinearGroup.map f x) := by
  simp only [tilde, map_mul, map_longElt, map_invT]

theorem map_corner {S : Type} [CommRing S] (f : R →+* S) {m : ℕ} (x : GL (Fin m) R) :
    GeneralLinearGroup.map f (corner x) = corner (GeneralLinearGroup.map f x) := by
  ext i j
  rw [val_map, Matrix.map_apply]
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [corner_last_last]
    | cast j => simp [corner_last_cs]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [corner_cs_last]
    | cast j => simp [corner_cs_cs]

end DiscreteGroups.sglob.DzRed
