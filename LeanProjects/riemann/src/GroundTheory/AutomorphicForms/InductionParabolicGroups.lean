import Mathlib
import GroundTheory.AutomorphicForms.Iwasawa

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa

variable (F : Type*) [Field F] (n : ℕ) {α : Type*} [LinearOrder α] (β : Fin n → α)

def blockDiagPart (A : Matrix (Fin n) (Fin n) F) : Matrix (Fin n) (Fin n) F :=
  Matrix.of fun i j => if β i = β j then A i j else 0

variable {F n β}

theorem blockDiagPart_apply (A : Matrix (Fin n) (Fin n) F) (i j : Fin n) :
    blockDiagPart F n β A i j = if β i = β j then A i j else 0 := rfl

theorem blockDiagPart_one : blockDiagPart F n β 1 = 1 := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · rw [one_apply_ne fun hij => h (by rw [hij])]

theorem blockDiagPart_mul {A B : Matrix (Fin n) (Fin n) F} (hA : A.BlockTriangular β)
    (hB : B.BlockTriangular β) :
    blockDiagPart F n β (A * B) = blockDiagPart F n β A * blockDiagPart F n β B := by
  ext i j
  simp only [blockDiagPart_apply, mul_apply]
  split_ifs with h
  · refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : β i = β k
    · rw [if_pos hk, if_pos (hk.symm.trans h)]
    · rw [if_neg hk, zero_mul]
      rcases lt_or_gt_of_ne hk with hlt | hlt
      · rw [hB (h ▸ hlt : β j < β k), mul_zero]
      · rw [hA hlt, zero_mul]
  · refine (Finset.sum_eq_zero fun k _ => ?_).symm
    by_cases hk : β i = β k
    · rw [if_neg fun h' => h (hk.trans h'), mul_zero]
    · rw [if_neg hk, zero_mul]

theorem blockDiagPart_of_forall {A : Matrix (Fin n) (Fin n) F}
    (hA : ∀ i j, β i ≠ β j → A i j = 0) : blockDiagPart F n β A = A := by
  ext i j
  rw [blockDiagPart_apply]
  split_ifs with h
  · rfl
  · exact (hA i j h).symm

variable (F n β)

def levi : Subgroup (GL (Fin n) F) :=
  blockUpper F n β ⊓ blockUpper F n (OrderDual.toDual ∘ β)

variable {F n β}

theorem mem_levi {g : GL (Fin n) F} :
    g ∈ levi F n β ↔ ∀ i j, β i ≠ β j → g i j = 0 := by
  constructor
  · rintro ⟨h1, h2⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact h2 (show OrderDual.toDual (β j) < OrderDual.toDual (β i) from h)
    · exact h1 h
  · intro h
    exact ⟨fun i j hij => h i j hij.ne', fun i j hij => h i j
      (show β i < β j from hij).ne⟩

theorem levi_le_blockUpper : levi F n β ≤ blockUpper F n β := inf_le_left

theorem diagGL_mem_levi (d : Fin n → Fˣ) : diagGL F n d ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  have : i ≠ j := fun h => hij (h ▸ rfl)
  simp [diagonal_apply_ne _ this]

def leviProjFun (p : blockUpper F n β) : GL (Fin n) F where
  val := blockDiagPart F n β (p : GL (Fin n) F)
  inv := blockDiagPart F n β ((p⁻¹ : blockUpper F n β) : GL (Fin n) F)
  val_inv := by
    rw [← blockDiagPart_mul p.2 (p⁻¹).2, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]
  inv_val := by
    rw [← blockDiagPart_mul (p⁻¹).2 p.2, ← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel,
      Subgroup.coe_one, Units.val_one, blockDiagPart_one]

theorem leviProjFun_mem (p : blockUpper F n β) : leviProjFun p ∈ levi F n β := by
  rw [mem_levi]
  intro i j hij
  show blockDiagPart F n β _ i j = 0
  rw [blockDiagPart_apply, if_neg hij]

variable (F n β)

def leviProj : blockUpper F n β →* levi F n β where
  toFun p := ⟨leviProjFun p, leviProjFun_mem p⟩
  map_one' := Subtype.ext (Units.ext (by
    show blockDiagPart F n β ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1
    rw [Units.val_one, blockDiagPart_one]))
  map_mul' p q := Subtype.ext (Units.ext (by
    show blockDiagPart F n β (((p * q : blockUpper F n β) : GL (Fin n) F) :
      Matrix (Fin n) (Fin n) F) = blockDiagPart F n β (p : GL (Fin n) F) *
        blockDiagPart F n β (q : GL (Fin n) F)
    rw [Subgroup.coe_mul, Units.val_mul, blockDiagPart_mul p.2 q.2]))

variable {F n β}

theorem leviProj_apply (p : blockUpper F n β) (i j : Fin n) :
    ((leviProj F n β p : levi F n β) : GL (Fin n) F) i j =
      if β i = β j then (p : GL (Fin n) F) i j else 0 := rfl

theorem leviProj_of_mem_levi {m : GL (Fin n) F} (hm : m ∈ levi F n β) :
    leviProj F n β ⟨m, levi_le_blockUpper hm⟩ = ⟨m, hm⟩ :=
  Subtype.ext (Units.ext (blockDiagPart_of_forall (mem_levi.1 hm)))

def leviIncl : levi F n β →* blockUpper F n β :=
  Subgroup.inclusion levi_le_blockUpper

theorem leviProj_leviIncl (m : levi F n β) : leviProj F n β (leviIncl m) = m :=
  leviProj_of_mem_levi m.2

variable (F n β)

def unipotentRadical : Subgroup (GL (Fin n) F) :=
  (leviProj F n β).ker.map (blockUpper F n β).subtype

def oppositeUnipotentRadical : Subgroup (GL (Fin n) F) :=
  unipotentRadical F n (OrderDual.toDual ∘ β)

variable {F n β}

theorem mem_unipotentRadical {g : GL (Fin n) F} :
    g ∈ unipotentRadical F n β ↔ g ∈ blockUpper F n β ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨p.2, fun i j hij => ?_⟩
    have h := congrArg (fun m : levi F n β => ((m : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j)
      ((leviProj F n β).mem_ker.1 hp)
    simp only [leviProj_apply, if_pos hij] at h
    simpa using h
  · rintro ⟨hP, h⟩
    refine ⟨⟨g, hP⟩, (leviProj F n β).mem_ker.2 (Subtype.ext (Units.ext ?_)), rfl⟩
    ext i j
    show (if β i = β j then g i j else 0) = ((1 : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i j
    split_ifs with hij
    · rw [h i j hij, Units.val_one]
    · rw [Units.val_one, one_apply_ne fun e => hij (by rw [e])]

theorem mem_oppositeUnipotentRadical {g : GL (Fin n) F} :
    g ∈ oppositeUnipotentRadical F n β ↔ (∀ i j, β i < β j → g i j = 0) ∧
      ∀ i j, β i = β j → g i j = (1 : Matrix (Fin n) (Fin n) F) i j := by
  rw [oppositeUnipotentRadical, mem_unipotentRadical, mem_blockUpper]
  exact ⟨fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 (show OrderDual.toDual (β j) < OrderDual.toDual (β i)
      from hij), fun i j hij => h2 i j (by simpa using hij)⟩,
    fun ⟨h1, h2⟩ => ⟨fun i j hij => h1 i j hij, fun i j hij => h2 i j (by simpa using hij)⟩⟩

theorem unipotentRadical_le_blockUpper : unipotentRadical F n β ≤ blockUpper F n β :=
  fun _ hg => (mem_unipotentRadical.1 hg).1

theorem mem_unipotentRadical_iff_leviProj {p : blockUpper F n β} :
    (p : GL (Fin n) F) ∈ unipotentRadical F n β ↔ leviProj F n β p = 1 := by
  constructor
  · rintro ⟨q, hq, hqp⟩
    rw [← (Subtype.ext hqp : q = p)]
    exact hq
  · intro h
    exact ⟨p, h, rfl⟩

theorem conj_mem_unipotentRadical {p u : GL (Fin n) F} (hp : p ∈ blockUpper F n β)
    (hu : u ∈ unipotentRadical F n β) : p * u * p⁻¹ ∈ unipotentRadical F n β := by
  have huP := unipotentRadical_le_blockUpper hu
  have h := (mem_unipotentRadical_iff_leviProj (p := ⟨u, huP⟩)).1 hu
  have hm : p * u * p⁻¹ ∈ blockUpper F n β :=
    (blockUpper F n β).mul_mem ((blockUpper F n β).mul_mem hp huP) ((blockUpper F n β).inv_mem hp)
  refine (mem_unipotentRadical_iff_leviProj (p := ⟨_, hm⟩)).2 ?_
  have : (⟨p * u * p⁻¹, hm⟩ : blockUpper F n β) = ⟨p, hp⟩ * ⟨u, huP⟩ * (⟨p, hp⟩)⁻¹ := rfl
  rw [this, map_mul, map_mul, h, mul_one, map_inv, mul_inv_cancel]

theorem leviProj_inv_mul_mem (p : blockUpper F n β) :
    ((leviIncl (leviProj F n β p))⁻¹ * p : blockUpper F n β).1 ∈ unipotentRadical F n β := by
  rw [mem_unipotentRadical_iff_leviProj, map_mul, map_inv, leviProj_leviIncl, inv_mul_cancel]

variable (F n) in
theorem diagGL_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    (diagGL F n d * g * (diagGL F n d)⁻¹ : GL (Fin n) F) i j =
      (d i : F) * g i j * ((d j)⁻¹ : Fˣ) := by
  rw [← map_inv]
  show ((diagGL F n d : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl

variable (F n) in
theorem diagGL_inv_conj_apply (d : Fin n → Fˣ) (g : GL (Fin n) F) (i j : Fin n) :
    ((diagGL F n d)⁻¹ * g * diagGL F n d : GL (Fin n) F) i j =
      (((d i)⁻¹ : Fˣ) : F) * g i j * (d j : F) := by
  rw [← map_inv]
  show ((diagGL F n d⁻¹ : Matrix (Fin n) (Fin n) F) * (g : Matrix (Fin n) (Fin n) F) *
    (diagGL F n d : Matrix (Fin n) (Fin n) F)) i j = _
  rw [coe_diagGL, coe_diagGL, mul_diagonal, diagonal_mul]
  rfl

variable (β) in

def blockRank (i : Fin n) : ℕ := (Finset.univ.filter fun j => β j < β i).card

theorem blockRank_lt {i j : Fin n} (h : β i < β j) : blockRank β i < blockRank β j := by
  refine Finset.card_lt_card ⟨fun k hk => ?_, fun hsub => ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact hk.trans h
  · have := hsub (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
    simp at this

theorem blockRank_eq {i j : Fin n} (h : β i = β j) : blockRank β i = blockRank β j := by
  simp [blockRank, h]

end Parabolic

end GroundTheory.Automorphic
