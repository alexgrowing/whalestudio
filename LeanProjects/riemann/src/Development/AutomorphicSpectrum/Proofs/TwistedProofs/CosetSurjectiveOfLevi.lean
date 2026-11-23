import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLeviNormalizesUnipotentRadical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryBlockTriangularLeviPartUnitary

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta

namespace GlobalTheory.CompanionTheory.InertCoset

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

def hf (σ : L →+* L) (x y : Fin n → L) : L := ∑ k, σ (x k.rev) * y k

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem hf_conj (hσσ : ∀ x, σ (σ x) = x) (x y : Fin n → L) : σ (hf σ x y) = hf σ y x := by
  unfold hf
  rw [map_sum]
  refine Fintype.sum_equiv Fin.revPerm _ _ (fun k => ?_)
  simp [hσσ, mul_comm]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem hf_sub_left (x x' y : Fin n → L) : hf σ (x - x') y = hf σ x y - hf σ x' y := by
  simp only [hf, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem hf_sub_right (x y y' : Fin n → L) : hf σ x (y - y') = hf σ x y - hf σ x y' := by
  simp only [hf, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem hf_add_left (x x' y : Fin n → L) : hf σ (x + x') y = hf σ x y + hf σ x' y := by
  simp only [hf, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem hf_smul (c c' : L) (x y : Fin n → L) : hf σ (c • x) (c' • y) = σ c * c' * hf σ x y := by
  simp only [hf, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem hf_single_left (a : Fin n) (y : Fin n → L) : hf σ (Pi.single a 1) y = y a.rev := by
  unfold hf
  rw [Finset.sum_eq_single a.rev]
  · simp
  · intro b _ hb
    have hba : b.rev ≠ a := fun h => hb (by rw [← h, Fin.rev_rev])
    simp [Pi.single_apply, hba]
  · intro h
    exact absurd (Finset.mem_univ _) h

def refl (σ : L →+* L) (d : Fin n → L) : Matrix (Fin n) (Fin n) L := 1 + Matrix.of fun i j => d i * σ (d j.rev)

private theorem hform_add_right_orbital_bounds_conclusion (x y y' : Fin n → L) : hf σ x (y + y') = hf σ x y + hf σ x y' := by
  simp only [hf, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem hf_single_one_right (x : Fin n → L) (a : Fin n) : hf σ x (Pi.single a 1) = σ (x a.rev) := by
  unfold hf
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem single_one_rev_eq_antiJ_apply (i j : Fin n) : (Pi.single j (1 : L) : Fin n → L) i.rev = antiJ L n i j := by
  by_cases h : i.rev = j
  · subst h
    have hv : (i : ℕ) + (i.rev : ℕ) + 1 = n := by rw [Fin.val_rev]; omega
    show (Pi.single i.rev (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (i.rev : ℕ) + 1 = n then 1 else 0)
    rw [if_pos hv, Pi.single_eq_same]
  · have hv : ¬ ((i : ℕ) + (j : ℕ) + 1 = n) := by
      intro h'
      apply h
      ext
      rw [Fin.val_rev]
      omega
    show (Pi.single j (1 : L) : Fin n → L) i.rev = (if (i : ℕ) + (j : ℕ) + 1 = n then 1 else 0)
    rw [if_neg hv, Pi.single_eq_of_ne h]

private theorem cT_mul_antiJ_mul_apply_eq_hf_col (A : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ A * antiJ L n * A) i j = hf σ (fun k => A k i) (fun k => A k j) := by
  have key : ∀ l, (cT σ A * antiJ L n) i l = σ (A l.rev i) := by
    intro l
    simp only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single l.rev]
    · have hl : (l.rev : ℕ) + l + 1 = n := by rw [Fin.val_rev]; omega
      rw [if_pos hl, mul_one]
    · intro b _ hb
      have hbl : ¬ ((b : ℕ) + l + 1 = n) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      rw [if_neg hbl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [Matrix.mul_apply]
  simp only [key]
  rfl

theorem refl_unitary (hσσ : ∀ x, σ (σ x) = x) (d : Fin n → L) (hd : hf σ d d = -2) :
    cT σ (refl σ d) * antiJ L n * refl σ d = antiJ L n := by
  ext i j
  rw [cT_mul_antiJ_mul_apply_eq_hf_col]
  have hcol : ∀ i, (fun k => refl σ d k i) = Pi.single i 1 + σ (d i.rev) • d := by
    intro i
    ext k
    simp [refl, Matrix.one_apply, Pi.single_apply, mul_comm]
  rw [hcol i, hcol j, hf_add_left, hf_single_left]
  have h1 : hf σ (σ (d i.rev) • d) (Pi.single j 1 + σ (d j.rev) • d) =
      σ (σ (d i.rev)) * hf σ d (Pi.single j 1 + σ (d j.rev) • d) := by
    simpa using hf_smul (σ := σ) (σ (d i.rev)) 1 d (Pi.single j 1 + σ (d j.rev) • d)
  rw [h1, hform_add_right_orbital_bounds_conclusion, hf_single_one_right]
  have h2 : hf σ d (σ (d j.rev) • d) = σ (d j.rev) * hf σ d d := by
    simpa using hf_smul (σ := σ) 1 (σ (d j.rev)) d d
  rw [h2, hd, hσσ]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [single_one_rev_eq_antiJ_apply]
  ring

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem refl_mulVec (d x : Fin n → L) : refl σ d *ᵥ x = x + hf σ d x • d := by
  ext i
  simp only [refl, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hf]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem mem_intL' {x : L} : x ∈ intL L ↔ Valued.v x ≤ 1 := by
  exact Iff.rfl

private theorem mem_KU_of_mat_and_inv_mem_intL {m : ℕ} (A : GU σ m) (h1 : ∀ i j, mat A i j ∈ intL L)
    (h2 : ∀ i j, (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L) :
    A ∈ KU σ m := by
  let X : Matrix (Fin m) (Fin m) (intL L) := Matrix.of fun i j => ⟨mat A i j, h1 i j⟩
  let Y : Matrix (Fin m) (Fin m) (intL L) :=
    Matrix.of fun i j => ⟨(((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j, h2 i j⟩
  have hX : (intL L).subtype.mapMatrix X = mat A := by
    ext i j
    rfl
  have hY : (intL L).subtype.mapMatrix Y = (((A : GL (Fin m) L)⁻¹ : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) := by
    ext i j
    rfl
  have hinj : Function.Injective
      ((intL L).subtype.mapMatrix : Matrix (Fin m) (Fin m) (intL L) → Matrix (Fin m) (Fin m) L) :=
    Matrix.map_injective Subtype.val_injective
  have hXY : X * Y = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).mul_inv)
  have hYX : Y * X = 1 := hinj (by rw [map_mul, map_one, hX, hY]; exact (A : GL (Fin m) L).inv_mul)
  rw [KU, Subgroup.mem_subgroupOf]
  show (A : GL (Fin m) L) ∈ GU σ m ⊓ (bc (intL L).subtype).range
  refine Subgroup.mem_inf.2 ⟨A.2, MonoidHom.mem_range.2 ⟨⟨X, Y, hXY, hYX⟩, ?_⟩⟩
  apply Units.ext
  ext i j
  rfl

theorem exists_K_of_pair (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {e w : Fin n → L}
    (he : ∀ i, e i ∈ intL L) (hw : ∀ i, w i ∈ intL L) (hee : hf σ e e = 0) (hww : hf σ w w = 0)
    (hew : hf σ e w = 1) : ∃ k ∈ KU σ n, mat k *ᵥ e = w := by
  set d := e - w with hd_def
  have hwe : hf σ w e = 1 := by rw [← hf_conj hσσ, hew, map_one]
  have hdd : hf σ d d = -2 := by
    rw [hd_def, hf_sub_left, hf_sub_right, hf_sub_right, hee, hew, hwe, hww]
    ring
  have hde : hf σ d e = -1 := by
    rw [hd_def, hf_sub_left, hee, hwe]
    ring
  have hinv : ∀ x, refl σ d *ᵥ (refl σ d *ᵥ x) = x := by
    intro x
    rw [refl_mulVec, refl_mulVec, hform_add_right_orbital_bounds_conclusion]
    have h2 : hf σ d (hf σ d x • d) = hf σ d x * hf σ d d := by
      simpa using hf_smul (σ := σ) 1 (hf σ d x) d d
    rw [h2, hdd]
    ext k
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hRR : refl σ d * refl σ d = 1 := by
    apply Matrix.ext_of_mulVec_single
    intro i
    rw [← Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have hσint : ∀ x, x ∈ intL L → σ x ∈ intL L := fun x hx => mem_intL'.2 (by rw [hσ]; exact mem_intL'.1 hx)
  have hdint : ∀ i, d i ∈ intL L := fun i => (intL L).sub_mem (he i) (hw i)
  have hRint : ∀ i j, refl σ d i j ∈ intL L := by
    intro i j
    simp only [refl, Matrix.add_apply, Matrix.of_apply]
    refine (intL L).add_mem ?_ ((intL L).mul_mem (hdint i) (hσint _ (hdint j.rev)))
    rw [Matrix.one_apply]
    split_ifs
    · exact (intL L).one_mem
    · exact (intL L).zero_mem
  let R : GL (Fin n) L := ⟨refl σ d, refl σ d, hRR, hRR⟩
  have hRU : R ∈ GU σ n := refl_unitary hσσ d hdd
  refine ⟨⟨R, hRU⟩, mem_KU_of_mat_and_inv_mem_intL _ hRint hRint, ?_⟩
  show refl σ d *ᵥ e = w
  rw [refl_mulVec, hde, hd_def]
  ext k
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

theorem single_mem (a : Fin n) (c : L) (hc : c ∈ intL L) (i : Fin n) : (Pi.single a c : Fin n → L) i ∈ intL L := by
  rw [Pi.single_apply]
  split_ifs
  · exact hc
  · exact (intL L).zero_mem

theorem exists_K_single {N : ℕ} (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x)
    (a : Fin (N + 2)) (ha : a ≠ a.rev) :
    ∃ k ∈ KU σ (N + 2), mat k *ᵥ (Pi.single 0 1 : Fin (N + 2) → L) = Pi.single a 1 := by
  have hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0 := last_ne_zero
  have he0int : ∀ k, (Pi.single (0 : Fin (N + 2)) (1 : L) : Fin (N + 2) → L) k ∈ intL L :=
    single_mem 0 1 (intL L).one_mem
  have haint : ∀ k, (Pi.single a (1 : L) : Fin (N + 2) → L) k ∈ intL L := single_mem a 1 (intL L).one_mem
  have hee0 : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) (Pi.single 0 1) = 0 := by
    rw [hf_single_left, Fin.rev_zero, Pi.single_eq_of_ne hN0]
  by_cases ha0 : a = 0
  · subst ha0
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) *ᵥ _ = _
    rw [Matrix.one_mulVec]
  by_cases hal : a = Fin.last (N + 1)
  · subst hal
    refine exists_K_of_pair hσσ hσ he0int haint hee0 ?_ ?_
    · rw [hf_single_left, Fin.rev_last, Pi.single_eq_of_ne (Ne.symm hN0)]
    · rw [hf_single_left, Fin.rev_zero, Pi.single_eq_same]
  have hbr : a.rev.rev = a := Fin.rev_rev a
  have hb0 : a.rev ≠ 0 := by
    intro h
    apply hal
    rw [← hbr, h, Fin.rev_zero]
  have hbl : a.rev ≠ Fin.last (N + 1) := by
    intro h
    apply ha0
    rw [← hbr, h, Fin.rev_last]
  have hba : a.rev ≠ a := fun h => ha h.symm
  set v : Fin (N + 2) → L := Pi.single (Fin.last (N + 1)) 1 + Pi.single a.rev 1 with hv_def
  have hvint : ∀ k, v k ∈ intL L := fun k =>
    (intL L).add_mem (single_mem _ 1 (intL L).one_mem k) (single_mem _ 1 (intL L).one_mem k)
  have hvv : hf σ v v = 0 := by
    rw [hv_def, hf_add_left, hf_single_left, hf_single_left, Fin.rev_last, hbr]
    simp only [Pi.add_apply]
    rw [Pi.single_eq_of_ne (Ne.symm hN0), Pi.single_eq_of_ne (Ne.symm hb0), Pi.single_eq_of_ne hal,
      Pi.single_eq_of_ne (Ne.symm hba)]
    ring
  have h0v : hf σ (Pi.single (0 : Fin (N + 2)) (1 : L)) v = 1 := by
    rw [hf_single_left, Fin.rev_zero, hv_def, Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne (Ne.symm hbl),
      add_zero]
  have hva : hf σ v (Pi.single a 1) = 1 := by
    rw [hf_single_one_right, hv_def, Pi.add_apply, Pi.single_eq_of_ne hbl, Pi.single_eq_same, zero_add, map_one]
  have haa : hf σ (Pi.single a (1 : L)) (Pi.single a 1) = 0 := by
    rw [hf_single_left, Pi.single_eq_of_ne hba]
  obtain ⟨k1, hk1, hk1v⟩ := exists_K_of_pair hσσ hσ he0int hvint hee0 hvv h0v
  obtain ⟨k2, hk2, hk2v⟩ := exists_K_of_pair hσσ hσ hvint haint hvv haa hva
  refine ⟨k2 * k1, Subgroup.mul_mem _ hk2 hk1, ?_⟩
  show (mat k2 * mat k1) *ᵥ _ = _
  rw [← Matrix.mulVec_mulVec, hk1v, hk2v]

theorem exists_K_unit {N : ℕ} (hσσ : ∀ x, σ (σ x) = x) (hσ : ∀ x, Valued.v (σ x) = Valued.v x) {z : L}
    (hz : Valued.v z = 1) :
    ∃ k ∈ KU σ (N + 2), mat k *ᵥ (Pi.single 0 1 : Fin (N + 2) → L) = z • Pi.single 0 1 := by
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, map_zero] at hz
    exact zero_ne_one hz
  have hσz0 : σ z ≠ 0 := by
    intro h
    apply hz0
    rw [← hσσ z, h, map_zero]
  have hN0 : (Fin.last (N + 1) : Fin (N + 2)) ≠ 0 := last_ne_zero
  let δ : Fin (N + 2) → L := fun i => if i = 0 then z else if i = Fin.last (N + 1) then (σ z)⁻¹ else 1
  let δ' : Fin (N + 2) → L := fun i => if i = 0 then z⁻¹ else if i = Fin.last (N + 1) then σ z else 1
  have hδδ' : ∀ i, δ i * δ' i = 1 := by
    intro i
    simp only [δ, δ']
    split_ifs
    · exact mul_inv_cancel₀ hz0
    · exact inv_mul_cancel₀ hσz0
    · exact one_mul 1
  have hD1 : Matrix.diagonal δ * Matrix.diagonal δ' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hδδ' i
  have hD2 : Matrix.diagonal δ' * Matrix.diagonal δ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hδδ' i
  let D : GL (Fin (N + 2)) L := ⟨Matrix.diagonal δ, Matrix.diagonal δ', hD1, hD2⟩
  have hunit : ∀ i, σ (δ i) * δ i.rev = 1 := by
    intro i
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · simp only [δ, Fin.rev_zero, if_pos rfl, if_neg hN0]
      exact mul_inv_cancel₀ hσz0
    · have h1 : mid j ≠ 0 := mid_ne_zero j
      have h2 : mid j ≠ Fin.last (N + 1) := mid_ne_last j
      have h3 : (mid j).rev ≠ 0 := by rw [← mid_rev]; exact mid_ne_zero _
      have h4 : (mid j).rev ≠ Fin.last (N + 1) := by rw [← mid_rev]; exact mid_ne_last _
      simp only [δ, if_neg h1, if_neg h2, if_neg h3, if_neg h4, map_one, one_mul]
    · simp only [δ, Fin.rev_last, hN0, if_false, if_true, eq_self_iff_true, ↓reduceIte, map_inv₀, hσσ]
      exact inv_mul_cancel₀ hz0
  have hDU : D ∈ GU σ (N + 2) := by
    show cT σ (Matrix.diagonal δ) * antiJ L (N + 2) * Matrix.diagonal δ = antiJ L (N + 2)
    ext i j
    rw [cT_mul_antiJ_mul_apply_eq_hf_col]
    have hc : ∀ i, (fun k => Matrix.diagonal δ k i) = δ i • Pi.single i 1 := by
      intro i
      ext k
      by_cases hk : k = i
      · subst hk
        simp
      · simp [Matrix.diagonal_apply_ne _ hk, Pi.single_eq_of_ne hk]
    rw [hc i, hc j, hf_smul, hf_single_left, ← single_one_rev_eq_antiJ_apply]
    by_cases h : i.rev = j
    · subst h
      rw [Pi.single_eq_same, mul_one, hunit i]
    · rw [Pi.single_eq_of_ne h, mul_zero]
  have hint : ∀ x : L, Valued.v x = 1 → x ∈ intL L := fun x hx => mem_intL'.2 (le_of_eq hx)
  have hδint : ∀ i, δ i ∈ intL L := by
    intro i
    simp only [δ]
    split_ifs
    · exact hint _ hz
    · exact hint _ (by rw [map_inv₀, hσ, hz, inv_one])
    · exact (intL L).one_mem
  have hδ'int : ∀ i, δ' i ∈ intL L := by
    intro i
    simp only [δ']
    split_ifs
    · exact hint _ (by rw [map_inv₀, hz, inv_one])
    · exact hint _ (by rw [hσ, hz])
    · exact (intL L).one_mem
  have hdiag : ∀ (f : Fin (N + 2) → L), (∀ i, f i ∈ intL L) → ∀ i j, Matrix.diagonal f i j ∈ intL L := by
    intro f hf i j
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hf i
    · exact (intL L).zero_mem
  refine ⟨⟨D, hDU⟩, mem_KU_of_mat_and_inv_mem_intL _ (hdiag δ hδint) (hdiag δ' hδ'int), ?_⟩
  show Matrix.diagonal δ *ᵥ _ = _
  ext k
  rw [Matrix.mulVec_diagonal]
  by_cases hk : k = 0
  · subst hk
    simp [δ]
  · simp [Pi.single_eq_of_ne hk]

theorem exists_unit_coord {w : Fin n → L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hw : ∀ i, w i ∈ intL L)
    (hww : hf σ w w = 0) {i₀ : Fin n} (hi : Valued.v (w i₀) = 1) : ∃ i, i ≠ i.rev ∧ Valued.v (w i) = 1 := by
  by_contra hcon
  push Not at hcon
  have hi0 : i₀ = i₀.rev := by
    by_contra h
    exact hcon i₀ h hi
  have hlt : ∀ k, k ≠ i₀ → Valued.v (σ (w k.rev) * w k) < 1 := by
    intro k hk
    have hkr : k ≠ k.rev := by
      intro h
      apply hk
      ext
      have h1 := congrArg Fin.val h
      have h2 := congrArg Fin.val hi0
      rw [Fin.val_rev] at h1 h2
      omega
    have hwk : Valued.v (w k) < 1 := lt_of_le_of_ne (mem_intL'.1 (hw k)) (hcon k hkr)
    rw [map_mul, hσ]
    calc Valued.v (w k.rev) * Valued.v (w k) ≤ 1 * Valued.v (w k) :=
          mul_le_mul' (mem_intL'.1 (hw _)) le_rfl
      _ < 1 := by rw [one_mul]; exact hwk
  have hsplit : hf σ w w = σ (w i₀.rev) * w i₀ + ∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k := by
    unfold hf
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ i₀)).symm
  have hrest : Valued.v (∑ k ∈ Finset.univ.erase i₀, σ (w k.rev) * w k) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero (fun k hk => hlt k (Finset.ne_of_mem_erase hk))
  have hterm : Valued.v (σ (w i₀.rev) * w i₀) = 1 := by
    rw [map_mul, hσ, ← hi0, hi, one_mul]
  have hv1 : Valued.v (hf σ w w) = 1 := by
    rw [hsplit, Valuation.map_add_eq_of_lt_left _ (by rw [hterm]; exact hrest), hterm]
  rw [hww, map_zero] at hv1
  exact zero_ne_one hv1

theorem hf_col (h : GU σ n) (i j : Fin n) :
    hf σ (fun k => mat h k i) (fun k => mat h k j) = antiJ L n i j := by
  have hh : cT σ (mat h) * antiJ L n * mat h = antiJ L n := h.2
  have key : ∀ l, (cT σ (mat h) * antiJ L n) i l = σ (mat h l.rev i) := by
    intro l
    simp only [Matrix.mul_apply, antiJ, cT, Matrix.transpose_apply, Matrix.map_apply]
    rw [Finset.sum_eq_single l.rev]
    · have hl : (l.rev : ℕ) + l + 1 = n := by rw [Fin.val_rev]; omega
      rw [if_pos hl, mul_one]
    · intro b _ hb
      have hbl : ¬ ((b : ℕ) + l + 1 = n) := by
        intro h
        apply hb
        ext
        rw [Fin.val_rev]
        omega
      rw [if_neg hbl, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  calc hf σ (fun k => mat h k i) (fun k => mat h k j) = (cT σ (mat h) * antiJ L n * mat h) i j := by
        rw [Matrix.mul_apply]
        simp only [key]
        rfl
    _ = antiJ L n i j := by rw [hh]

theorem exists_zpow_unit {ϖ x : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (hx : x ≠ 0) :
    ∃ s : ℤ, Valued.v (ϖ ^ s * x) = 1 := by
  have hvx : Valued.v x ≠ 0 := (Valuation.ne_zero_iff _).2 hx
  obtain ⟨γ, hγ⟩ := WithZero.ne_zero_iff_exists.1 hvx
  refine ⟨Multiplicative.toAdd γ, ?_⟩
  have h1 : WithZero.exp (-1 : ℤ) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) := rfl
  rw [map_mul, map_zpow₀, hϖ, ← hγ, h1, ← WithZero.coe_zpow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_inj]
  apply Multiplicative.toAdd.injective
  simp

private theorem mulVec_single_one_eq_col (M : Matrix (Fin n) (Fin n) L) (j : Fin n) : M *ᵥ Pi.single j 1 = fun k => M k j := by
  ext k
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem exists_col {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) (g : GU σ (N + 2)) :
    ∃ s : ℤ, ∃ k ∈ KU σ (N + 2), ∀ i, mat (g * k) i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i := by
  obtain ⟨hσσ, hσ, -, hϖ, -⟩ := hU
  set u : Fin (N + 2) → L := mat g⁻¹ *ᵥ Pi.single 0 1 with hu_def
  have hgu : mat g *ᵥ u = Pi.single 0 1 := by
    rw [hu_def, Matrix.mulVec_mulVec]
    have h1 : mat g * mat g⁻¹ = 1 := by
      show mat (g * g⁻¹) = 1
      rw [mul_inv_cancel]
      rfl
    rw [h1, Matrix.one_mulVec]
  have huu : hf σ u u = 0 := by
    have h := hf_col g⁻¹ 0 0
    rw [hu_def, mulVec_single_one_eq_col, h]
    show (if ((0 : Fin (N + 2)) : ℕ) + ((0 : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) = 0
    rw [if_neg (by simp only [Fin.val_zero]; omega)]
  obtain ⟨i₁, -, hi₁⟩ := Finset.exists_max_image Finset.univ (fun k => Valued.v (u k)) Finset.univ_nonempty
  have hu1 : u i₁ ≠ 0 := by
    intro h0
    have hall : u = 0 := by
      ext k
      have hk := hi₁ k (Finset.mem_univ _)
      rw [h0, map_zero] at hk
      exact (Valuation.zero_iff _).1 (le_antisymm hk zero_le')
    rw [hall, Matrix.mulVec_zero] at hgu
    have h2 := congrFun hgu 0
    simp at h2
  obtain ⟨t, ht⟩ := exists_zpow_unit hϖ hu1
  set w : Fin (N + 2) → L := (ϖ ^ t) • u with hw_def
  have hwint : ∀ k, w k ∈ intL L := by
    intro k
    apply mem_intL'.2
    simp only [hw_def, Pi.smul_apply, smul_eq_mul, map_mul]
    rw [map_mul] at ht
    calc Valued.v (ϖ ^ t) * Valued.v (u k) ≤ Valued.v (ϖ ^ t) * Valued.v (u i₁) :=
          mul_le_mul' le_rfl (hi₁ k (Finset.mem_univ _))
      _ = 1 := ht
  have hwi₁ : Valued.v (w i₁) = 1 := by
    simpa [hw_def] using ht
  have hww : hf σ w w = 0 := by
    rw [hw_def, hf_smul, huu, mul_zero]
  obtain ⟨i, hi, hwi⟩ := exists_unit_coord hσ hwint hww hwi₁
  set u0 := w i with hu0
  have hu00 : u0 ≠ 0 := by
    intro h
    rw [h, map_zero] at hwi
    exact zero_ne_one hwi
  set z : L := (σ u0)⁻¹ with hz_def
  have hzv : Valued.v z = 1 := by rw [hz_def, map_inv₀, hσ, hwi, inv_one]
  set e : Fin (N + 2) → L := z • Pi.single i.rev 1 with he_def
  have heint : ∀ k, e k ∈ intL L := by
    intro k
    rw [he_def, Pi.smul_apply, smul_eq_mul]
    exact (intL L).mul_mem (mem_intL'.2 (le_of_eq hzv)) (single_mem _ 1 (intL L).one_mem k)
  have hee : hf σ e e = 0 := by
    rw [he_def, hf_smul, hf_single_left, Fin.rev_rev, Pi.single_eq_of_ne hi, mul_zero]
  have hew : hf σ e w = 1 := by
    have h := hf_smul (σ := σ) z 1 (Pi.single i.rev 1) w
    rw [one_smul, mul_one, hf_single_left, Fin.rev_rev] at h
    rw [he_def, h, hz_def, map_inv₀, hσσ]
    exact inv_mul_cancel₀ hu00
  obtain ⟨k1, hk1, hk1e⟩ := exists_K_of_pair hσσ hσ heint hwint hee hww hew
  have hirev : i.rev ≠ i.rev.rev := by
    rw [Fin.rev_rev]
    exact fun h => hi h.symm
  obtain ⟨k2, hk2, hk2e⟩ := exists_K_single hσσ hσ i.rev hirev
  obtain ⟨k3, hk3, hk3e⟩ := exists_K_unit (N := N) hσσ hσ hzv
  refine ⟨t, k1 * k2 * k3, Subgroup.mul_mem _ (Subgroup.mul_mem _ hk1 hk2) hk3, ?_⟩
  have hkv : mat (k1 * k2 * k3) *ᵥ Pi.single 0 1 = w := by
    show (mat k1 * mat k2 * mat k3) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hk3e, Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, hk2e, ← Matrix.mulVec_smul,
      ← he_def, hk1e]
  have hfinal : mat (g * (k1 * k2 * k3)) *ᵥ Pi.single 0 1 = ϖ ^ t • Pi.single 0 1 := by
    show (mat g * mat (k1 * k2 * k3)) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hkv, hw_def, Matrix.mulVec_smul, hgu]
  intro j
  have hj := congrFun hfinal j
  rw [mulVec_single_one_eq_col] at hj
  simpa using hj

section Levi

variable {N : ℕ} {ϖ : L} {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)}

theorem isLeviElt_mul (h0 : ϖ ≠ 0) (h : IsLeviElt ϖ a g m) (h' : IsLeviElt ϖ a' g' m') :
    IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  obtain ⟨hm, hm0, hl, hmid⟩ := h
  obtain ⟨hm', hm0', hl', hmid'⟩ := h'
  have hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm
  have hmat : mat (m * m') = mat m * mat m' := rfl
  refine ⟨Subgroup.mul_mem _ hm hm', ?_, ?_, ?_⟩
  · rw [hmat, Matrix.mul_apply, sum_idx,
      Finset.sum_eq_zero (fun j _ => by rw [hmz 0 (mid j) (by simp [blk_zero, blk_mid]), zero_mul]),
      hmz 0 (Fin.last (N + 1)) (by simp [blk_zero, blk_last]), hm0, hm0', zpow_add₀ h0]
    ring
  · rw [hmat, Matrix.mul_apply, sum_idx,
      Finset.sum_eq_zero (fun j _ => by rw [hmz (Fin.last (N + 1)) (mid j) (by simp [blk_last, blk_mid]), zero_mul]),
      hmz (Fin.last (N + 1)) 0 (by simp [blk_zero, blk_last]), hl, hl', neg_add, zpow_add₀ h0]
    ring
  · intro i j
    rw [hmat, Matrix.mul_apply, sum_idx, hmz (mid i) 0 (by simp [blk_zero, blk_mid]),
      hmz (mid i) (Fin.last (N + 1)) (by simp [blk_mid, blk_last])]
    simp only [zero_mul, zero_add, add_zero, hmid, hmid']
    show _ = (mat g * mat g') i j
    rw [Matrix.mul_apply]

theorem isLeviElt_unique (h : IsLeviElt ϖ a g m) (h' : IsLeviElt ϖ a g m') : m = m' := by
  obtain ⟨hm, h0, hl, hmid⟩ := h
  obtain ⟨hm', h0', hl', hmid'⟩ := h'
  have hmz : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hm
  have hmz' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := hm'
  have key : ∀ i j, mat m i j = mat m' i j := by
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
      all_goals first
        | (rw [h0, h0'])
        | (rw [hmid, hmid'])
        | (rw [hl, hl'])
        | (simp [blk_zero, blk_mid, blk_last] at hij)
    · rw [hmz i j hij, hmz' i j hij]
  exact Subtype.ext (Units.ext (Matrix.ext key))

end Levi

private theorem mat_apply_mem_intL_of_mem_KU {m : ℕ} {A : GU σ m} (hA : A ∈ KU σ m) (i j : Fin m) : mat A i j ∈ intL L := by
  rw [KU, Subgroup.mem_subgroupOf, intPts] at hA
  obtain ⟨-, hr⟩ := Subgroup.mem_inf.1 hA
  obtain ⟨g', hg'⟩ := MonoidHom.mem_range.1 hr
  show ((A : GL (Fin m) L) : Matrix (Fin m) (Fin m) L) i j ∈ intL L
  rw [← hg']
  exact ((g' : Matrix (Fin m) (Fin m) (intL L)) i j).2

private theorem mat_apply_mem_intL_of_isLeviElt_of_mem_KU {N : ℕ} {ϖ : L} {h : GU σ N} {e : GU σ (N + 2)} (he : IsLeviElt ϖ 0 h e)
    (hh : h ∈ KU σ N) (i j : Fin (N + 2)) : mat e i j ∈ intL L := by
  obtain ⟨heL, he0, hel, hem⟩ := he
  have hez : ∀ i j, blk N i ≠ blk N j → mat e i j = 0 := heL
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
    all_goals first
      | (rw [he0, zpow_zero]; exact (intL L).one_mem)
      | (rw [hem]; exact mat_apply_mem_intL_of_mem_KU hh _ _)
      | (rw [hel, neg_zero, zpow_zero]; exact (intL L).one_mem)
      | (simp [blk_zero, blk_mid, blk_last] at hij)
  · rw [hez i j hij]
    exact (intL L).zero_mem

theorem levi_step (hLE : LeviExists) {ϖ : L} {q N : ℕ} (hU : IsUnramInv ϖ σ q) {s : ℤ} (p : GU σ (N + 2))
    (hp : ∀ i, mat p i 0 = ϖ ^ s * (Pi.single 0 1 : Fin (N + 2) → L) i) :
    ∃ y : GU σ N ⧸ KU σ N, ∀ m, IsLeviElt ϖ s y.out m →
      ∃ u ∈ radQ σ N, ∃ k ∈ KU σ (N + 2), p = m * u * k := by
  have hU' := hU
  obtain ⟨hσσ, hσ, hσϖ, hϖ, -⟩ := hU'
  have hϖ0 : ϖ ≠ 0 := by
    intro h
    rw [h, map_zero] at hϖ
    exact WithZero.zero_ne_coe hϖ
  have hcol0 : (fun k => mat p k 0) = ϖ ^ s • Pi.single 0 1 := by
    funext k
    rw [hp k]
    rfl
  have hσs : σ (ϖ ^ s) = ϖ ^ s := by rw [map_zpow₀, hσϖ]
  have hrow : ∀ b, ϖ ^ s * mat p (Fin.last (N + 1)) b = (Pi.single b (1 : L) : Fin (N + 2) → L) (Fin.last (N + 1)) := by
    intro b
    have h := hf_col p 0 b
    rw [hcol0, ← single_one_rev_eq_antiJ_apply, Fin.rev_zero] at h
    have h2 := hf_smul (σ := σ) (ϖ ^ s) 1 (Pi.single 0 1) (fun k => mat p k b)
    rw [one_smul, mul_one, hf_single_left, Fin.rev_zero, hσs] at h2
    rw [← h, h2]
  have hlast0 : ∀ b, b ≠ Fin.last (N + 1) → mat p (Fin.last (N + 1)) b = 0 := by
    intro b hb
    have h := hrow b
    rw [Pi.single_eq_of_ne (Ne.symm hb)] at h
    exact (mul_eq_zero.1 h).resolve_left (zpow_ne_zero _ hϖ0)
  have hlastlast : mat p (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-s) := by
    have h := hrow (Fin.last (N + 1))
    rw [Pi.single_eq_same] at h
    rw [_root_.zpow_neg]
    exact eq_inv_of_mul_eq_one_right h
  have hp0 : ∀ i, i ≠ 0 → mat p i 0 = 0 := fun i hi => by rw [hp i, Pi.single_eq_of_ne hi, mul_zero]
  have htri : (mat p).BlockTriangular (blk N) := by
    intro i j hij
    rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl
    all_goals simp only [blk_zero, blk_mid, blk_last] at hij
    all_goals first
      | omega
      | exact hp0 _ (mid_ne_zero _)
      | exact hp0 _ last_ne_zero
      | exact hlast0 _ (mid_ne_last _)
  have hrevblk : ∀ a : Fin (N + 2), blk N a.rev = 2 - blk N a := by
    intro a
    rcases idx_cases a with rfl | ⟨i', rfl⟩ | rfl
    · rw [Fin.rev_zero, blk_last, blk_zero]
    · rw [← mid_rev, blk_mid, blk_mid]
    · rw [Fin.rev_last, blk_zero, blk_last]
  have hsym : ∀ a b : Fin (N + 2), blk N a = blk N b → blk N a.rev = blk N b.rev := by
    intro a b hab
    rw [hrevblk, hrevblk, hab]
  obtain ⟨m0, hm0L, hm0eq, hm0r⟩ := leviPart L σ (N + 2) (blk N) hsym p htri
  have hm0z : ∀ i j, blk N i ≠ blk N j → mat m0 i j = 0 := hm0L
  have hm0iL : m0⁻¹ ∈ leviU σ (blk N) := Subgroup.inv_mem _ hm0L
  have hm0iz : ∀ i j, blk N i ≠ blk N j → mat m0⁻¹ i j = 0 := hm0iL
  have hmidprod : ∀ (a b : GU σ (N + 2)), (∀ i j, blk N i ≠ blk N j → mat a i j = 0) → ∀ i j,
      mat (a * b) (mid i) (mid j) = ∑ k, mat a (mid i) (mid k) * mat b (mid k) (mid j) := by
    intro a b ha i j
    show (mat a * mat b) (mid i) (mid j) = _
    rw [Matrix.mul_apply, sum_idx, ha (mid i) 0 (by rw [blk_mid, blk_zero]; decide),
      ha (mid i) (Fin.last (N + 1)) (by rw [blk_mid, blk_last]; decide), zero_mul, zero_mul, zero_add, add_zero]
  have hone : ∀ i j : Fin N, (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (mid i) (mid j) =
      (1 : Matrix (Fin N) (Fin N) L) i j := by
    intro i j
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne (fun h' => h (mid_injective h'))]
  let G : Matrix (Fin N) (Fin N) L := fun i j => mat m0 (mid i) (mid j)
  let G' : Matrix (Fin N) (Fin N) L := fun i j => mat m0⁻¹ (mid i) (mid j)
  have hGG' : G * G' = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ k, mat m0 (mid i) (mid k) * mat m0⁻¹ (mid k) (mid j) = _
    rw [← hmidprod m0 m0⁻¹ hm0z, mul_inv_cancel]
    exact hone i j
  have hG'G : G' * G = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    show ∑ k, mat m0⁻¹ (mid i) (mid k) * mat m0 (mid k) (mid j) = _
    rw [← hmidprod m0⁻¹ m0 hm0iz, inv_mul_cancel]
    exact hone i j
  have hGU : cT σ G * antiJ L N * G = antiJ L N := by
    ext i j
    rw [cT_mul_antiJ_mul_apply_eq_hf_col]
    have h := hf_col m0 (mid i) (mid j)
    have hJ : antiJ L (N + 2) (mid i) (mid j) = antiJ L N i j := by
      show (if ((mid i : Fin (N + 2)) : ℕ) + ((mid j : Fin (N + 2)) : ℕ) + 1 = N + 2 then (1 : L) else 0) =
        (if (i : ℕ) + (j : ℕ) + 1 = N then 1 else 0)
      rw [val_mid, val_mid]
      by_cases hc : (i : ℕ) + (j : ℕ) + 1 = N
      · rw [if_pos (by omega), if_pos hc]
      · rw [if_neg (by omega), if_neg hc]
    rw [hJ] at h
    rw [← h]
    show ∑ k, σ (G k.rev i) * G k j = ∑ l, σ (mat m0 l.rev (mid i)) * mat m0 l (mid j)
    rw [sum_idx, hm0z 0 (mid j) (by rw [blk_zero, blk_mid]; decide),
      hm0z (Fin.last (N + 1)) (mid j) (by rw [blk_last, blk_mid]; decide), mul_zero, mul_zero, zero_add, add_zero]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← mid_rev]
  let g0 : GU σ N := ⟨⟨G, G', hGG', hG'G⟩, hGU⟩
  refine ⟨QuotientGroup.mk g0, fun m hm => ?_⟩
  obtain ⟨k0, hk0⟩ := QuotientGroup.mk_out_eq_mul (KU σ N) g0
  obtain ⟨e, he⟩ := hLE L ϖ σ q N hU 0 (k0 : GU σ N)
  obtain ⟨e', he'⟩ := hLE L ϖ σ q N hU 0 ((k0 : GU σ N)⁻¹)
  have hm0lev : IsLeviElt ϖ s g0 m0 := by
    refine ⟨hm0L, ?_, ?_, fun i j => rfl⟩
    · rw [hm0eq 0 0 rfl, hp 0, Pi.single_eq_same, mul_one]
    · rw [hm0eq _ _ rfl, hlastlast]
  have hprod := isLeviElt_mul hϖ0 hm0lev he
  rw [add_zero, ← hk0] at hprod
  have hmeq : m = m0 * e := isLeviElt_unique hm hprod
  have hee' : e * e' = 1 := by
    have h1 := isLeviElt_mul hϖ0 he he'
    rw [add_zero, mul_inv_cancel] at h1
    have h2 : IsLeviElt ϖ 0 (1 : GU σ N) (1 : GU σ (N + 2)) := by
      refine ⟨Subgroup.one_mem _, ?_, ?_, ?_⟩
      · show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) 0 0 = ϖ ^ (0 : ℤ)
        simp
      · show (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-(0 : ℤ))
        simp
      · intro i j
        exact hone i j
    exact isLeviElt_unique h1 h2
  have he'eq : e' = e⁻¹ := eq_inv_of_mul_eq_one_right hee'
  have heK : e ∈ KU σ (N + 2) := by
    refine mem_KU_of_mat_and_inv_mem_intL e (mat_apply_mem_intL_of_isLeviElt_of_mem_KU he k0.2) ?_
    intro i j
    have h := mat_apply_mem_intL_of_isLeviElt_of_mem_KU he' (Subgroup.inv_mem _ k0.2) i j
    rw [he'eq] at h
    exact h
  have heL' := he
  obtain ⟨heL, -⟩ := heL'
  refine ⟨e⁻¹ * (m0⁻¹ * p) * e, ?_, e⁻¹, Subgroup.inv_mem _ heK, ?_⟩
  · have h := (leviRad L σ (N + 2) (blk N) hσ e⁻¹ (Subgroup.inv_mem _ heL) (m0⁻¹ * p) hm0r).1
    rw [inv_inv] at h
    exact h
  · rw [hmeq]
    group

theorem cosetSurj : LeviExists → CosetSurj := by
  intro hLE L _ _ ϖ σ q N hU g
  obtain ⟨s, k, hk, hcol⟩ := exists_col hU g
  obtain ⟨y, hy⟩ := levi_step hLE hU (g * k) hcol
  refine ⟨s, y, fun m hm => ?_⟩
  obtain ⟨u, hu, k', hk', he⟩ := hy m hm
  refine ⟨u, hu, k' * k⁻¹, Subgroup.mul_mem _ hk' (Subgroup.inv_mem _ hk), ?_⟩
  rw [← mul_assoc, ← he, mul_inv_cancel_right]

end GlobalTheory.CompanionTheory.InertCoset

end
