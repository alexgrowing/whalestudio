import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DensityLemma.PFibreBoundVDefs

open MeasureTheory Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6

noncomputable section

namespace PI.UnitaryGroupMassFormula.DLm

namespace NBk

variable {k r : ℕ}

def piI (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

def epsI (k r : ℕ) (i : Fin (2 * r + k + 1)) : ℂ := if i.val = r + k then -1 else 1

lemma piI_val (i : Fin (2 * r + k + 1)) :
    (piI k r i).val = if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val := by
  unfold piI
  split_ifs <;> rfl

lemma Hpk_apply (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = piI k r i then epsI k r i else 0 := by
  have hp := piI_val (k := k) (r := r) i
  have hi := i.isLt
  have hj := j.isLt
  simp only [Hpk, epsI, Fin.ext_iff, hp]
  split_ifs <;> first | rfl | (exfalso; omega)

lemma Hpk_mul_apply (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (i j) :
    (Hpk k r * X) i j = epsI k r i * X (piI k r i) j := by
  simp [Matrix.mul_apply, Hpk_apply]

lemma Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = epsI k r i * v (piI k r i) := by
  simp [Matrix.mulVec, dotProduct, Hpk_apply]

lemma uh_entry (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (p q) :
    (gᴴ * Hpk k r * g) p q = ∑ i, star (g i p) * (epsI k r i * g (piI k r i) q) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Hpk_mul_apply, Matrix.conjTranspose_apply]

lemma eI_val (a : Fin r) : (eI k r a).val = a.val := rfl
lemma wI_val (j : Fin (k + 1)) : (wI k r j).val = r + j.val := rfl
lemma esI_val (a : Fin r) : (esI k r a).val = 2 * r + k - a.val := rfl

lemma sum_split {M : Type*} [AddCommMonoid M] (f : Fin (2 * r + k + 1) → M) :
    ∑ i, f i = ∑ a : Fin r, f (eI k r a) + ∑ j : Fin (k + 1), f (wI k r j) + ∑ a : Fin r, f (esI k r a) := by
  have hinj : Function.Injective
      (Sum.elim (eI k r) (Sum.elim (wI k r) (esI k r)) : Fin r ⊕ (Fin (k + 1) ⊕ Fin r) → Fin (2 * r + k + 1)) := by
    rintro (a | j | a) (b | i | b) h <;>
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.ext_iff, eI_val, wI_val, esI_val, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq] at h ⊢ <;>
      omega
  have hbij : Function.Bijective
      (Sum.elim (eI k r) (Sum.elim (wI k r) (esI k r)) : Fin r ⊕ (Fin (k + 1) ⊕ Fin r) → Fin (2 * r + k + 1)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  rw [← Fintype.sum_bijective _ hbij (fun x => f (Sum.elim (eI k r) (Sum.elim (wI k r) (esI k r)) x)) f
    (fun _ => rfl)]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, add_assoc]

lemma cases3 {P : Fin (2 * r + k + 1) → Prop} (h1 : ∀ a, P (eI k r a)) (h2 : ∀ j, P (wI k r j))
    (h3 : ∀ a, P (esI k r a)) (i : Fin (2 * r + k + 1)) : P i := by
  have hi := i.isLt
  rcases Nat.lt_or_ge i.val r with h | h
  · have e : i = eI k r ⟨i.val, h⟩ := Fin.ext rfl
    rw [e]; exact h1 _
  · rcases Nat.lt_or_ge (r + k) i.val with h' | h'
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := Fin.ext (by simp only [esI_val, Fin.val_mk]; omega)
      rw [e]; exact h3 _
    · have e : i = wI k r ⟨i.val - r, by omega⟩ := Fin.ext (by simp only [wI_val, Fin.val_mk]; omega)
      rw [e]; exact h2 _

lemma piI_eI (a : Fin r) : piI k r (eI k r a) = esI k r a := Fin.ext (by
  rw [piI_val]
  have h1 : ¬ (r ≤ (eI k r a).val ∧ (eI k r a).val ≤ r + k) := by rw [eI_val]; omega
  rw [if_neg h1, eI_val, esI_val])
lemma piI_wI (j : Fin (k + 1)) : piI k r (wI k r j) = wI k r j := Fin.ext (by
  rw [piI_val]
  have h1 : r ≤ (wI k r j).val ∧ (wI k r j).val ≤ r + k := by rw [wI_val]; omega
  rw [if_pos h1])
lemma piI_esI (a : Fin r) : piI k r (esI k r a) = eI k r a := Fin.ext (by
  rw [piI_val]
  have h1 : ¬ (r ≤ (esI k r a).val ∧ (esI k r a).val ≤ r + k) := by rw [esI_val]; omega
  rw [if_neg h1, esI_val, eI_val]
  omega)
lemma epsI_eI (a : Fin r) : epsI k r (eI k r a) = 1 := by
  have h1 : ¬ ((eI k r a).val = r + k) := by rw [eI_val]; omega
  unfold epsI
  rw [if_neg h1]
lemma epsI_esI (a : Fin r) : epsI k r (esI k r a) = 1 := by
  have h1 : ¬ ((esI k r a).val = r + k) := by rw [esI_val]; omega
  unfold epsI
  rw [if_neg h1]
lemma epsI_wI (j : Fin (k + 1)) : epsI k r (wI k r j) = hW k j := by
  unfold epsI hW
  by_cases h : j.val = k
  · have h1 : (wI k r j).val = r + k := by rw [wI_val]; omega
    rw [if_pos h1, if_pos h]
  · have h1 : ¬ (wI k r j).val = r + k := by rw [wI_val]; omega
    rw [if_neg h1, if_neg h]

lemma hW_sq (j : Fin (k + 1)) : hW k j * hW k j = 1 := by
  unfold hW
  split_ifs <;> norm_num
lemma star_hW (j : Fin (k + 1)) : star (hW k j) = hW k j := by
  unfold hW
  split_ifs <;> simp

lemma eI_inj (a b : Fin r) : eI k r a = eI k r b ↔ a = b := by
  rw [Fin.ext_iff, Fin.ext_iff, eI_val, eI_val]
lemma wI_inj (i j : Fin (k + 1)) : wI k r i = wI k r j ↔ i = j := by
  rw [Fin.ext_iff, Fin.ext_iff, wI_val, wI_val]
  constructor <;> intro h <;> omega
lemma esI_inj (a b : Fin r) : esI k r a = esI k r b ↔ a = b := by
  rw [Fin.ext_iff, Fin.ext_iff, esI_val, esI_val]
  constructor <;> intro h <;> omega
lemma eI_ne_wI (a : Fin r) (j : Fin (k + 1)) : eI k r a ≠ wI k r j := by
  intro h
  have h' := congrArg Fin.val h
  simp only [eI_val, wI_val] at h'
  omega
lemma eI_ne_esI (a b : Fin r) : eI k r a ≠ esI k r b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [eI_val, esI_val] at h'
  omega
lemma wI_ne_esI (j : Fin (k + 1)) (b : Fin r) : wI k r j ≠ esI k r b := by
  intro h
  have h' := congrArg Fin.val h
  simp only [wI_val, esI_val] at h'
  omega

lemma star_ite_one_zero (p : Prop) [Decidable p] : star (if p then (1 : ℂ) else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

lemma Hpk_ee (a b : Fin r) : Hpk k r (eI k r a) (eI k r b) = 0 := by
  simp [Hpk_apply, piI_eI, eI_ne_esI]
lemma Hpk_ew (a : Fin r) (j : Fin (k + 1)) : Hpk k r (eI k r a) (wI k r j) = 0 := by
  simp [Hpk_apply, piI_eI, wI_ne_esI]
lemma Hpk_es (a b : Fin r) : Hpk k r (eI k r a) (esI k r b) = if a = b then 1 else 0 := by
  simp only [Hpk_apply, piI_eI, esI_inj, epsI_eI]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]
lemma Hpk_we (j : Fin (k + 1)) (b : Fin r) : Hpk k r (wI k r j) (eI k r b) = 0 := by
  simp [Hpk_apply, piI_wI, eI_ne_wI]
lemma Hpk_ww (i j : Fin (k + 1)) : Hpk k r (wI k r i) (wI k r j) = if i = j then hW k i else 0 := by
  simp only [Hpk_apply, piI_wI, wI_inj, epsI_wI]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]
lemma Hpk_ws (j : Fin (k + 1)) (b : Fin r) : Hpk k r (wI k r j) (esI k r b) = 0 := by
  simp [Hpk_apply, piI_wI, (wI_ne_esI j b).symm]
lemma Hpk_se (a b : Fin r) : Hpk k r (esI k r a) (eI k r b) = if a = b then 1 else 0 := by
  simp only [Hpk_apply, piI_esI, eI_inj, epsI_esI]
  by_cases h : a = b
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]
lemma Hpk_sw (a : Fin r) (j : Fin (k + 1)) : Hpk k r (esI k r a) (wI k r j) = 0 := by
  simp [Hpk_apply, piI_esI, (eI_ne_wI a j).symm]
lemma Hpk_ss (a b : Fin r) : Hpk k r (esI k r a) (esI k r b) = 0 := by
  simp [Hpk_apply, piI_esI, (eI_ne_esI a b).symm]

variable (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ)

lemma eI_back (a : Fin r) (h) : (⟨(eI k r a).val, h⟩ : Fin r) = a := Fin.ext rfl
lemma wI_back (j : Fin (k + 1)) (h) : (⟨(wI k r j).val - r, h⟩ : Fin (k + 1)) = j := Fin.ext (by simp only [Fin.val_mk, wI_val]; omega)
lemma esI_back (b : Fin r) (h) : (⟨2 * r + k - (esI k r b).val, h⟩ : Fin r) = b := Fin.ext (by simp only [Fin.val_mk, esI_val]; have := b.isLt; omega)

macro "nbt" : tactic => `(tactic| (simp only [unipotentBlockMatrix, Matrix.of_apply]; split_ifs <;>
  (try (exfalso; simp only [Fin.ext_iff, eI_val, wI_val, esI_val] at *; omega)) <;> simp [eI_back, wI_back, esI_back]))

lemma nb_ee (a b : Fin r) : unipotentBlockMatrix k r Bm S (eI k r a) (eI k r b) = if a = b then 1 else 0 := by
  nbt
lemma nb_we (j : Fin (k + 1)) (b : Fin r) : unipotentBlockMatrix k r Bm S (wI k r j) (eI k r b) = 0 := by
  nbt
lemma nb_se (a b : Fin r) : unipotentBlockMatrix k r Bm S (esI k r a) (eI k r b) = 0 := by
  nbt
lemma nb_ew (a : Fin r) (j : Fin (k + 1)) : unipotentBlockMatrix k r Bm S (eI k r a) (wI k r j) = Bm a j := by
  nbt
lemma nb_ww (i j : Fin (k + 1)) : unipotentBlockMatrix k r Bm S (wI k r i) (wI k r j) = if i = j then 1 else 0 := by
  nbt
lemma nb_sw (a : Fin r) (j : Fin (k + 1)) : unipotentBlockMatrix k r Bm S (esI k r a) (wI k r j) = 0 := by
  nbt
lemma nb_es (a b : Fin r) : unipotentBlockMatrix k r Bm S (eI k r a) (esI k r b) = cmOf k r Bm S a b := by
  nbt
lemma nb_ws (j : Fin (k + 1)) (b : Fin r) :
    unipotentBlockMatrix k r Bm S (wI k r j) (esI k r b) = -(hW k j) * star (Bm b j) := by
  nbt
lemma nb_ss (a b : Fin r) : unipotentBlockMatrix k r Bm S (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
  nbt

lemma X_apply (a b : Fin r) :
    (Bm * Matrix.diagonal (hW k) * Bmᴴ) a b = ∑ j, Bm a j * hW k j * star (Bm b j) := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply]

lemma X_herm (a b : Fin r) :
    star ((Bm * Matrix.diagonal (hW k) * Bmᴴ) b a) = (Bm * Matrix.diagonal (hW k) * Bmᴴ) a b := by
  rw [X_apply, X_apply, star_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [star_mul', star_mul', star_star, star_hW]
  ring

lemma cm_skew (hS : Sᴴ = -S) (a b : Fin r) :
    cmOf k r Bm S a b + star (cmOf k r Bm S b a) + (Bm * Matrix.diagonal (hW k) * Bmᴴ) a b = 0 := by
  have h1 : star (S b a) = -S a b := by
    have h := congrFun (congrFun hS a) b
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply] at h
    exact h
  have h2 := X_herm (k := k) Bm a b
  have h3 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  simp only [cmOf, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, star_sub, star_mul', h1, h2, h3]
  ring

lemma mid_sum (a b : Fin r) :
    ∑ j, star (-(hW k j) * star (Bm a j)) * (hW k j * (-(hW k j) * star (Bm b j))) =
      (Bm * Matrix.diagonal (hW k) * Bmᴴ) a b := by
  rw [X_apply]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [star_mul', star_neg, star_star, star_hW]
  linear_combination (Bm a j * star (Bm b j) * hW k j) * hW_sq j

lemma aux1 (x : ℂ) (j : Fin (k + 1)) : x + hW k j * (-hW k j * x) = 0 := by
  linear_combination (-x) * hW_sq j
lemma aux2 (x : ℂ) (j : Fin (k + 1)) : star (-hW k j * star x) * hW k j + x = 0 := by
  rw [star_mul', star_neg, star_star, star_hW]
  linear_combination (-x) * hW_sq j

private theorem fin_eq_eI_or_wI_or_esI (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ (∃ a, i = esI k r a) :=
  cases3 (P := fun i => (∃ a, i = eI k r a) ∨ (∃ j, i = wI k r j) ∨ (∃ a, i = esI k r a))
    (fun a => Or.inl ⟨a, rfl⟩) (fun j => Or.inr (Or.inl ⟨j, rfl⟩)) (fun a => Or.inr (Or.inr ⟨a, rfl⟩)) i

theorem nb_UH (hS : Sᴴ = -S) : unipotentBlockMatrix k r Bm S ∈ UH (Hpk k r) := by
  show (unipotentBlockMatrix k r Bm S)ᴴ * Hpk k r * unipotentBlockMatrix k r Bm S = Hpk k r
  ext p q
  rw [uh_entry, sum_split]
  rcases fin_eq_eI_or_wI_or_esI p with ⟨a, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩ <;>
    rcases fin_eq_eI_or_wI_or_esI q with ⟨b, rfl⟩ | ⟨i, rfl⟩ | ⟨b, rfl⟩ <;>
    simp only [piI_eI, piI_wI, piI_esI, epsI_eI, epsI_wI, epsI_esI, one_mul, mul_one, mul_zero, zero_mul,
      nb_ee, nb_we, nb_se, nb_ew, nb_ww, nb_sw, nb_es, nb_ws, nb_ss, star_ite_one_zero, star_zero,
      Finset.sum_const_zero, add_zero, zero_add, Hpk_ee, Hpk_ew, Hpk_es, Hpk_we, Hpk_ww, Hpk_ws, Hpk_se,
      Hpk_sw, Hpk_ss, ite_mul, mul_ite, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  all_goals first
    | exact aux1 _ _
    | exact aux2 _ _
    | (rw [mid_sum]; linear_combination cm_skew Bm S hS _ _)
    | (split_ifs <;> simp_all; done)

lemma inWb_eI {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin r) : z (eI k r a) = 0 := hz _ (Or.inl (by rw [eI_val]; exact a.isLt))
lemma inWb_esI {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin r) : z (esI k r a) = 0 := hz _ (Or.inr (by rw [esI_val]; have := a.isLt; omega))

lemma herm_Hpk_of_inWb_eq_sum_wI {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v z = ∑ j, star (z (wI k r j)) * (hW k j * v (wI k r j)) := by
  simp only [herm, dotProduct, Pi.star_apply, Hpk_mulVec]
  rw [sum_split]
  simp only [inWb_eI hz, inWb_esI hz, star_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero,
    piI_wI, epsI_wI]

lemma herm_esI (v : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) v (bvec (esI k r a)) = v (eI k r a) := by
  simp only [herm, dotProduct, Pi.star_apply, bvec, Pi.single_apply, star_ite_one_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Hpk_mulVec, piI_esI, epsI_esI]

lemma mulVec_bvec (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (x i : Fin (2 * r + k + 1)) :
    (g *ᵥ bvec x) i = g i x := by
  simp only [Matrix.mulVec, dotProduct, bvec, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

lemma nb_z_eI {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (a : Fin r) :
    (unipotentBlockMatrix k r Bm S *ᵥ z) (eI k r a) = (Bm *ᵥ zW k r z) a := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_split]
  simp only [nb_ew, inWb_eI hz, inWb_esI hz, mul_zero, Finset.sum_const_zero, zero_add, add_zero, zW]

lemma nb_z_wI {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (j : Fin (k + 1)) :
    (unipotentBlockMatrix k r Bm S *ᵥ z) (wI k r j) = z (wI k r j) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_split]
  simp only [nb_we, nb_ww, nb_ws, inWb_esI hz, zero_mul, mul_zero, Finset.sum_const_zero, zero_add,
    add_zero, ite_mul, one_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]

theorem nb_uMap {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hB : Bm *ᵥ zW k r z = 0) :
    C2.uMap k r z (unipotentBlockMatrix k r Bm S) = 1 := by
  obtain ⟨hzW, hT⟩ := hz
  have hne : herm (Hpk k r) z z ≠ 0 := by
    intro h0
    simp only [Formalism.QuantumDeterminants.Tz, h0, Complex.zero_re, neg_zero, lt_self_iff_false] at hT
  ext a b
  have ha' := a.isLt
  have hb' := b.isLt
  rw [Matrix.one_apply]
  simp only [C2.uMap]
  by_cases ha : a.val < r
  · rw [dif_pos ha, herm_esI]
    by_cases hb : b.val < r
    · simp only [fvec, dif_pos hb, mulVec_bvec, nb_ee]
      by_cases hab : a = b
      · subst hab; simp
      · rw [if_neg hab, if_neg]
        intro h; exact hab (Fin.ext (by simpa using congrArg Fin.val h))
    · simp only [fvec, dif_neg hb, nb_z_eI Bm S hzW, hB, Pi.zero_apply]
      rw [if_neg]
      intro h; apply hb; rw [← h]; exact ha
  · rw [dif_neg ha, herm_Hpk_of_inWb_eq_sum_wI hzW (unipotentBlockMatrix k r Bm S *ᵥ fvec k r z b)]
    by_cases hb : b.val < r
    · simp only [fvec, dif_pos hb, mulVec_bvec, nb_we, mul_zero, Finset.sum_const_zero, zero_div]
      rw [if_neg]
      intro h; apply ha; rw [h]; exact hb
    · simp only [fvec, dif_neg hb, nb_z_wI Bm S hzW]
      rw [← herm_Hpk_of_inWb_eq_sum_wI hzW z, div_self hne, if_pos]
      exact Fin.ext (by omega)

theorem nb_Nset (hS : Sᴴ = -S) : unipotentBlockMatrix k r Bm S ∈ Nset k r := by
  show _ ∧ _ ∧ _
  refine ⟨nb_UH Bm S hS, ?_, ?_⟩
  · intro a i _
    rcases fin_eq_eI_or_wI_or_esI i with ⟨c, rfl⟩ | ⟨j, rfl⟩ | ⟨c, rfl⟩
    · rw [nb_ee]; simp only [eI_inj]
    · rw [nb_we, if_neg (eI_ne_wI a j).symm]
    · rw [nb_se, if_neg (eI_ne_esI a c).symm]
  · intro i j hj1 hj2 hi
    simp only [unipotentBlockMatrix, Matrix.of_apply]
    split_ifs <;> first | (exfalso; omega) | simp

theorem nb_mem {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (hB : Bm *ᵥ zW k r z = 0) (hS : Sᴴ = -S) :
    unipotentBlockMatrix k r Bm S ∈ C2.N0set k r z := by
  show _ ∧ _
  exact ⟨nb_Nset Bm S hS, nb_uMap Bm S hz hB⟩

omit Bm S in
lemma um_lt (z : Fin (2 * r + k + 1) → ℂ) (n : B.Mat k r) (a : Fin r) (b : Fin (r + 1)) :
    C2.uMap k r z n ⟨a.val, by omega⟩ b = (n *ᵥ fvec k r z b) (eI k r a) := by
  simp only [C2.uMap]
  rw [dif_pos a.isLt, herm_esI]

omit Bm S in
lemma fvec_lt (z : Fin (2 * r + k + 1) → ℂ) (b : Fin r) : fvec k r z ⟨b.val, by omega⟩ = bvec (eI k r b) := by
  simp only [fvec]
  rw [dif_pos b.isLt]

omit Bm S in
lemma fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by
  simp [fvec]

omit Bm S in
lemma gz_eI {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (g : B.Mat k r) (a : Fin r) :
    (g *ᵥ z) (eI k r a) = ∑ j, g (eI k r a) (wI k r j) * z (wI k r j) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_split]
  simp only [inWb_eI hz, inWb_esI hz, mul_zero, Finset.sum_const_zero, zero_add, add_zero]

omit Bm S in
theorem nb_fwd {z : Fin (2 * r + k + 1) → ℂ} (hz : C2.StdZ k r z) (n : B.Mat k r) (hn : n ∈ C2.N0set k r z) :
    ∃ (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ),
      Bm *ᵥ zW k r z = 0 ∧ Sᴴ = -S ∧ n = unipotentBlockMatrix k r Bm S := by
  have hzW : inWb k r z := hz.1
  have hu : C2.uMap k r z n = 1 := hn.2
  have hN : n ∈ Nset k r := hn.1
  have hU : nᴴ * Hpk k r * n = Hpk k r := hN.1
  have hcol := hN.2.1
  have hmid := hN.2.2
  have hE : ∀ p q, ∑ i, star (n i p) * (epsI k r i * n (piI k r i) q) = Hpk k r p q := by
    intro p q
    have h := congrFun (congrFun hU p) q
    rwa [uh_entry] at h
  have hee : ∀ a b : Fin r, n (eI k r a) (eI k r b) = if a = b then 1 else 0 := by
    intro a b
    have h1 := congrFun (congrFun hu ⟨a.val, by omega⟩) ⟨b.val, by omega⟩
    rw [um_lt, fvec_lt, mulVec_bvec, Matrix.one_apply] at h1
    rw [h1]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg hab, if_neg]
      intro h; exact hab (Fin.ext (by simpa using congrArg Fin.val h))
  have hlast : ∀ a : Fin r, (n *ᵥ z) (eI k r a) = 0 := by
    intro a
    have h1 := congrFun (congrFun hu ⟨a.val, by omega⟩) (Fin.last r)
    rw [um_lt, fvec_last, Matrix.one_apply, if_neg] at h1
    · exact h1
    · intro h
      have h2 := congrArg Fin.val h
      simp only [Fin.val_last, Fin.val_mk] at h2
      have := a.isLt
      omega
  obtain ⟨B0, hB0⟩ : ∃ B0 : Matrix (Fin r) (Fin (k + 1)) ℂ, ∀ a j, B0 a j = n (eI k r a) (wI k r j) :=
    ⟨Matrix.of fun a j => n (eI k r a) (wI k r j), fun _ _ => rfl⟩
  obtain ⟨C0, hC0⟩ : ∃ C0 : Matrix (Fin r) (Fin r) ℂ, ∀ a b, C0 a b = n (eI k r a) (esI k r b) :=
    ⟨Matrix.of fun a b => n (eI k r a) (esI k r b), fun _ _ => rfl⟩
  obtain ⟨S0, hS0⟩ : ∃ S0 : Matrix (Fin r) (Fin r) ℂ,
      ∀ a b, S0 a b = C0 a b + (1 / 2 : ℂ) * (B0 * Matrix.diagonal (hW k) * B0ᴴ) a b :=
    ⟨C0 + (1 / 2 : ℂ) • (B0 * Matrix.diagonal (hW k) * B0ᴴ), fun a b => by
      rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]⟩
  have hwe : ∀ j b, n (wI k r j) (eI k r b) = 0 := by
    intro j b
    have := b.isLt
    rw [hcol b (wI k r j) (by rw [wI_val]; omega), if_neg (eI_ne_wI b j).symm]
  have hse : ∀ a b, n (esI k r a) (eI k r b) = 0 := by
    intro a b
    have := a.isLt
    have := b.isLt
    rw [hcol b (esI k r a) (by rw [esI_val]; omega), if_neg (eI_ne_esI b a).symm]
  have hww : ∀ i j, n (wI k r i) (wI k r j) = if i = j then 1 else 0 := by
    intro i j
    have := i.isLt
    have := j.isLt
    rw [hmid (wI k r i) (wI k r j) (by rw [wI_val]; omega) (by rw [wI_val]; omega) (by rw [wI_val]; omega)]
    simp only [wI_inj]
  have hsw : ∀ a j, n (esI k r a) (wI k r j) = 0 := by
    intro a j
    have := a.isLt
    have := j.isLt
    rw [hmid (esI k r a) (wI k r j) (by rw [wI_val]; omega) (by rw [wI_val]; omega)
      (by rw [esI_val]; omega), if_neg (wI_ne_esI j a).symm]
  have hss : ∀ a b, n (esI k r a) (esI k r b) = if a = b then 1 else 0 := by
    intro a b
    have h := hE (eI k r a) (esI k r b)
    rw [sum_split] at h
    simp only [piI_eI, piI_wI, piI_esI, epsI_eI, epsI_wI, epsI_esI, one_mul, hee, hwe, hse, star_ite_one_zero,
      star_zero, zero_mul, ite_mul, Finset.sum_const_zero, add_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Hpk_es] at h
    exact h
  have hws : ∀ j b, n (wI k r j) (esI k r b) = -(hW k j) * star (B0 b j) := by
    intro j b
    have h := hE (wI k r j) (esI k r b)
    rw [sum_split] at h
    simp only [piI_eI, piI_wI, piI_esI, epsI_eI, epsI_wI, epsI_esI, one_mul, hss, hww, hsw, star_ite_one_zero,
      star_zero, zero_mul, mul_zero, mul_one, ite_mul, mul_ite, Finset.sum_const_zero, add_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Hpk_ws] at h
    rw [hB0]
    linear_combination (hW k j) * h - n (wI k r j) (esI k r b) * hW_sq j
  have hcm : ∀ a b, C0 a b + star (C0 b a) + (B0 * Matrix.diagonal (hW k) * B0ᴴ) a b = 0 := by
    intro a b
    have h := hE (esI k r a) (esI k r b)
    rw [sum_split] at h
    simp only [piI_eI, piI_wI, piI_esI, epsI_eI, epsI_wI, epsI_esI, one_mul, hss, hws, star_ite_one_zero,
      mul_one, mul_zero, zero_mul, ite_mul, mul_ite, Finset.sum_const_zero, Finset.sum_ite_eq',
      Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Hpk_ss] at h
    rw [mid_sum] at h
    rw [hC0, hC0]
    linear_combination h
  have h12 : star (1 / 2 : ℂ) = 1 / 2 := by simp
  refine ⟨B0, S0, ?_, ?_, ?_⟩
  · funext a
    have h := hlast a
    rw [gz_eI hzW] at h
    simp only [Matrix.mulVec, dotProduct, zW, hB0, Pi.zero_apply]
    exact h
  · ext a b
    rw [Matrix.conjTranspose_apply, Matrix.neg_apply, hS0, hS0, star_add, star_mul', X_herm, h12]
    linear_combination hcm a b
  · ext p q
    rcases fin_eq_eI_or_wI_or_esI p with ⟨a, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases fin_eq_eI_or_wI_or_esI q with ⟨b, rfl⟩ | ⟨i, rfl⟩ | ⟨b, rfl⟩
    · rw [nb_ee, hee]
    · rw [nb_ew, hB0]
    · rw [nb_es]
      simp only [cmOf, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, hS0, hC0]
      ring
    · rw [nb_we, hwe]
    · rw [nb_ww, hww]
    · rw [nb_ws, hws]
    · rw [nb_se, hse]
    · rw [nb_sw, hsw]
    · rw [nb_ss, hss]

end NBk

theorem unipotentBlock_mem : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z →
    ∀ (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ),
      Bm *ᵥ zW k r z = 0 → Sᴴ = -S → unipotentBlockMatrix k r Bm S ∈ C2.N0set k r z := fun k r z hz Bm S hB hS => NBk.nb_mem Bm S hz hB hS

theorem unipotent_eq_block : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), C2.StdZ k r z →
    ∀ n ∈ C2.N0set k r z, ∃ (Bm : Matrix (Fin r) (Fin (k + 1)) ℂ) (S : Matrix (Fin r) (Fin r) ℂ),
      Bm *ᵥ zW k r z = 0 ∧ Sᴴ = -S ∧ n = unipotentBlockMatrix k r Bm S := fun k r z hz n hn => NBk.nb_fwd hz n hn

theorem unipotent_block_form : UnipotentBlockCoordinates := by
  intro k r z hz
  exact ⟨unipotent_eq_block k r z hz, unipotentBlock_mem k r z hz⟩

end PI.UnitaryGroupMassFormula.DLm
