import Mathlib
import CompanionTheory.AutomorphicTheory.ZuckermanCommutation.ZuckermanFunctors.IsSimpleFam
open CompanionTheory.Zuck BranchingSupport Matrix Finset
open scoped InnerProductSpace Kronecker

namespace GlobalTheory.CompanionTheory.WedgeEmb

variable {n m : ℕ}

def er (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) : BranchingSupport.Sub n m :=
  ⟨I.1.erase (I.1.orderEmbOfFin I.2 j), by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), I.2]; rfl⟩

theorem er_emb (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ⇑((er I j).1.orderEmbOfFin (er I j).2) = fun a => I.1.orderEmbOfFin I.2 (j.succAbove a) := by
  symm
  apply Finset.orderEmbOfFin_unique
  · intro a
    show _ ∈ I.1.erase _
    rw [Finset.mem_erase]
    exact ⟨fun h => Fin.succAbove_ne j a ((I.1.orderEmbOfFin I.2).injective h), Finset.orderEmbOfFin_mem _ _ _⟩
  · exact (I.1.orderEmbOfFin I.2).strictMono.comp (Fin.strictMono_succAbove j)

theorem exists_emb (I : BranchingSupport.Sub n (m + 1)) {t : Fin n} (ht : t ∈ I.1) : ∃ j, I.1.orderEmbOfFin I.2 j = t := by
  have h : t ∈ Set.range (I.1.orderEmbOfFin I.2) := by
    rw [Finset.range_orderEmbOfFin]
    exact ht
  exact h

theorem er_card (I : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j).card = j := by
  have key : ((er I j).1.filter fun a => a < I.1.orderEmbOfFin I.2 j) =
      (Finset.Iio j).map (I.1.orderEmbOfFin I.2).toEmbedding := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Iio, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨ha, hlt⟩
      have ha' : a ∈ I.1 := Finset.mem_of_mem_erase ha
      obtain ⟨i, rfl⟩ := exists_emb I ha'
      exact ⟨i, (I.1.orderEmbOfFin I.2).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      have hlt := (I.1.orderEmbOfFin I.2).lt_iff_lt.mpr hi
      exact ⟨Finset.mem_erase.mpr ⟨hlt.ne, Finset.orderEmbOfFin_mem _ _ _⟩, hlt⟩
  rw [key, Finset.card_map, Fin.card_Iio]

theorem jW_er (I I' : BranchingSupport.Sub n (m + 1)) (j : Fin (m + 1)) :
    jW n m (er I j, I.1.orderEmbOfFin I.2 j) I' = if I' = I then (-1) ^ (j : ℕ) else 0 := by
  have h1 : I.1.orderEmbOfFin I.2 j ∉ (er I j).1 := by simp [er]
  have h2 : insert (I.1.orderEmbOfFin I.2 j) (er I j).1 = I.1 :=
    Finset.insert_erase (Finset.orderEmbOfFin_mem _ _ _)
  simp only [jW, h1, not_false_eq_true, true_and, h2, er_card]
  by_cases hI : I' = I
  · subst hI
    simp
  · rw [if_neg (fun h => hI (Subtype.ext h)), if_neg hI]

theorem jW_ne (p : BranchingSupport.Sub n m × Fin n) (I : BranchingSupport.Sub n (m + 1)) (h : jW n m p I ≠ 0) :
    ∃ j, (er I j, I.1.orderEmbOfFin I.2 j) = p := by
  obtain ⟨J, t⟩ := p
  simp only [jW] at h
  by_cases hc : t ∉ J.1 ∧ I.1 = insert t J.1
  · have htI : t ∈ I.1 := by
      rw [hc.2]
      exact Finset.mem_insert_self t J.1
    obtain ⟨j, hj⟩ := exists_emb I htI
    refine ⟨j, ?_⟩
    rw [hj]
    refine Prod.ext ?_ rfl
    apply Subtype.ext
    show I.1.erase (I.1.orderEmbOfFin I.2 j) = J.1
    rw [hj, hc.2, Finset.erase_insert hc.1]
  · exact (h (if_neg hc)).elim

theorem sum_jW (F : BranchingSupport.Sub n m × Fin n → ℂ) (I : BranchingSupport.Sub n (m + 1)) :
    ∑ p, F p * jW n m p I = ∑ j : Fin (m + 1), (-1) ^ (j : ℕ) * F (er I j, I.1.orderEmbOfFin I.2 j) := by
  have hq : Function.Injective (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)) :=
    fun a b hab => (I.1.orderEmbOfFin I.2).injective (congrArg Prod.snd hab)
  rw [← Finset.sum_subset (Finset.subset_univ
    (Finset.univ.image (fun j : Fin (m + 1) => (er I j, I.1.orderEmbOfFin I.2 j)))) ?_]
  · rw [Finset.sum_image (fun a _ b _ hab => hq hab)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [jW_er, if_pos rfl, mul_comm]
  · intro p _ hp
    by_contra hne
    obtain ⟨j, hj⟩ := jW_ne p I (right_ne_zero_of_mul hne)
    exact hp (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩)

theorem laplace (g : Matrix (Fin n) (Fin n) ℂ) (r : Fin (m + 1) → Fin n) (i : Fin (m + 1))
    (J : BranchingSupport.Sub n m) (hJ : ⇑(J.1.orderEmbOfFin J.2) = fun a => r (i.succAbove a)) (I : BranchingSupport.Sub n (m + 1)) :
    ((cmp m g ⊗ₖ g) * jW n m) (J, r i) I =
      (-1) ^ (i : ℕ) * (g.submatrix r (I.1.orderEmbOfFin I.2)).det := by
  rw [Matrix.mul_apply]
  simp only [Matrix.kroneckerMap_apply]
  have hs := sum_jW (fun p => cmp m g J p.1 * g (r i) p.2) I
  simp only at hs
  rw [hs, Matrix.det_succ_row _ i, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hd : cmp m g J (er I j) =
      ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det := by
    unfold BranchingSupport.cmp
    rw [hJ, er_emb]
    rfl
  have h2 : ((-1 : ℂ)) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    rw [← mul_pow]
    norm_num
  rw [hd, Matrix.submatrix_apply, pow_add]
  generalize ((g.submatrix r ⇑(I.1.orderEmbOfFin I.2)).submatrix i.succAbove j.succAbove).det = d
  generalize g (r i) (I.1.orderEmbOfFin I.2 j) = x
  linear_combination (-(-1 : ℂ) ^ (j : ℕ) * d * x) * h2

theorem first (g : Matrix (Fin n) (Fin n) ℂ) : jW n m * cmp (m + 1) g = (cmp m g ⊗ₖ g) * jW n m := by
  ext ⟨J, t⟩ I
  by_cases ht : t ∈ J.1
  · have hL : (jW n m * cmp (m + 1) g) (J, t) I = 0 := by
      rw [Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro I'' _
      simp only [jW, ht, not_true_eq_false, false_and, if_false, zero_mul]
    have hl := laplace g (Fin.cons t ⇑(J.1.orderEmbOfFin J.2)) 0 J (by
      funext a
      simp only [Fin.succAbove_zero, Fin.cons_succ]) I
    rw [Fin.cons_zero] at hl
    rw [hL, hl]
    have hr : t ∈ Set.range (J.1.orderEmbOfFin J.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact ht
    obtain ⟨a, ha⟩ := hr
    rw [Matrix.det_zero_of_row_eq (i := (0 : Fin (m + 1))) (j := a.succ) (Fin.succ_ne_zero a).symm ?_, mul_zero]
    funext c
    simp only [Matrix.submatrix_apply, Fin.cons_zero, Fin.cons_succ, ha]
  · let K : BranchingSupport.Sub n (m + 1) := ⟨insert t J.1, by simp [ht, J.2]⟩
    obtain ⟨i, hi⟩ := exists_emb K (Finset.mem_insert_self t J.1)
    have hJK : er K i = J := by
      apply Subtype.ext
      show K.1.erase (K.1.orderEmbOfFin K.2 i) = J.1
      rw [hi]
      exact Finset.erase_insert ht
    have hl := laplace g ⇑(K.1.orderEmbOfFin K.2) i J (by rw [← hJK]; exact er_emb K i) I
    rw [hi] at hl
    rw [hl, Matrix.mul_apply, Finset.sum_eq_single K]
    · have hp : ((J, t) : BranchingSupport.Sub n m × Fin n) = (er K i, K.1.orderEmbOfFin K.2 i) := by
        rw [hJK, hi]
      rw [hp, jW_er, if_pos rfl]
      rfl
    · intro I'' _ hne
      simp only [jW]
      rw [if_neg (fun h => hne (Subtype.ext h.2)), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ K) h

theorem cmp_tr (l : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) : BranchingSupport.cmp l gᵀ = (BranchingSupport.cmp l g)ᵀ := by
  ext I J
  simp only [BranchingSupport.cmp, Matrix.transpose_apply]
  rw [← Matrix.det_transpose, Matrix.transpose_submatrix, Matrix.transpose_transpose]

theorem third : (jW n m)ᵀ * jW n m = ((m : ℂ) + 1) • (1 : Matrix (BranchingSupport.Sub n (m + 1)) (BranchingSupport.Sub n (m + 1)) ℂ) := by
  have h1 : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (-1) ^ (j : ℕ) = 1 := fun j => by
    rw [← mul_pow]
    norm_num
  ext I I'
  rw [Matrix.mul_apply]
  show ∑ p, jW n m p I * jW n m p I' = _
  have hs := sum_jW (fun p => jW n m p I') I
  rw [Finset.sum_congr rfl (fun p _ => mul_comm (jW n m p I) (jW n m p I')), hs]
  simp only [jW_er]
  by_cases h : I' = I
  · subst h
    have hc : ∀ j : Fin (m + 1), ((-1 : ℂ)) ^ (j : ℕ) * (if I' = I' then (-1) ^ (j : ℕ) else 0) = 1 :=
      fun j => by rw [if_pos rfl, h1]
    rw [Finset.sum_congr rfl (fun j _ => hc j), Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    norm_num
  · simp only [if_neg h, mul_zero, Finset.sum_const_zero, Matrix.smul_apply,
      Matrix.one_apply_ne (Ne.symm h), smul_zero]

theorem wedgeInt : WedgeInt := by
  intro n m
  refine ⟨fun g => ⟨first g, ?_⟩, third⟩
  have h := congrArg Matrix.transpose (first (n := n) (m := m) gᵀ)
  simp only [Matrix.transpose_mul, cmp_tr, Matrix.transpose_transpose,
    Matrix.kroneckerMap_transpose] at h
  exact h.symm

end GlobalTheory.CompanionTheory.WedgeEmb
