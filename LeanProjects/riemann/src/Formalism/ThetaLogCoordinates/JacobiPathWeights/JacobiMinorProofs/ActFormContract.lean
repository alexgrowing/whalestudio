import Mathlib
import Formalism.ThetaLogCoordinates.JacobiPathWeights.StatementC

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.InvariantFactorPaths.GelfandTsetlinBases

variable {R : Type*} [CommRing R] {n : ℕ}

theorem minorMap : MinorMap := by
  intro R R' _ _ φ n m I J
  unfold minorF
  split_ifs with h
  · rw [RingHom.map_det]
    rfl
  · exact map_zero φ

lemma sg_mul_self (I : Finset (Fin n)) (m : Fin n) : sg I m * sg I m = 1 := by
  rw [sg, ← mul_pow, neg_one_mul, neg_neg, one_pow]

lemma sg_insert {I : Finset (Fin n)} {m : Fin n} (hm : m ∉ I) (m' : Fin n) :
    sg (insert m I) m' = sg I m' * (if m' < m then -1 else 1) := by
  unfold sg
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun hmem => hm (Finset.mem_filter.mp hmem).1), pow_succ]
  · rw [mul_one]

lemma sg_erase {I : Finset (Fin n)} {m' : Fin n} (hm' : m' ∈ I) (m : Fin n) :
    sg (I.erase m') m = sg I m * (if m < m' then -1 else 1) := by
  unfold sg
  rw [Finset.filter_erase]
  split_ifs with h
  · have hmem : m' ∈ I.filter (fun j => m < j) := Finset.mem_filter.mpr ⟨hm', h⟩
    rw [Finset.card_erase_of_mem hmem]
    obtain ⟨c, hc⟩ : ∃ c, (I.filter fun j => m < j).card = c + 1 :=
      ⟨_, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨m', hmem⟩)).symm⟩
    rw [hc, Nat.add_sub_cancel, pow_succ]
    ring
  · rw [Finset.erase_eq_of_notMem (fun hmem => h (Finset.mem_filter.mp hmem).2), mul_one]

lemma sgR_mul_self (I : Finset (Fin n)) (m : Fin n) : ((sg I m : ℤ) : R) * ((sg I m : ℤ) : R) = 1 := by
  rw [← Int.cast_mul, sg_mul_self, Int.cast_one]

theorem contractWedge : ContractWedge := by
  intro R _ n K X Y
  funext I
  simp only [contrF, wedgeF, Pi.sub_apply]
  have hsgi : ∀ m, m ∉ I → sg (insert m I) m = sg I m := fun m hm => by
    rw [sg_insert hm]; simp
  have hsge : ∀ m', m' ∈ I → sg (I.erase m') m' = sg I m' := fun m' hm' => by
    rw [sg_erase hm']; simp
  have hL : ∀ m ∈ Iᶜ, ∑ m' ∈ insert m I, ((sg (insert m I) m' : ℤ) : R) * K ((insert m I).erase m') * X m' =
      ((sg I m : ℤ) : R) * K I * X m +
        ∑ m' ∈ I, ((sg (insert m I) m' : ℤ) : R) * K ((insert m I).erase m') * X m' := by
    intro m hm
    rw [Finset.mem_compl] at hm
    rw [Finset.sum_insert hm, Finset.erase_insert hm, hsgi m hm]
  have hR : ∀ m' ∈ I, ∑ m ∈ (I.erase m')ᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m')) =
      ((sg I m' : ℤ) : R) * Y m' * K I +
        ∑ m ∈ Iᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m')) := by
    intro m' hm'
    rw [Finset.compl_erase, Finset.sum_insert (by simpa using hm'), Finset.insert_erase hm', hsge m' hm']
  have hcross : ∀ m ∈ Iᶜ, ∀ m' ∈ I,
      ((sg I m : ℤ) : R) * Y m * (((sg (insert m I) m' : ℤ) : R) * K ((insert m I).erase m') * X m') =
        -(((sg I m' : ℤ) : R) * (((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m'))) * X m') := by
    intro m hm m' hm'
    rw [Finset.mem_compl] at hm
    have hne : m ≠ m' := fun h => hm (h ▸ hm')
    rw [sg_insert hm, sg_erase hm', Finset.erase_insert_of_ne hne]
    rcases lt_or_gt_of_ne hne with h | h
    · simp [h, not_lt.mpr h.le]
      ring
    · simp [h, not_lt.mpr h.le]
      ring
  have d1 : ∀ m, ((sg I m : ℤ) : R) * Y m * (((sg I m : ℤ) : R) * K I * X m) = X m * Y m * K I := by
    intro m
    linear_combination (Y m * K I * X m) * sgR_mul_self (R := R) I m
  have d2 : ∀ m, ((sg I m : ℤ) : R) * (((sg I m : ℤ) : R) * Y m * K I) * X m = X m * Y m * K I := by
    intro m
    linear_combination (Y m * K I * X m) * sgR_mul_self (R := R) I m
  conv_lhs => rw [Finset.sum_congr rfl (fun m hm => by rw [hL m hm])]
  have hRs : ∑ m' ∈ I, ((sg I m' : ℤ) : R) *
      (∑ m ∈ (I.erase m')ᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m'))) * X m' =
      ∑ m' ∈ I, ((sg I m' : ℤ) : R) * (((sg I m' : ℤ) : R) * Y m' * K I +
        ∑ m ∈ Iᶜ, ((sg (I.erase m') m : ℤ) : R) * Y m * K (insert m (I.erase m'))) * X m' :=
    Finset.sum_congr rfl (fun m' hm' => by rw [hR m' hm'])
  rw [hRs]
  simp only [mul_add, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun m' hm' => hcross m hm m' hm')),
    Finset.sum_congr rfl (fun m _ => d1 m), Finset.sum_congr rfl (fun m _ => d2 m)]
  simp only [Finset.sum_neg_distrib]
  conv_lhs => rw [Finset.sum_comm]
  rw [← Finset.sum_add_sum_compl I (fun a => X a * Y a * K I)]
  ring

lemma minorF_eq {d : ℕ} (m : Matrix (Fin n) (Fin n) R) {I J : Finset (Fin n)} (hI : I.card = d)
    (hJ : J.card = d) :
    minorF m I J = (m.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hI
  unfold minorF
  rw [dif_pos hJ]

lemma minorF_ne (m : Matrix (Fin n) (Fin n) R) {I J : Finset (Fin n)} (h : J.card ≠ I.card) :
    minorF m I J = 0 := by
  unfold minorF
  rw [dif_neg h]

lemma emb_succAbove {d : ℕ} {J J' : Finset (Fin n)} (h : J.card = d + 1) (j : Fin (d + 1))
    (hJ' : J' = J.erase (J.orderEmbOfFin h j)) (h' : J'.card = d) :
    (fun x => J.orderEmbOfFin h (j.succAbove x)) = J'.orderEmbOfFin h' := by
  subst hJ'
  apply Finset.orderEmbOfFin_unique h'
  · intro x
    rw [Finset.mem_erase]
    exact ⟨fun heq => Fin.succAbove_ne j x ((J.orderEmbOfFin h).injective heq),
      Finset.orderEmbOfFin_mem J h _⟩
  · exact (J.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove j)

lemma sg_emb {d : ℕ} {J : Finset (Fin n)} (h : J.card = d + 1) (j : Fin (d + 1)) :
    sg J (J.orderEmbOfFin h j) = (-1) ^ (d + (j : ℕ)) := by
  have hf : (J.filter fun x => J.orderEmbOfFin h j < x) =
      (Finset.Ioi j).map (J.orderEmbOfFin h).toEmbedding := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_map, Finset.mem_Ioi, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hx, hlt⟩
      have : x ∈ Set.range (J.orderEmbOfFin h) := by rw [Finset.range_orderEmbOfFin]; exact hx
      obtain ⟨k, rfl⟩ := this
      exact ⟨k, (J.orderEmbOfFin h).lt_iff_lt.mp hlt, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem J h k, (J.orderEmbOfFin h).lt_iff_lt.mpr hk⟩
  unfold sg
  rw [hf, Finset.card_map, Fin.card_Ioi]
  have hj := j.isLt
  rw [show d + (j : ℕ) = (d + 1 - 1 - j) + 2 * j by omega, pow_add, pow_mul]
  simp

lemma sum_emb {d : ℕ} {J : Finset (Fin n)} (h : J.card = d) (f : Fin n → R) :
    ∑ b ∈ J, f b = ∑ j, f (J.orderEmbOfFin h j) := by
  conv_lhs => rw [← Finset.image_orderEmbOfFin_univ J h]
  rw [Finset.sum_image (fun x _ y _ hxy => (J.orderEmbOfFin h).injective hxy)]

lemma det_rows_expand {d : ℕ} (m : Matrix (Fin n) (Fin n) R) (r : Fin (d + 1) → Fin n) (i : Fin (d + 1))
    {I' J : Finset (Fin n)} (hJ : J.card = d + 1) (hI' : I'.card = d)
    (hr : (fun x => r (i.succAbove x)) = I'.orderEmbOfFin hI') :
    (-1 : R) ^ (d + (i : ℕ)) * (m.submatrix r (J.orderEmbOfFin hJ)).det =
      ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m (r i) b := by
  rw [sum_emb hJ, Matrix.det_succ_row _ i, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hcard : (J.erase (J.orderEmbOfFin hJ j)).card = d := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem J hJ j), hJ]
    rfl
  rw [sg_emb hJ j, minorF_eq m hI' hcard, ← emb_succAbove hJ j rfl hcard, ← hr]
  simp only [Matrix.submatrix_apply, Matrix.submatrix_submatrix, Function.comp_def]
  push_cast
  have e : ((-1 : R) ^ (d + (i : ℕ))) * (-1) ^ ((i : ℕ) + (j : ℕ)) = (-1) ^ (d + (j : ℕ)) := by
    rw [← pow_add, show d + (i : ℕ) + ((i : ℕ) + (j : ℕ)) = d + j + 2 * i by ring, pow_add, pow_mul]
    simp
  linear_combination (m (r i) (J.orderEmbOfFin hJ j) *
    (m.submatrix (fun x => r (i.succAbove x)) (fun x => J.orderEmbOfFin hJ (j.succAbove x))).det) * e

lemma lap_row (m : Matrix (Fin n) (Fin n) R) (I' J : Finset (Fin n)) (a : Fin n) :
    ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m a b =
      if a ∈ I' then 0 else ((sg (insert a I') a : ℤ) : R) * minorF m (insert a I') J := by
  classical
  obtain ⟨d, hd⟩ : ∃ d, I'.card = d := ⟨_, rfl⟩
  by_cases hJ : J.card = d + 1
  · by_cases ha : a ∈ I'
    · rw [if_pos ha]
      have hr : (fun x => (Fin.cons a ⇑(I'.orderEmbOfFin hd) : Fin (d + 1) → Fin n)
          ((0 : Fin (d + 1)).succAbove x)) = I'.orderEmbOfFin hd := by
        funext x
        simp [Fin.succAbove_zero]
      have hexp := det_rows_expand m (Fin.cons a ⇑(I'.orderEmbOfFin hd) : Fin (d + 1) → Fin n) 0 hJ hd hr
      simp only [Fin.cons_zero] at hexp
      rw [← hexp]
      obtain ⟨k, hk⟩ : ∃ k, I'.orderEmbOfFin hd k = a := by
        have : a ∈ Set.range (I'.orderEmbOfFin hd) := by rw [Finset.range_orderEmbOfFin]; exact ha
        exact this
      rw [Matrix.det_zero_of_row_eq (i := 0) (j := k.succ) (Fin.succ_ne_zero k).symm
        (by funext c; simp [hk]), mul_zero]
    · rw [if_neg ha]
      have hcard : (insert a I').card = d + 1 := by rw [Finset.card_insert_of_notMem ha, hd]
      obtain ⟨i, hi⟩ : ∃ i, (insert a I').orderEmbOfFin hcard i = a := by
        have : a ∈ Set.range ((insert a I').orderEmbOfFin hcard) := by
          rw [Finset.range_orderEmbOfFin]; exact Finset.mem_insert_self a I'
        exact this
      have hr := emb_succAbove hcard i (J' := I') (by rw [hi, Finset.erase_insert ha]) hd
      have hexp := det_rows_expand m ((insert a I').orderEmbOfFin hcard) i hJ hd hr
      rw [hi] at hexp
      rw [← hexp]
      have hs := sg_emb hcard i
      rw [hi] at hs
      rw [hs, minorF_eq m hcard hJ]
      push_cast
      ring
  · rw [Finset.sum_eq_zero]
    · split_ifs with ha
      · rfl
      · rw [minorF_ne, mul_zero]
        rw [Finset.card_insert_of_notMem ha, hd]
        exact hJ
    · intro b hb
      rw [minorF_ne, mul_zero, zero_mul]
      rw [Finset.card_erase_of_mem hb, hd]
      have := Finset.card_pos.mpr ⟨b, hb⟩
      omega

lemma actF_add (K K' : Form R n) (m : Matrix (Fin n) (Fin n) R) :
    actF (K + K') m = actF K m + actF K' m := by
  funext J
  simp only [actF, Pi.add_apply, add_mul, Finset.sum_add_distrib]

lemma actF_smul (c : R) (K : Form R n) (m : Matrix (Fin n) (Fin n) R) :
    actF (c • K) m = c • actF K m := by
  funext J
  simp only [actF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma actF_sub (K K' : Form R n) (m : Matrix (Fin n) (Fin n) R) :
    actF (K - K') m = actF K m - actF K' m := by
  funext J
  simp only [actF, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma wedgeF_add (K K' : Form R n) (X : Fin n → R) :
    wedgeF (K + K') X = wedgeF K X + wedgeF K' X := by
  funext I
  simp only [wedgeF, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

lemma wedgeF_smul (c : R) (K : Form R n) (X : Fin n → R) :
    wedgeF (c • K) X = c • wedgeF K X := by
  funext I
  simp only [wedgeF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

lemma contrF_add (K K' : Form R n) (X : Fin n → R) :
    contrF (K + K') X = contrF K X + contrF K' X := by
  funext I
  simp only [contrF, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma contrF_smul (c : R) (K : Form R n) (X : Fin n → R) :
    contrF (c • K) X = c • contrF K X := by
  funext I
  simp only [contrF, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

theorem actFormWedge : FactX2wedge := by
  intro R _ n K X m
  funext J
  simp only [actF, wedgeF]
  have hR : ∑ b ∈ J, ((sg J b : ℤ) : R) * (∑ I', K I' * minorF m I' (J.erase b)) * Matrix.vecMul X m b =
      ∑ I', ∑ a, K I' * X a * ∑ b ∈ J, ((sg J b : ℤ) : R) * minorF m I' (J.erase b) * m a b := by
    simp only [Matrix.vecMul, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hR]
  simp only [lap_row]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm' (t' := Finset.univ) (s' := fun a => Finset.univ.filter (fun I => a ∈ I))
    (by intro I a; simp)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hZ : ∑ I', K I' * X a * (if a ∈ I' then 0 else ((sg (insert a I') a : ℤ) : R) * minorF m (insert a I') J) =
      ∑ I' ∈ Finset.univ.filter (fun I' => a ∉ I'),
        K I' * X a * (((sg (insert a I') a : ℤ) : R) * minorF m (insert a I') J) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro I' _
    split_ifs <;> simp_all
  rw [hZ]
  refine Finset.sum_nbij' (fun I => I.erase a) (fun I' => insert a I') ?_ ?_ ?_ ?_ ?_
  · intro I hI
    simp
  · intro I' hI'
    simp
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
    exact Finset.insert_erase hI
  · intro I' hI'
    simp only [Finset.coe_filter, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hI'
    exact Finset.erase_insert hI'
  · intro I hI
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hI
    simp only [Finset.insert_erase hI]
    ring

def basisF (I : Finset (Fin n)) : Form R n := fun I' => if I' = I then 1 else 0

lemma basisF_empty : (basisF ∅ : Form R n) = oneF := rfl

lemma basisF_insert {a : Fin n} {s : Finset (Fin n)} (hs : ∀ x ∈ s, x < a) :
    (basisF (insert a s) : Form R n) = wedgeF (basisF s) (Pi.single a 1) := by
  have has : a ∉ s := fun h => lt_irrefl a (hs a h)
  have hsg : sg (insert a s) a = 1 := by
    unfold sg
    have : (insert a s).filter (fun j => a < j) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact lt_irrefl _
      · exact lt_asymm (hs x hx)
    rw [this]
    rfl
  funext I
  simp only [wedgeF, basisF, Pi.single_apply, mul_ite, mul_one, mul_zero]
  simp only [Finset.sum_ite_eq', Finset.sum_ite_eq]
  by_cases ha : a ∈ I
  · rw [if_pos ha]
    by_cases hI : I = insert a s
    · subst hI
      rw [if_pos rfl, Finset.erase_insert has, if_pos rfl, hsg]
      simp
    · have : I.erase a ≠ s := fun he => hI (by rw [← he, Finset.insert_erase ha])
      rw [if_neg hI, if_neg this]
  · rw [if_neg ha, if_neg]
    rintro rfl
    exact ha (Finset.mem_insert_self a s)

theorem form_induction {P : Form R n → Prop} (h1 : P oneF)
    (hadd : ∀ K K', P K → P K' → P (K + K')) (hsmul : ∀ (c : R) K, P K → P (c • K))
    (hw : ∀ K X, P K → P (wedgeF K X)) (K : Form R n) : P K := by
  classical
  have hzero : P 0 := by
    have := hsmul 0 oneF h1
    rwa [zero_smul] at this
  have hbasis : ∀ I, P (basisF I) := by
    intro I
    exact Finset.induction_on_max I (by rw [basisF_empty]; exact h1)
      (fun a s hs ih => by rw [basisF_insert hs]; exact hw _ _ ih)
  have hK : K = ∑ I, K I • basisF I := by
    funext J
    simp [basisF, Finset.sum_apply]
  rw [hK]
  exact Finset.sum_induction _ P hadd hzero (fun I _ => hsmul _ _ (hbasis I))

lemma actF_oneF (m : Matrix (Fin n) (Fin n) R) : actF (oneF : Form R n) m = oneF := by
  funext J
  simp only [actF, oneF, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  unfold minorF
  by_cases hJ : J = ∅
  · subst hJ
    rw [dif_pos rfl, if_pos rfl]
    exact Matrix.det_eq_one_of_card_eq_zero (by first | exact Fintype.card_fin 0 | rfl | decide)
  · rw [dif_neg, if_neg hJ]
    simpa [Finset.card_eq_zero] using hJ

lemma contrF_oneF (Y : Fin n → R) : contrF (oneF : Form R n) Y = 0 := by
  funext I
  simp [contrF, oneF]

lemma actF_zero (m : Matrix (Fin n) (Fin n) R) : actF (0 : Form R n) m = 0 := by
  funext J
  simp [actF]

theorem actFormMul : FactX2mul := by
  intro R _ n K m m'
  constructor
  · refine form_induction (P := fun K => actF K 1 = K) ?_ ?_ ?_ ?_ K
    · exact actF_oneF 1
    · intro K K' h h'
      try dsimp only at h h' ⊢
      rw [actF_add, h, h']
    · intro c K h
      try dsimp only at h ⊢
      rw [actF_smul, h]
    · intro K X h
      try dsimp only at h ⊢
      rw [actFormWedge R n K X 1, h, Matrix.vecMul_one]
  · refine form_induction (P := fun K => actF (actF K m) m' = actF K (m * m')) ?_ ?_ ?_ ?_ K
    · try dsimp only
      rw [actF_oneF, actF_oneF, actF_oneF]
    · intro K K' h h'
      try dsimp only at h h' ⊢
      rw [actF_add, actF_add, actF_add, h, h']
    · intro c K h
      try dsimp only at h ⊢
      rw [actF_smul, actF_smul, actF_smul, h]
    · intro K X h
      try dsimp only at h ⊢
      rw [actFormWedge R n K X m, actFormWedge R n (actF K m) (Matrix.vecMul X m) m', h,
        actFormWedge R n K X (m * m'), Matrix.vecMul_vecMul]

theorem actFormContract : FactX2contr := by
  intro R _ n K Y g
  have hc : ∀ X : Fin n → R, ∑ a, Matrix.vecMul X (↑g : Matrix (Fin n) (Fin n) R) a *
      Matrix.vecMul Y (↑g⁻¹ : Matrix (Fin n) (Fin n) R).transpose a = ∑ a, X a * Y a := by
    intro X
    show dotProduct (Matrix.vecMul X (↑g : Matrix (Fin n) (Fin n) R))
        (Matrix.vecMul Y (↑g⁻¹ : Matrix (Fin n) (Fin n) R).transpose) = dotProduct X Y
    rw [Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Units.mul_inv,
      Matrix.one_mulVec]
  refine form_induction (P := fun K => actF (contrF K Y) (↑g : Matrix (Fin n) (Fin n) R) =
      contrF (actF K (↑g : Matrix (Fin n) (Fin n) R))
        (Matrix.vecMul Y (↑g⁻¹ : Matrix (Fin n) (Fin n) R).transpose)) ?_ ?_ ?_ ?_ K
  · try dsimp only
    rw [contrF_oneF, actF_zero, actF_oneF, contrF_oneF]
  · intro K K' h h'
    try dsimp only at h h' ⊢
    rw [contrF_add, actF_add, h, h', actF_add, contrF_add]
  · intro c K h
    try dsimp only at h ⊢
    rw [contrF_smul, actF_smul, h, actF_smul, contrF_smul]
  · intro K X h
    try dsimp only at h ⊢
    rw [contractWedge R n K X Y, actF_sub,
      show (fun I => (∑ a, X a * Y a) * K I) = (∑ a, X a * Y a) • K from rfl, actF_smul,
      actFormWedge R n (contrF K Y) X _, h, actFormWedge R n K X _,
      contractWedge R n (actF K _) (Matrix.vecMul X _) _, hc X]
    rfl

end Formalism.InvariantFactorPaths.GelfandTsetlinBases
