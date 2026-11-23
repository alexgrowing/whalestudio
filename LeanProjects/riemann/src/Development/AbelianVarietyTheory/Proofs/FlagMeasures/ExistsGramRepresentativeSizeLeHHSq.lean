import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowMinor
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramUnipotentStabilizerBruhatCellConjRoot

open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.GramSize

section Alg
variable {K : Type} [Field K] {N n : ℕ}

theorem sub_mul (A B : Matrix (Fin N) (Fin N) K) (I J M : Fin n → Fin N) (hM : Function.Injective M)
    (h : ∀ i j k, k ∉ Set.range M → A (I i) k * B k (J j) = 0) :
    (A * B).submatrix I J = A.submatrix I M * B.submatrix M J := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply]
  have hmap := Finset.sum_map Finset.univ ⟨M, hM⟩ (fun k => A (I i) k * B k (J j))
  simp only [Function.Embedding.coeFn_mk] at hmap
  rw [← hmap]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk
  apply h
  rintro ⟨x, rfl⟩
  exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ x))

theorem det_lo {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) (I : Fin n → Fin N) (hI : StrictMono I) :
    (L.submatrix I I).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (L.submatrix I I) (fun i j hij => (h (I i) (I j)).1 (hI (OrderDual.toDual_lt_toDual.mp hij)))]
  exact Finset.prod_eq_one (fun i _ => (h (I i) (I i)).2 rfl)

theorem det_up {U : Matrix (Fin N) (Fin N) K} (h : IsUpUni U) (I : Fin n → Fin N) (hI : StrictMono I) :
    (U.submatrix I I).det = 1 := by
  rw [Matrix.det_of_upperTriangular (M := U.submatrix I I) (fun i j hij => (h (I i) (I j)).1 (hI hij))]
  exact Finset.prod_eq_one (fun i _ => (h (I i) (I i)).2 rfl)

theorem lt_of_not_range (hn : n ≤ N) (i : Fin n) (k : Fin N) (hk : k ∉ Set.range (Fin.castLE hn)) :
    Fin.castLE hn i < k := by
  have hk' : n ≤ k.val := by
    by_contra hlt
    push_neg at hlt
    exact hk ⟨⟨k.val, hlt⟩, Fin.ext rfl⟩
  rw [Fin.lt_iff_val_lt_val, Fin.coe_castLE]
  exact lt_of_lt_of_le i.isLt hk'

theorem det_lo_mul {L : Matrix (Fin N) (Fin N) K} (h : IsLoUni L) (W : Matrix (Fin N) (Fin N) K)
    (hn : n ≤ N) (J : Fin n → Fin N) :
    ((L * W).submatrix (Fin.castLE hn) J).det = (W.submatrix (Fin.castLE hn) J).det := by
  have hsub : (L * W).submatrix (Fin.castLE hn) J =
      L.submatrix (Fin.castLE hn) (Fin.castLE hn) * W.submatrix (Fin.castLE hn) J :=
    GlobalTheory.LoopC.GramSize.sub_mul L W _ J (Fin.castLE hn) (Fin.castLE_injective hn) (fun i j k hk => by
      rw [(h _ _).1 (lt_of_not_range hn i k hk), zero_mul])
  rw [hsub, Matrix.det_mul, det_lo h _ (Fin.strictMono_castLE hn), one_mul]

theorem lead_inv {L U : Matrix (Fin N) (Fin N) K} (hL : IsLoUni L) (hU : IsUpUni U)
    (W : Matrix (Fin N) (Fin N) K) (l : ℕ) : leadMinorE (L * W * U) l = leadMinorE W l := by
  unfold leadMinorE
  by_cases hl : l ≤ N
  · rw [dif_pos hl, dif_pos hl, Matrix.mul_assoc, det_lo_mul hL (W * U) hl]
    have hUt : IsLoUni Uᵀ := fun i j => ⟨(hU j i).1, fun e => (hU j i).2 e.symm⟩
    have key := det_lo_mul hUt Wᵀ hl (Fin.castLE hl)
    rw [← Matrix.transpose_mul, ← Matrix.transpose_submatrix, ← Matrix.transpose_submatrix,
      Matrix.det_transpose, Matrix.det_transpose] at key
    exact key
  · rw [dif_neg hl, dif_neg hl]

theorem det_mono_sq {w : Matrix (Fin N) (Fin N) K} {σ : Equiv.Perm (Fin N)} {d : Fin N → K}
    (hw : ∀ i j, w i j = if j = σ i then d i else 0) (I J : Fin n → Fin N) (hI : Function.Injective I)
    (hJ : Function.Injective J) (h : ∀ i, σ (I i) ∈ Set.range J) :
    (w.submatrix I J).det ^ 2 = (∏ i, d (I i)) ^ 2 := by
  have h' : ∀ i, ∃ j, J j = σ (I i) := h
  choose π hπ using h'
  have hπi : Function.Injective π := fun a b hab => hI (σ.injective (by rw [← hπ a, ← hπ b, hab]))
  set e : Equiv.Perm (Fin n) := Equiv.ofBijective π hπi.bijective_of_finite with he
  have hsub : w.submatrix I J = Matrix.diagonal (fun i => d (I i)) * e.toPEquiv.toMatrix := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.submatrix_apply, hw, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
    simp only [Option.mem_def, Option.some.injEq]
    have hiff : (J j = σ (I i)) ↔ (e i = j) := by
      rw [← hπ i]
      exact ⟨fun hh => (hJ hh).symm, fun hh => by rw [← hh]; rfl⟩
    by_cases hc : e i = j
    · rw [if_pos (hiff.mpr hc), if_pos hc, mul_one]
    · rw [if_neg (fun h2 => hc (hiff.mp h2)), if_neg hc, mul_zero]
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_permutation, mul_pow]
  rcases Int.units_eq_one_or (Equiv.Perm.sign e) with hs | hs <;> simp [hs]

theorem det_OM_sq {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (I J : Fin n → Fin (r + 1)) :
    ((ZhatOM Z).submatrix I J).det ^ 2 = (Z.submatrix I J).det ^ 2 := by
  have hsub : (ZhatOM Z).submatrix I J =
      Z.submatrix I J * Matrix.diagonal (fun j => (-1 : K) ^ (r - (J j).val)) := by
    ext a b
    rw [Matrix.mul_diagonal, Matrix.submatrix_apply, Matrix.submatrix_apply]
    simp only [ZhatOM]
    ring
  rw [hsub, Matrix.det_mul, Matrix.det_diagonal, mul_pow, ← Finset.prod_pow,
    Finset.prod_eq_one (fun j _ => by rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]), mul_one]

theorem last_block (bs : List (K × ℕ)) (h : ∀ b ∈ bs, b.1 ≠ 0 ∧ 1 ≤ b.2) (hne : bs ≠ []) :
    ∃ (l : ℕ) (t : K), l < (bs.map Prod.snd).sum ∧ t ≠ 0 ∧ (∀ i j, i < l → l ≤ j → ptEntry bs i j = 0) ∧
      ∀ i j, l ≤ i → l ≤ j → i + j + 1 = (bs.map Prod.snd).sum + l → ptEntry bs i j = t := by
  induction bs with
  | nil => exact absurd rfl hne
  | cons b rest ih =>
    obtain ⟨t0, s0⟩ := b
    have hb := h (t0, s0) List.mem_cons_self
    simp only at hb
    by_cases hr : rest = []
    · subst hr
      refine ⟨0, t0, ?_, hb.1, fun i j hi _ => absurd hi (Nat.not_lt_zero _), fun i j _ _ hij => ?_⟩
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
        omega
      · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hij
        simp only [ptEntry]
        rw [if_pos ⟨by omega, by omega⟩, if_pos (by omega)]
    · obtain ⟨l, t, hl, ht, h1, h2⟩ := ih (fun b hb' => h b (List.mem_cons_of_mem _ hb')) hr
      simp only [List.map_cons, List.sum_cons]
      refine ⟨s0 + l, t, by omega, ht, fun i j hi hj => ?_, fun i j hi hj hij => ?_⟩
      · simp only [ptEntry]
        rw [if_neg (by omega)]
        by_cases h3 : s0 ≤ i ∧ s0 ≤ j
        · rw [if_pos h3]
          exact h1 _ _ (by omega) (by omega)
        · rw [if_neg h3]
      · simp only [ptEntry]
        rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩]
        exact h2 _ _ (by omega) (by omega) (by omega)

theorem prod_tail (e : ℕ → K) (t : K) (l k : ℕ) (hlk : l ≤ k) (h : ∀ i, l ≤ i → i < k → e i = t) :
    ∏ i ∈ Finset.range k, e i = (∏ i ∈ Finset.range l, e i) * t ^ (k - l) := by
  rw [← Finset.prod_range_mul_prod_Ico e hlk,
    Finset.prod_congr rfl (fun i hi => h i (Finset.mem_Ico.mp hi).1 (Finset.mem_Ico.mp hi).2),
    Finset.prod_const, Nat.card_Ico]

theorem cell_minor {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (p : Point K (r + 1))
    (hp : IsInCell (ZhatOM Z) p) :
    ∃ (b₀ : Fin (r + 1)) (l : ℕ) (a t : K), l ≤ r ∧ a ≠ 0 ∧ t ≠ 0 ∧
      ((Z.submatrix Fin.castSucc id).submatrix id b₀.succAbove).det ^ 2 = (a * t ^ (r - l)) ^ 2 ∧
      leadMinorE Z l ^ 2 = a ^ 2 ∧ leadMinorE Z (r + 1) ^ 2 = (a * t ^ (r + 1 - l)) ^ 2 := by
  obtain ⟨L, U, hL, hU, hZ⟩ := hp
  obtain ⟨σ, d, hd, hw⟩ := GlobalTheory.LoopV.Cell.ptMat_monomial p
  have hpne : p.1 ≠ [] := by
    intro hnil
    have hs := p.2.2
    rw [hnil] at hs
    simp at hs
  obtain ⟨l, t, hl, ht, h0, ht'⟩ := last_block p.1 p.2.1 hpne
  rw [p.2.2] at hl ht'
  have hent : ∀ i j : Fin (r + 1), ptMat p i j = ptEntry p.1 i.val j.val := fun _ _ => rfl
  have hσlast : ∀ i : Fin (r + 1), ∀ _hi : l ≤ i.val, σ i = ⟨r + l - i.val, by have := i.isLt; omega⟩ ∧ d i = t := by
    intro i hi
    have hi2 := i.isLt
    have hval : ptMat p i ⟨r + l - i.val, by omega⟩ = t := by
      rw [hent]
      exact ht' _ _ hi (show l ≤ r + l - i.val by omega) (show i.val + (r + l - i.val) + 1 = r + 1 + l by omega)
    rw [hw] at hval
    by_cases hc : (⟨r + l - i.val, by omega⟩ : Fin (r + 1)) = σ i
    · rw [if_pos hc] at hval
      exact ⟨hc.symm, hval⟩
    · rw [if_neg hc] at hval
      exact absurd hval.symm ht
  have hσfirst : ∀ i : Fin (r + 1), i.val < l → (σ i).val < l := by
    intro i hi
    by_contra hc
    push_neg at hc
    have hz := h0 i.val (σ i).val hi hc
    rw [← hent, hw, if_pos rfl] at hz
    exact hd i hz
  obtain ⟨e, he⟩ : ∃ e : ℕ → K, ∀ k (hk : k < r + 1), e k = d ⟨k, hk⟩ :=
    ⟨fun k => if hk : k < r + 1 then d ⟨k, hk⟩ else 0, fun k hk => dif_pos hk⟩
  have hde : ∀ (n : ℕ) (hn : n ≤ r + 1) (i : Fin n), d (Fin.castLE hn i) = e i.val := by
    intro n hn i
    rw [he _ (lt_of_lt_of_le i.isLt hn)]
    rfl
  have hde' : ∀ i : Fin r, d (Fin.castSucc i) = e i.val := by
    intro i
    rw [he _ (Nat.lt_succ_of_lt i.isLt)]
    rfl
  have hLM : ∀ (n : ℕ) (hn : n ≤ r + 1), leadMinorE Z n ^ 2 = leadMinorE (ptMat p) n ^ 2 := by
    intro n hn
    rw [← lead_inv hL hU (ptMat p) n, ← hZ]
    unfold leadMinorE
    rw [dif_pos hn, dif_pos hn, det_OM_sq]
  have hmono : ∀ (n : ℕ) (hn : n ≤ r + 1), (∀ i : Fin n, (σ (Fin.castLE hn i)).val < n) →
      leadMinorE (ptMat p) n ^ 2 = (∏ k ∈ Finset.range n, e k) ^ 2 := by
    intro n hn hσn
    unfold leadMinorE
    rw [dif_pos hn, det_mono_sq hw _ _ (Fin.castLE_injective hn) (Fin.castLE_injective hn)
      (fun i => ⟨⟨(σ (Fin.castLE hn i)).val, hσn i⟩, Fin.ext rfl⟩),
      Finset.prod_congr rfl (fun i _ => hde n hn i), Fin.prod_univ_eq_prod_range]
  have hlr : l ≤ r := by omega
  have hlast : σ (Fin.last r) = ⟨l, hl⟩ := by
    rw [(hσlast (Fin.last r) (by rw [Fin.val_last]; omega)).1]
    apply Fin.ext
    show r + l - (Fin.last r).val = l
    rw [Fin.val_last]
    omega
  have hσI : ∀ i : Fin r, σ (Fin.castSucc i) ≠ ⟨l, hl⟩ := by
    intro i hh
    rw [← hlast] at hh
    exact (Fin.castSucc_lt_last i).ne (σ.injective hh)
  have hrowW : ((ptMat p * U).submatrix Fin.castSucc (Fin.succAbove ⟨l, hl⟩)).det =
      ((ptMat p).submatrix Fin.castSucc (Fin.succAbove ⟨l, hl⟩)).det := by
    rw [GlobalTheory.LoopC.GramSize.sub_mul (ptMat p) U Fin.castSucc (Fin.succAbove ⟨l, hl⟩) (Fin.succAbove ⟨l, hl⟩)
      Fin.succAbove_right_injective ?_, Matrix.det_mul,
      det_up hU _ (Fin.strictMono_succAbove _), mul_one]
    intro i j k hk
    have hkb : k = ⟨l, hl⟩ := by
      by_contra hne
      obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hne
      exact hk ⟨z, hz⟩
    rw [hkb, hw, if_neg (fun hh => hσI i hh.symm), zero_mul]
  have hcs : (Fin.castSucc : Fin r → Fin (r + 1)) = Fin.castLE (Nat.le_succ r) :=
    funext fun i => Fin.ext rfl
  have hrow : ((Z.submatrix Fin.castSucc id).submatrix id (Fin.succAbove ⟨l, hl⟩)).det ^ 2 =
      (∏ k ∈ Finset.range r, e k) ^ 2 := by
    have h1 : (Z.submatrix Fin.castSucc id).submatrix id (Fin.succAbove ⟨l, hl⟩) =
        Z.submatrix Fin.castSucc (Fin.succAbove ⟨l, hl⟩) := rfl
    rw [h1, ← det_OM_sq Z Fin.castSucc (Fin.succAbove ⟨l, hl⟩), hZ, Matrix.mul_assoc, hcs,
      det_lo_mul hL (ptMat p * U) (Nat.le_succ r), ← hcs, hrowW,
      det_mono_sq hw _ _ (Fin.castSucc_injective r) Fin.succAbove_right_injective
        (fun i => Fin.exists_succAbove_eq (hσI i)),
      Finset.prod_congr rfl (fun i _ => hde' i), Fin.prod_univ_eq_prod_range]
  have hpt : ∀ k, l ≤ k → k < r + 1 → e k = t := fun k h1 h2 => by
    rw [he k h2]
    exact (hσlast ⟨k, h2⟩ h1).2
  refine ⟨⟨l, hl⟩, l, ∏ k ∈ Finset.range l, e k, t, hlr, ?_, ht, ?_, ?_, ?_⟩
  · rw [Finset.prod_ne_zero_iff]
    intro k hk
    rw [Finset.mem_range] at hk
    rw [he k (by omega)]
    exact hd _
  · rw [hrow, prod_tail e t l r hlr (fun k h1 h2 => hpt k h1 (by omega))]
  · rw [hLM l hl.le, hmono l hl.le (fun i => hσfirst _ i.isLt)]
  · rw [hLM (r + 1) le_rfl, hmono (r + 1) le_rfl (fun i => (σ _).isLt),
      prod_tail e t l (r + 1) hl.le (fun k h1 h2 => hpt k h1 h2)]

theorem norm_of_sq (τ : K →+* ℂ) {x y : K} (h : x ^ 2 = y ^ 2) : ‖τ x‖ = ‖τ y‖ := by
  have h1 : ‖τ x‖ ^ 2 = ‖τ y‖ ^ 2 := by rw [← norm_pow, ← map_pow, h, map_pow, norm_pow]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

theorem cell_minor_le {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (p : Point K (r + 1))
    (hp : IsInCell (ZhatOM Z) p) :
    ∃ (b₀ : Fin (r + 1)) (l : ℕ), l ≤ r ∧
      ((Z.submatrix Fin.castSucc id).submatrix id b₀.succAbove).det ≠ 0 ∧ ∀ τ : K →+* ℂ,
      ‖τ ((Z.submatrix Fin.castSucc id).submatrix id b₀.succAbove).det‖ ≤
        max ‖τ (leadMinorE Z l)‖ ‖τ (leadMinorE Z (r + 1))‖ := by
  obtain ⟨b₀, l, a, t, hl, ha, ht, h1, h2, h3⟩ := cell_minor Z p hp
  refine ⟨b₀, l, hl, ?_, fun τ => ?_⟩
  · intro h0
    have hnz : (a * t ^ (r - l)) ^ 2 ≠ 0 := pow_ne_zero _ (mul_ne_zero ha (pow_ne_zero _ ht))
    apply hnz
    rw [← h1, h0]
    ring
  · rw [norm_of_sq τ h1, norm_of_sq τ h2, norm_of_sq τ h3]
    simp only [map_mul, map_pow, norm_mul, norm_pow]
    rcases le_total ‖τ t‖ 1 with hT | hT
    · apply le_max_of_le_left
      exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hT)
    · apply le_max_of_le_right
      exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hT (by omega)) (norm_nonneg _)

end Alg

theorem lead_zequiv {E : Type} [Field E] {n : ℕ} {Z Z₂ : Matrix (Fin n) (Fin n) E} (h : ZEquiv Z Z₂) (l : ℕ) :
    leadMinorE Z₂ l = leadMinorE Z l := by
  obtain ⟨A, B, hA1, hA2, hB1, hB2, rfl⟩ := h
  apply lead_inv
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [Matrix.map_apply, hA1 i j hij]
    · subst hij
      simp [Matrix.map_apply, hA2]
  · intro i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · simp [Matrix.map_apply, hB1 i j hij]
    · subst hij
      simp [Matrix.map_apply, hB2]

theorem zequiv_refl {E : Type} [Field E] {n : ℕ} (Z : Matrix (Fin n) (Fin n) E) : ZEquiv Z Z := by
  refine ⟨1, 1, fun a b hab => Matrix.one_apply_ne (ne_of_lt hab), fun a => Matrix.one_apply_eq a,
    fun a b hab => Matrix.one_apply_ne (ne_of_gt hab), fun a => Matrix.one_apply_eq a, ?_⟩
  rw [Matrix.map_one _ (by simp) (by simp), Matrix.one_mul, Matrix.mul_one]

theorem one_le_prod'' {ι : Type} (s : Finset ι) (f : ι → ℝ) (h : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  exact Finset.prod_induction f (fun x => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl h

theorem frameExp_le (r l : ℕ) (hl : l ≤ r + 1) : 2 * frameExp r l ≤ (2 * r + 2) ^ 2 := by
  unfold frameExp
  have h1 : ∑ a ∈ Finset.Icc 1 l, (r + 1 - a) ≤ ∑ a ∈ Finset.Icc 1 l, (r + 1) :=
    Finset.sum_le_sum (fun a _ => Nat.sub_le _ _)
  rw [Finset.sum_const, Nat.card_Icc, smul_eq_mul, show l + 1 - 1 = l by omega] at h1
  have h3 : l * (r + 1) ≤ (r + 1) * (r + 1) := Nat.mul_le_mul_right _ hl
  nlinarith [h1, h3]

noncomputable def locSize (D : D7) (b C : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : ℝ :=
  ∏ l ∈ Finset.Icc 1 (D.R.rS + 1), max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))

theorem one_le_locSize (D : D7) (b C : ℝ) (Z : GramM D) (τ : D.what₂.Tau) : 1 ≤ locSize D b C Z τ := by
  unfold locSize
  exact GlobalTheory.LoopC.GramSize.one_le_prod'' _ _ (fun l _ => le_max_left _ _)

theorem lead_le (D : D7) (b C : ℝ) (hb : 1 ≤ b) (hC : 0 ≤ C) (hrd : D.host.rdE ≤ b) (Z : GramM D)
    (τ : D.what₂.Tau) (l : ℕ) (hl : l ≤ D.R.rS + 1) :
    ‖embS D τ (leadMinorE Z l)‖ ≤ b ^ ((C + 1) * (D.R.m : ℝ) ^ 2) * locSize D b C Z τ := by
  obtain ⟨-, -, -, hm, hrd1, -, -, -, -, -⟩ := GlobalTheory.real_places_facts D
  have hb0 : 0 < b := by linarith
  have hloc := one_le_locSize D b C Z τ
  have hB1 : 1 ≤ b ^ ((C + 1) * (D.R.m : ℝ) ^ 2) :=
    Real.one_le_rpow hb (mul_nonneg (by linarith) (sq_nonneg _))
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · have h1 : leadMinorE Z 0 = 1 := by
      unfold leadMinorE
      rw [dif_pos (Nat.zero_le _)]
      exact Matrix.det_isEmpty
    rw [h1, map_one, norm_one]
    nlinarith
  · have hmem : l ∈ Finset.Icc 1 (D.R.rS + 1) := Finset.mem_Icc.mpr ⟨hl0, hl⟩
    have hP0 : 0 < b ^ (C * (D.R.m : ℝ) ^ 2) := Real.rpow_pos_of_pos hb0 _
    have hfac : max 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)) ≤ locSize D b C Z τ := by
      unfold locSize
      rw [← Finset.mul_prod_erase _ _ hmem]
      have hrest : 1 ≤ ∏ x ∈ (Finset.Icc 1 (D.R.rS + 1)).erase l,
          max 1 (absDl D Z x τ / b ^ (C * (D.R.m : ℝ) ^ 2)) :=
        GlobalTheory.LoopC.GramSize.one_le_prod'' _ _ (fun _ _ => le_max_left _ _)
      have hm1 := le_max_left 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2))
      nlinarith
    have hA : absDl D Z l τ ≤ b ^ (C * (D.R.m : ℝ) ^ 2) * locSize D b C Z τ := by
      have h1 := (div_le_iff₀ hP0).mp (le_max_right 1 (absDl D Z l τ / b ^ (C * (D.R.m : ℝ) ^ 2)))
      nlinarith
    have hx : ‖embS D τ (leadMinorE Z l)‖ =
        absDl D Z l τ * D.host.rdE ^ (2 * (frameExp D.R.rS l : ℝ)) := by
      unfold absDl absReal
      rw [mul_assoc, ← Real.rpow_add (by linarith), neg_add_cancel, Real.rpow_zero, mul_one]
    have hs : D.host.rdE ^ (2 * (frameExp D.R.rS l : ℝ)) ≤ b ^ ((D.R.m : ℝ) ^ 2) := by
      calc D.host.rdE ^ (2 * (frameExp D.R.rS l : ℝ)) ≤ b ^ (2 * (frameExp D.R.rS l : ℝ)) :=
            Real.rpow_le_rpow (by linarith) hrd (by positivity)
        _ ≤ b ^ ((D.R.m : ℝ) ^ 2) := by
            apply Real.rpow_le_rpow_of_exponent_le hb
            have hfe := frameExp_le D.R.rS l hl
            rw [hm]
            exact_mod_cast hfe
    rw [hx]
    calc absDl D Z l τ * D.host.rdE ^ (2 * (frameExp D.R.rS l : ℝ))
        ≤ (b ^ (C * (D.R.m : ℝ) ^ 2) * locSize D b C Z τ) * b ^ ((D.R.m : ℝ) ^ 2) :=
          mul_le_mul hA hs (Real.rpow_nonneg (by linarith) _) (mul_nonneg hP0.le (by linarith))
      _ = b ^ ((C + 1) * (D.R.m : ℝ) ^ 2) * locSize D b C Z τ := by
          rw [add_mul, one_mul, Real.rpow_add hb0]
          ring

theorem prod_le_HH (D : D7) (b C x : ℝ) (hb : 1 ≤ b) (Z : GramM D) (hx : x ≤ 2 * C ^ 2 * (D.R.m : ℝ) ^ 3)
    (X : D.what₂.Tau → ℝ) (h0 : ∀ τ, 0 ≤ X τ) (h : ∀ τ, X τ ≤ b ^ x * locSize D b C Z τ ^ 2) :
    ∏ τ, X τ ≤ HHZ D b C Z ^ 2 := by
  obtain ⟨hcard, -, -, -, -, -, -, -, -, -⟩ := GlobalTheory.real_places_facts D
  have hb0 : 0 < b := by linarith
  have hS : 1 ≤ sizeZ D b C Z := by
    unfold sizeZ
    exact GlobalTheory.LoopC.GramSize.one_le_prod'' _ _ (fun τ _ => one_le_locSize D b C Z τ)
  have hsz : sizeZ D b C Z = ∏ τ, locSize D b C Z τ := rfl
  calc ∏ τ, X τ ≤ ∏ τ, (b ^ x * locSize D b C Z τ ^ 2) :=
        Finset.prod_le_prod (fun τ _ => h0 τ) (fun τ _ => h τ)
    _ = b ^ (x * D.R.f) * sizeZ D b C Z ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, hcard, Finset.prod_pow, ← hsz,
          ← Real.rpow_natCast (b ^ x) D.R.f, ← Real.rpow_mul hb0.le]
    _ ≤ b ^ (2 * C ^ 2 * (D.R.m : ℝ) ^ 3 * D.R.f) * sizeZ D b C Z ^ 8 := by
        apply mul_le_mul (Real.rpow_le_rpow_of_exponent_le hb
          (mul_le_mul_of_nonneg_right hx (Nat.cast_nonneg _)))
          (pow_le_pow_right₀ hS (by norm_num)) (by positivity) (Real.rpow_pos_of_pos hb0 _).le
    _ = HHZ D b C Z ^ 2 := by
        unfold HHZ
        rw [mul_pow, ← Real.rpow_mul hb0.le,
          ← Real.rpow_natCast (b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f * (C * (D.R.m : ℝ)))) 2,
          ← Real.rpow_mul hb0.le, ← pow_mul]
        congr 1
        congr 1
        push_cast
        ring

private theorem exists_ne_zero_smul_mem_of_mem_span' (C CT m : ℝ) (hC : 2 * |CT| + 3 ≤ C) (hm : 1 ≤ m) :
    2 * ((C + 1) * m ^ 2) + 4 * |CT| * m ≤ 2 * C ^ 2 * m ^ 3 := by
  have ha := abs_nonneg CT
  have hm2 : m ≤ m ^ 2 := by nlinarith
  have hm3 : m ^ 2 ≤ m ^ 3 := by nlinarith
  have h1 : 2 * (C + 1) + 4 * |CT| ≤ 2 * C ^ 2 := by nlinarith
  calc 2 * ((C + 1) * m ^ 2) + 4 * |CT| * m ≤ 2 * (C + 1) * m ^ 2 + 4 * |CT| * m ^ 2 := by nlinarith
    _ = (2 * (C + 1) + 4 * |CT|) * m ^ 2 := by ring
    _ ≤ 2 * C ^ 2 * m ^ 2 := by nlinarith
    _ ≤ 2 * C ^ 2 * m ^ 3 := by nlinarith

private theorem main_lemma_2 {b : ℝ} (hb : 1 ≤ b) (y : ℝ) : (b ^ y) ^ 2 = b ^ (2 * y) := by
  rw [sq, ← Real.rpow_add (by linarith : (0 : ℝ) < b), two_mul]

theorem main : ∀ Cg cb Cu cT CT C0 A : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∀ (D : D7) (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl : ℝ), 1 ≤ Cl → Hyp D large₂ u u' C' Cl Cg cb Cu cT CT C0 A → ∀ (F0 : Fb D u) (Λ : LatV D), IsBase D u F0 → IsRowLat D F0 Λ → ∀ (Z : GramM D) (F' : FlagU D u'), RelZ D Z → IsTermF D Λ (lf D F0) F' → ZEquiv (ZhatL (lf D F0) F') Z → ∃ Z₁, ZEquiv Z Z₁ ∧ QOK D u u' Z₁ (HHZ D large₂.sc.b C Z ^ 2) := by
  intro Cg cb Cu cT CT C0 A
  refine ⟨2 * |CT| + 3, ?_⟩
  intro C hC D large₂ u u' C' Cl hCl hH F0 Λ _ _ Z F' hRel hT hZ
  obtain ⟨-, -, -, hm, hrd1, hstar, -⟩ := GlobalTheory.real_places_facts D
  obtain ⟨⟨hS0, -, -⟩, hSt, -⟩ := hH
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hlog, -, -, -, -, -, -, -, -, -, -, -, hTr, -, -⟩ := hS0
  obtain ⟨-, -, -, hT3, hT3', -⟩ := hSt
  obtain ⟨⟨-, -, hG0⟩, -⟩ := hT
  have hCa : 0 ≤ |CT| := abs_nonneg CT
  have hC0 : 0 ≤ C := by linarith
  have hL0 : 0 ≤ large₂.sc.L := Real.rpow_nonneg (by linarith [large₂.sc.one_lt_alt]) _
  have hb1 : 1 ≤ large₂.sc.b := Real.one_le_exp hL0
  have hb0 : (0 : ℝ) ≤ large₂.sc.b := by linarith
  have hrdb : D.host.rdE ≤ large₂.sc.b := by
    have h0 : 0 < D.host.rdE := by linarith
    have h1 : Real.log D.host.rdE ≤ large₂.sc.L := le_trans hlog (div_le_self hL0 hCl)
    exact (Real.log_le_iff_le_exp h0).1 h1
  have hmN : 1 ≤ D.R.m := by omega
  have hm1 : (1 : ℝ) ≤ (D.R.m : ℝ) := by exact_mod_cast hmN
  have hmr : 2 * (D.R.rS : ℝ) ≤ (D.R.m : ℝ) := by
    have : 2 * D.R.rS ≤ D.R.m := by omega
    exact_mod_cast this
  have hsz : 1 ≤ sizeZ D large₂.sc.b C Z :=
    one_le_prod'' Finset.univ (fun τ => locSize D large₂.sc.b C Z τ) (fun τ _ => one_le_locSize D _ _ Z τ)
  have hHb : 1 ≤ (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) :=
    Real.one_le_rpow (Real.one_le_rpow hb1 (by positivity)) (by positivity)
  have hHH : 1 ≤ HHZ D large₂.sc.b C Z := one_le_mul_of_one_le_of_one_le hHb (one_le_pow₀ hsz)
  have hHH2 : HHZ D large₂.sc.b C Z ≤ HHZ D large₂.sc.b C Z ^ 2 := le_self_pow₀ hHH (by norm_num)
  have hB : ∀ τ l, l ≤ D.R.rS + 1 → ‖embS D τ (leadMinorE Z l)‖ ≤
      large₂.sc.b ^ ((C + 1) * (D.R.m : ℝ) ^ 2) * locSize D large₂.sc.b C Z τ :=
    fun τ l hl => lead_le D large₂.sc.b C hb1 hC0 hrdb Z τ l hl
  have hx := exists_ne_zero_smul_mem_of_mem_span' C CT (D.R.m : ℝ) hC hm1
  refine ⟨Z, zequiv_refl Z, one_le_pow₀ hHH, ?_, ?_, ?_, ?_⟩
  ·
    have e1 : D.host.rdE ^ (2 * D.R.f * D.R.rS) ≤ large₂.sc.b ^ ((2 * D.R.f * D.R.rS : ℕ) : ℝ) := by
      rw [Real.rpow_natCast]
      exact pow_le_pow_left₀ (by linarith) hrdb _
    have e2 : large₂.sc.b ^ ((2 * D.R.f * D.R.rS : ℕ) : ℝ) ≤
        (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) := by
      rw [← Real.rpow_mul hb0]
      apply Real.rpow_le_rpow_of_exponent_le hb1
      have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
      have hC2 : 1 ≤ C ^ 2 := by nlinarith
      have hm3' : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 3 := by nlinarith
      have hm3 : (D.R.m : ℝ) ≤ C ^ 2 * (D.R.m : ℝ) ^ 3 := by
        nlinarith [mul_le_mul_of_nonneg_right hC2 (by positivity : (0 : ℝ) ≤ (D.R.m : ℝ) ^ 3)]
      push_cast
      nlinarith [mul_le_mul_of_nonneg_right hmr hf, mul_le_mul_of_nonneg_right hm3 hf]
    have e3 : (large₂.sc.b ^ (C * (D.R.m : ℝ) ^ 2 * D.R.f)) ^ (C * (D.R.m : ℝ)) ≤ HHZ D large₂.sc.b C Z := by
      unfold HHZ
      exact le_mul_of_one_le_right (by linarith) (one_le_pow₀ hsz)
    exact e1.trans (e2.trans (e3.trans hHH2))
  ·
    obtain ⟨p, hp⟩ := hRel
    obtain ⟨b₀, l, hl, hne, hle⟩ := cell_minor_le Z p hp
    refine ⟨b₀, hne, ?_⟩
    refine prod_le_HH D large₂.sc.b C (2 * ((C + 1) * (D.R.m : ℝ) ^ 2)) hb1 Z
      (by have hcm := mul_nonneg hCa (le_trans zero_le_one hm1); linarith)
      (fun τ => ‖embS D τ (rowMinor D Z b₀)‖ ^ 2) (fun τ => by positivity) (fun τ => ?_)
    have h1 : ‖embS D τ (rowMinor D Z b₀)‖ ≤
        large₂.sc.b ^ ((C + 1) * (D.R.m : ℝ) ^ 2) * locSize D large₂.sc.b C Z τ :=
      (hle (embS D τ)).trans (max_le (hB τ l (by omega)) (hB τ _ le_rfl))
    calc ‖embS D τ (rowMinor D Z b₀)‖ ^ 2
        ≤ (large₂.sc.b ^ ((C + 1) * (D.R.m : ℝ) ^ 2) * locSize D large₂.sc.b C Z τ) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = large₂.sc.b ^ (2 * ((C + 1) * (D.R.m : ℝ) ^ 2)) * locSize D large₂.sc.b C Z τ ^ 2 := by
          rw [mul_pow, main_lemma_2 hb1]
  ·
    unfold Gmat
    rw [lead_zequiv hZ, lead_zequiv hZ]
    exact hG0
  ·
    have hTu : ∀ v : D.what₂.Word, (3 : ℝ) ≤ (Tu D v : ℝ) → (Tu D v : ℝ) ≤ large₂.sc.b ^ (|CT| * (D.R.m : ℝ)) := by
      intro v _
      refine le_trans (hTr v).2 (Real.rpow_le_rpow_of_exponent_le hb1 ?_)
      exact mul_le_mul_of_nonneg_right (le_abs_self CT) (by positivity)
    have t1 : (3 : ℝ) ≤ (Tu D u : ℝ) := by exact_mod_cast hT3
    have t2 : (3 : ℝ) ≤ (Tu D u' : ℝ) := by exact_mod_cast hT3'
    have hT1 := hTu u t1
    have hT2 := hTu u' t2
    refine prod_le_HH D large₂.sc.b C (2 * ((C + 1) * (D.R.m : ℝ) ^ 2) + 4 * |CT| * (D.R.m : ℝ)) hb1 Z hx
      (fun τ => ‖embS D τ (Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z)‖)
      (fun τ => norm_nonneg _) (fun τ => ?_)
    set B := large₂.sc.b ^ ((C + 1) * (D.R.m : ℝ) ^ 2) * locSize D large₂.sc.b C Z τ with hBdef
    have h1 := hB τ (D.R.rS + 1) le_rfl
    have h2 := hB τ D.R.rS (by omega)
    have hst : ∀ a : D.host.E, ‖embS D τ (star a)‖ = ‖embS D τ a‖ := fun a => by
      rw [hstar, Complex.norm_conj]
    have hG : ‖embS D τ (Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z)‖ ≤
        ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ * ‖embS D τ (leadMinorE Z (D.R.rS + 1))‖ +
        ((Tu D u : ℝ) * (Tu D u' : ℝ)) *
          (‖embS D τ (leadMinorE Z D.R.rS)‖ * ‖embS D τ (leadMinorE Z D.R.rS)‖) := by
      unfold Gmat
      simp only [map_sub, map_mul]
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, map_natCast, Complex.norm_natCast, hst, le_refl]
    have hn1 := norm_nonneg (embS D τ (leadMinorE Z (D.R.rS + 1)))
    have hn2 := norm_nonneg (embS D τ (leadMinorE Z D.R.rS))
    have hTT : (1 : ℝ) + (Tu D u : ℝ) * (Tu D u' : ℝ) ≤ ((Tu D u : ℝ) * (Tu D u' : ℝ)) ^ 2 := by
      have h9 : (9 : ℝ) ≤ (Tu D u : ℝ) * (Tu D u' : ℝ) := by
        nlinarith [mul_le_mul t1 t2 (by norm_num) (by linarith)]
      nlinarith [h9]
    have hTT2 : ((Tu D u : ℝ) * (Tu D u' : ℝ)) ^ 2 ≤ large₂.sc.b ^ (4 * |CT| * (D.R.m : ℝ)) := by
      have e : large₂.sc.b ^ (4 * |CT| * (D.R.m : ℝ)) = ((large₂.sc.b ^ (|CT| * (D.R.m : ℝ))) ^ 2) ^ 2 := by
        rw [main_lemma_2 hb1, main_lemma_2 hb1]; ring_nf
      rw [e]
      have hp : 0 ≤ (Tu D u : ℝ) * (Tu D u' : ℝ) := by positivity
      refine pow_le_pow_left₀ hp ?_ 2
      rw [sq]
      exact mul_le_mul hT1 hT2 (by positivity) (by positivity)
    have hB0 : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hb0 _) (le_trans zero_le_one (one_le_locSize D _ _ Z τ))
    calc ‖embS D τ (Gmat D ((Tu D u : ℕ) : D.host.E) ((Tu D u' : ℕ) : D.host.E) Z)‖
        ≤ B * B + ((Tu D u : ℝ) * (Tu D u' : ℝ)) * (B * B) := by
          refine hG.trans (add_le_add (mul_le_mul h1 h1 hn1 hB0) ?_)
          exact mul_le_mul_of_nonneg_left (mul_le_mul h2 h2 hn2 hB0) (by positivity)
      _ = (1 + (Tu D u : ℝ) * (Tu D u' : ℝ)) * B ^ 2 := by ring
      _ ≤ large₂.sc.b ^ (4 * |CT| * (D.R.m : ℝ)) * B ^ 2 :=
          mul_le_mul_of_nonneg_right (hTT.trans hTT2) (by positivity)
      _ = large₂.sc.b ^ (2 * ((C + 1) * (D.R.m : ℝ) ^ 2) + 4 * |CT| * (D.R.m : ℝ)) *
            locSize D large₂.sc.b C Z τ ^ 2 := by
          rw [hBdef, mul_pow, main_lemma_2 hb1, ← mul_assoc, ← Real.rpow_add (by linarith), add_comm]

end GlobalTheory.LoopC.GramSize
