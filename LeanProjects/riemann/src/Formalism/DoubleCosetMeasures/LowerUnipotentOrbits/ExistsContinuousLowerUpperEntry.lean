import Formalism.DoubleCosetMeasures.Statement

noncomputable section

open Matrix Topology

namespace Formalism.DoubleCosetMeasures.P

namespace Supp

section LU

variable {K : Type} [CommRing K] {n : ℕ}

theorem lu_entry (h u : Matrix (Fin n) (Fin n) K) (hh : IsLowUni h) (hu : IsUpUni u)
    (i j : Fin n) :
    (h * u) i j = (∑ k, if k < i ∧ k < j then h i k * u k j else 0) + (h + u - 1) i j := by
  have hL : ∀ a b : Fin n, a < b → h a b = 0 := fun a b hab => hh.1 (OrderDual.toDual_lt_toDual.mpr hab)
  have hU : ∀ a b : Fin n, b < a → u a b = 0 := fun a b hab => hu.1 hab
  have key : ∀ k, h i k * u k j = (if k < i ∧ k < j then h i k * u k j else 0) +
      (if k = min i j then (h + u - 1) i j else 0) := by
    intro k
    rcases lt_trichotomy k (min i j) with hk | hk | hk
    · rw [if_pos (lt_min_iff.mp hk), if_neg hk.ne, add_zero]
    · have hn : ¬ (k < i ∧ k < j) := fun hk' => (lt_min hk'.1 hk'.2).ne hk
      rw [if_neg hn, if_pos hk, zero_add, hk]
      simp only [Matrix.sub_apply, Matrix.add_apply]
      rcases lt_trichotomy i j with hij | rfl | hij
      · rw [min_eq_left hij.le, hh.2, hL i j hij, Matrix.one_apply_ne hij.ne]; ring
      · rw [min_self, hh.2, hu.2, Matrix.one_apply_eq]; ring
      · rw [min_eq_right hij.le, hu.2, hU i j hij, Matrix.one_apply_ne hij.ne']; ring
    · have hn : ¬ (k < i ∧ k < j) := fun hk' => lt_asymm (lt_min hk'.1 hk'.2) hk
      rw [if_neg hn, if_neg hk.ne', add_zero]
      rcases min_lt_iff.mp hk with hik | hjk
      · rw [hL i k hik, zero_mul]
      · rw [hU k j hjk, mul_zero]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun k _ => key k), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable [TopologicalSpace K] [IsTopologicalRing K]

theorem exists_continuous_lowerUpper_entry (m : ℕ) : ∃ E : Fin n → Fin n → Matrix (Fin n) (Fin n) K → K,
    (∀ i j, Continuous (E i j)) ∧ ∀ i j, (min i j).val < m → ∀ h u : Matrix (Fin n) (Fin n) K,
      IsLowUni h → IsUpUni u → E i j (h * u) = (h + u - 1) i j := by
  induction m with
  | zero => exact ⟨fun _ _ _ => 0, fun _ _ => continuous_const, fun i j h => absurd h (Nat.not_lt_zero _)⟩
  | succ m ih =>
    obtain ⟨E, hEc, hE⟩ := ih
    refine ⟨fun i j => if (min i j).val < m then E i j else
      fun M => M i j - ∑ k, if k < i ∧ k < j then E i k M * E k j M else 0, ?_, ?_⟩
    · intro i j
      by_cases hm : (min i j).val < m
      · simp only [hm, if_true]; exact hEc i j
      · simp only [hm, if_false]
        refine (continuous_id.matrix_elem i j).sub (continuous_finsetSum _ fun k _ => ?_)
        by_cases hk : k < i ∧ k < j
        · simp only [hk, and_self, if_true]; exact (hEc i k).mul (hEc k j)
        · simp only [hk, if_false]; exact continuous_const
    · intro i j hij h u hh hu
      have hL : ∀ a b : Fin n, a < b → h a b = 0 := fun a b hab => hh.1 (OrderDual.toDual_lt_toDual.mpr hab)
      have hU : ∀ a b : Fin n, b < a → u a b = 0 := fun a b hab => hu.1 hab
      by_cases hm : (min i j).val < m
      · simp only [hm, if_true]; exact hE i j hm h u hh hu
      · simp only [hm, if_false]
        rw [lu_entry h u hh hu i j]
        have hs : ∀ k, (if k < i ∧ k < j then E i k (h * u) * E k j (h * u) else 0) =
            (if k < i ∧ k < j then h i k * u k j else 0) := by
          intro k
          by_cases hk : k < i ∧ k < j
          · have hkm : k.val < m := by
              have h1 : k < min i j := lt_min hk.1 hk.2
              have h2 : (k : ℕ) < (min i j : Fin n) := h1
              omega
            have hki : (min i k).val < m := by rw [min_eq_right hk.1.le]; exact hkm
            have hkj : (min k j).val < m := by rw [min_eq_left hk.2.le]; exact hkm
            rw [if_pos hk, if_pos hk, hE i k hki h u hh hu, hE k j hkj h u hh hu]
            rw [Matrix.sub_apply, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply, hU i k hk.1,
              hL k j hk.2, Matrix.one_apply_ne hk.1.ne', Matrix.one_apply_ne hk.2.ne]
            ring
          · rw [if_neg hk, if_neg hk]
        rw [Finset.sum_congr rfl (fun k _ => hs k)]
        ring

theorem lu_rec : ∃ Ph Pu : Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K,
    Continuous Ph ∧ Continuous Pu ∧
      ∀ h u, IsLowUni h → IsUpUni u → Ph (h * u) = h ∧ Pu (h * u) = u := by
  obtain ⟨E, hEc, hE⟩ := exists_continuous_lowerUpper_entry (K := K) (n := n) n
  refine ⟨fun M i j => if j < i then E i j M else if i = j then 1 else 0,
    fun M i j => if i < j then E i j M else if i = j then 1 else 0, ?_, ?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h1 : j < i
    · simp only [h1, if_true]; exact hEc i j
    · simp only [h1, if_false]; exact continuous_const
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    by_cases h1 : i < j
    · simp only [h1, if_true]; exact hEc i j
    · simp only [h1, if_false]; exact continuous_const
  · intro h u hh hu
    have hL : ∀ a b : Fin n, a < b → h a b = 0 := fun a b hab => hh.1 (OrderDual.toDual_lt_toDual.mpr hab)
    have hU : ∀ a b : Fin n, b < a → u a b = 0 := fun a b hab => hu.1 hab
    have hall : ∀ i j, E i j (h * u) = (h + u - 1) i j := fun i j => hE i j (min i j).isLt h u hh hu
    constructor
    · ext i j
      simp only [hall, Matrix.sub_apply, Matrix.add_apply]
      split_ifs with h1 h2
      · rw [hU i j h1, Matrix.one_apply_ne h1.ne']; ring
      · subst h2; rw [hh.2]
      · rw [hL i j (lt_of_le_of_ne (not_lt.mp h1) h2)]
    · ext i j
      simp only [hall, Matrix.sub_apply, Matrix.add_apply]
      split_ifs with h1 h2
      · rw [hL i j h1, Matrix.one_apply_ne h1.ne]; ring
      · subst h2; rw [hu.2]
      · rw [hU i j (lt_of_le_of_ne (not_lt.mp h1) (Ne.symm h2))]

end LU

section Pt

theorem revIn_lt : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s j < s.sum
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [List.sum_cons] at h ⊢
    by_cases hj : j < a
    · simp only [revIn, hj, if_true]; omega
    · simp only [revIn, hj, if_false]
      have := revIn_lt s (j - a) (by omega); omega

theorem revIn_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → revIn s (revIn s j) = j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < a
    · have e : revIn (a :: s) j = a - 1 - j := by simp [revIn, hj]
      rw [e]
      have h1 : a - 1 - j < a := by omega
      simp only [revIn, h1, if_true]; omega
    · have e : revIn (a :: s) j = a + revIn s (j - a) := by simp [revIn, hj]
      rw [e]
      have h1 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [revIn, h1, if_false, Nat.add_sub_cancel_left]
      rw [revIn_revIn s (j - a) (by omega)]; omega

theorem blk_revIn : ∀ (s : List ℕ) (j : ℕ), j < s.sum → blk s (revIn s j) = blk s j
  | [], j, h => by simp at h
  | a :: s, j, h => by
    simp only [List.sum_cons] at h
    by_cases hj : j < a
    · have e : revIn (a :: s) j = a - 1 - j := by simp [revIn, hj]
      rw [e]
      have h1 : a - 1 - j < a := by omega
      simp only [blk, h1, hj, if_true]
    · have e : revIn (a :: s) j = a + revIn s (j - a) := by simp [revIn, hj]
      rw [e]
      have h1 : ¬ (a + revIn s (j - a) < a) := by omega
      simp only [blk, h1, hj, if_false, Nat.add_sub_cancel_left]
      rw [blk_revIn s (j - a) (by omega)]

theorem pt_mul_pt {K : Type} [CommRing K] (s : List ℕ) (t t' : ℕ → Kˣ)
    (htt : ∀ b, ((t b : Kˣ) : K) * ((t' b : Kˣ) : K) = 1) : pt s t * pt s t' = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have ha := revIn_lt s a a.isLt
  have hrr : revIn s (revIn s a) = a := revIn_revIn s a a.isLt
  have hbb : blk s (revIn s a) = blk s a := blk_revIn s a a.isLt
  rw [Finset.sum_eq_single ⟨revIn s a, ha⟩]
  · simp only [pt, hrr, hbb, if_true]
    by_cases hab : a = b
    · subst hab; simp [htt]
    · have hne : (b : ℕ) ≠ a := fun e => hab (Fin.ext e.symm)
      simp [hab, hne]
  · intro c _ hc
    simp only [pt]
    rw [if_neg (fun e => hc (Fin.ext e)), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end Pt

section Closed

variable {K : Type} [CommRing K] [TopologicalSpace K] [T2Space K] {n : ℕ}

theorem isClosed_lowUni : IsClosed {x : Matrix (Fin n) (Fin n) K | IsLowUni x} := by
  have hset : {x : Matrix (Fin n) (Fin n) K | IsLowUni x} =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : i < j), {x | x i j = 0}) ∩ ⋂ a : Fin n, {x | x a a = 1} := by
    ext x
    simp only [IsLowUni, Matrix.IsLowerTriangular, Matrix.BlockTriangular, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_iInter, OrderDual.toDual_lt_toDual]
  rw [hset]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)

theorem isClosed_upUni : IsClosed {x : Matrix (Fin n) (Fin n) K | IsUpUni x} := by
  have hset : {x : Matrix (Fin n) (Fin n) K | IsUpUni x} =
      (⋂ i : Fin n, ⋂ j : Fin n, ⋂ (_ : j < i), {x | x i j = 0}) ∩ ⋂ a : Fin n, {x | x a a = 1} := by
    ext x
    simp only [IsUpUni, Matrix.IsUpperTriangular, Matrix.BlockTriangular, Set.mem_ofPred_eq,
      Set.mem_inter_iff, Set.mem_iInter, id]
  rw [hset]
  exact (isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
    isClosed_eq (continuous_id.matrix_elem i j) continuous_const).inter
    (isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_elem a a) continuous_const)

end Closed

theorem mem_lowW_iff {K : Type} [CommRing K] (s : List ℕ) (t : ℕ → Kˣ)
    (wi : Matrix (Fin s.sum) (Fin s.sum) K) (h1 : wi * pt s t = 1) (h2 : pt s t * wi = 1)
    (g : GL (Fin s.sum) K) :
    g ∈ lowW K s t ↔ IsLowUni (g : Matrix (Fin s.sum) (Fin s.sum) K) ∧
      IsLowUni (wi * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) := by
  show (IsLowUni (g : Matrix (Fin s.sum) (Fin s.sum) K) ∧ ∃ h : Matrix (Fin s.sum) (Fin s.sum) K, IsLowUni h ∧
    (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t = pt s t * h) ↔ _
  constructor
  · rintro ⟨hg, h, hh, he⟩
    refine ⟨hg, ?_⟩
    have hw : wi * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t = h := by
      rw [Matrix.mul_assoc, he, ← Matrix.mul_assoc, h1, Matrix.one_mul]
    rw [hw]; exact hh
  · rintro ⟨hg, hh⟩
    refine ⟨hg, _, hh, ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h2, Matrix.one_mul]

theorem isClosed_lowW {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (s : List ℕ) (t : ℕ → Kˣ) (wi : Matrix (Fin s.sum) (Fin s.sum) K)
    (h1 : wi * pt s t = 1) (h2 : pt s t * wi = 1) :
    IsClosed (lowW K s t : Set (GL (Fin s.sum) K)) := by
  have hset : (lowW K s t : Set (GL (Fin s.sum) K)) =
      (fun g : GL (Fin s.sum) K => (g : Matrix (Fin s.sum) (Fin s.sum) K)) ⁻¹' {x | IsLowUni x} ∩
      (fun g : GL (Fin s.sum) K => wi * (g : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t) ⁻¹'
        {x | IsLowUni x} := by
    ext g; exact mem_lowW_iff s t wi h1 h2 g
  rw [hset]
  exact (isClosed_lowUni.preimage Units.continuous_val).inter (isClosed_lowUni.preimage
    ((continuous_const.matrix_mul Units.continuous_val).matrix_mul continuous_const))

theorem isClosed_upUniG {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    [T2Space K] (n : ℕ) : IsClosed (upUniG K n : Set (GL (Fin n) K)) := by
  have hset : (upUniG K n : Set (GL (Fin n) K)) =
      (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K)) ⁻¹' {x | IsUpUni x} := by
    ext g; exact Iff.rfl
  rw [hset]
  exact isClosed_upUni.preimage Units.continuous_val

theorem coe_inv_of_det {K : Type} [CommRing K] {n : ℕ} (g : GL (Fin n) K)
    (hg : (g : Matrix (Fin n) (Fin n) K).det = 1) :
    ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = (g : Matrix (Fin n) (Fin n) K).adjugate := by
  rw [Matrix.coe_units_inv, Matrix.inv_def, hg, Ring.inverse_one, one_smul]

end Supp

open Supp in

theorem suppCompact : Formalism.DoubleCosetMeasures.SuppCompact := by
  intro K _ _ _ _ R hRo hRc s t ψ C _ _ e lam
  let P := pt s t
  let P' := pt s (fun b => (t b)⁻¹)
  have hPP' : P * P' = 1 := pt_mul_pt s t _ (fun b => Units.mul_inv (t b))
  have hP'P : P' * P = 1 := pt_mul_pt s _ t (fun b => Units.inv_mul (t b))
  obtain ⟨Ph, Pu, hPhc, hPuc, hPhu⟩ := lu_rec (K := K) (n := s.sum)
  let G : Matrix (Fin s.sum) (Fin s.sum) K → Matrix (Fin s.sum) (Fin s.sum) K :=
    fun M => P * Ph (P' * M) * P'
  let U : Matrix (Fin s.sum) (Fin s.sum) K → Matrix (Fin s.sum) (Fin s.sum) K :=
    fun M => Pu (P' * M)
  have hGc : Continuous G := (continuous_const.matrix_mul
    (hPhc.comp (continuous_const.matrix_mul continuous_id))).matrix_mul continuous_const
  have hUc : Continuous U := hPuc.comp (continuous_const.matrix_mul continuous_id)
  let D : Set (Matrix (Fin s.sum) (Fin s.sum) K) := {M | IsInt R M} ∩
    ({M | IsLowUni (G M)} ∩ {M | IsLowUni (P' * G M * P)} ∩ {M | IsUpUni (U M)})
  have hIntc : IsCompact {M : Matrix (Fin s.sum) (Fin s.sum) K | IsInt R M} := by
    have hset : {M : Matrix (Fin s.sum) (Fin s.sum) K | IsInt R M} =
        Set.univ.pi fun _ => Set.univ.pi fun _ => (R : Set K) := by
      ext M
      exact ⟨fun h a _ b _ => h a b, fun h a b => h a trivial b trivial⟩
    rw [hset]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hRc
  have hDc : IsCompact D := hIntc.inter_right
    (((isClosed_lowUni.preimage hGc).inter (isClosed_lowUni.preimage
      ((continuous_const.matrix_mul hGc).matrix_mul continuous_const))).inter
      (isClosed_upUni.preimage hUc))
  have hGdet : ∀ M ∈ D, (G M).det = 1 := fun M hM => isLowUni_det K hM.2.1.1
  have hUdet : ∀ M ∈ D, (U M).det = 1 := fun M hM => isUpUni_det K hM.2.2
  let gU : D → GL (Fin s.sum) K := fun M => ⟨G M.1, (G M.1).adjugate,
    by rw [Matrix.mul_adjugate, hGdet M.1 M.2, one_smul],
    by rw [Matrix.adjugate_mul, hGdet M.1 M.2, one_smul]⟩
  let uU : D → GL (Fin s.sum) K := fun M => ⟨U M.1, (U M.1).adjugate,
    by rw [Matrix.mul_adjugate, hUdet M.1 M.2, one_smul],
    by rw [Matrix.adjugate_mul, hUdet M.1 M.2, one_smul]⟩
  have hgU : Continuous gU := Units.continuous_iff.mpr
    ⟨hGc.comp continuous_subtype_val, (hGc.comp continuous_subtype_val).matrix_adjugate⟩
  have huU : Continuous uU := Units.continuous_iff.mpr
    ⟨hUc.comp continuous_subtype_val, (hUc.comp continuous_subtype_val).matrix_adjugate⟩
  have hgmem : ∀ M : D, gU M ∈ lowW K s t := fun M =>
    (mem_lowW_iff s t P' hP'P hPP' (gU M)).mpr ⟨M.2.2.1.1, M.2.2.1.2⟩
  have humem : ∀ M : D, uU M ∈ upUniG K s.sum := fun M => M.2.2.2
  let F : D → lowW K s t × upUniG K s.sum := fun M => (⟨gU M, hgmem M⟩, ⟨uU M, humem M⟩)
  have hF : Continuous F := (hgU.subtype_mk hgmem).prodMk (huU.subtype_mk humem)
  have : CompactSpace D := isCompact_iff_compactSpace.mp hDc
  refine HasCompactSupport.intro (isCompact_range hF) ?_
  intro p hp
  have hnot : ¬ IsInt R (((p.1 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K) * pt s t *
      ((p.2 : GL (Fin s.sum) K) : Matrix (Fin s.sum) (Fin s.sum) K)) := by
    intro hInt
    rcases p with ⟨⟨g, hg⟩, ⟨u, hu⟩⟩
    apply hp
    let gm : Matrix (Fin s.sum) (Fin s.sum) K := g
    let um : Matrix (Fin s.sum) (Fin s.sum) K := u
    obtain ⟨hgl, hhl⟩ := (mem_lowW_iff s t P' hP'P hPP' g).mp hg
    have hu' : IsUpUni um := hu
    have hM : P' * (gm * P * um) = (P' * gm * P) * um := by
      simp only [Matrix.mul_assoc]
    obtain ⟨hPh, hPu⟩ := hPhu _ _ hhl hu'
    have hGM : G (gm * P * um) = g := by
      show P * Ph (P' * (gm * P * um)) * P' = g
      rw [hM, hPh]
      simp only [Matrix.mul_assoc]
      rw [hPP', Matrix.mul_one, ← Matrix.mul_assoc, hPP', Matrix.one_mul]
    have hUM : U (gm * P * um) = u := by
      show Pu (P' * (gm * P * um)) = u
      rw [hM, hPu]
    have hMD : gm * P * um ∈ D :=
      ⟨hInt, ⟨⟨by rw [Set.mem_ofPred_eq, hGM]; exact hgl, by rw [Set.mem_ofPred_eq, hGM]; exact hhl⟩,
        by rw [Set.mem_ofPred_eq, hUM]; exact hu'⟩⟩
    exact ⟨⟨_, hMD⟩, Prod.ext (Subtype.ext (Units.ext hGM)) (Subtype.ext (Units.ext hUM))⟩
  rw [phi, if_neg hnot, zero_mul]

end Formalism.DoubleCosetMeasures.P
