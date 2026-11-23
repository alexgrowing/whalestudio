import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EaGeCOfNorm

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

section Idx

variable {n' ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

theorem ea_eS_val (s : Fin n') : (ea_eS hn s).val = s.val := by
  show (((s.val : ℕ) : ZMod (2 * ν))).val = s.val
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hn ▸ s.isLt)]

theorem ea_eS_symm_val (x : ZMod (2 * ν)) : ((ea_eS hn).symm x).val = x.val := rfl

theorem ea_eS_posAdd (s : Fin n') (k : ℕ) : ea_eS hn (posAdd s k) = ea_eS hn s + (k : ZMod (2 * ν)) := by
  subst hn
  show (((s.val + k) % (2 * ν) : ℕ) : ZMod (2 * ν)) = (s.val : ZMod (2 * ν)) + k
  rw [ZMod.natCast_mod, Nat.cast_add]

theorem ea_eS_sub_val (s s' : Fin n') : (ea_eS hn s' - ea_eS hn s).val = (s'.val + n' - s.val) % n' := by
  subst hn
  have hle : s.val ≤ s'.val + 2 * ν := by have := s.isLt; omega
  show (((s'.val : ℕ) : ZMod (2 * ν)) - ((s.val : ℕ) : ZMod (2 * ν))).val = _
  rw [← ZMod.val_natCast (n := 2 * ν) (s'.val + 2 * ν - s.val)]
  congr 1
  rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_self, add_zero]

end Idx

theorem ea_card_fin (N : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun c : Fin N => P c.val).card = ((range N).filter P).card := by
  rw [← Finset.card_map Fin.valEmbedding]
  congr 1
  ext x
  simp only [mem_map, mem_filter, mem_univ, true_and, Fin.valEmbedding_apply, mem_range]
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.isLt, hc⟩
  · rintro ⟨hx, hP⟩
    exact ⟨⟨x, hx⟩, hP, rfl⟩

theorem ea_lg (p x : ℕ) : Formalism.InvariantFactorPaths.G7.lgN p x = lgp p (x : ℤ) := by
  unfold Formalism.InvariantFactorPaths.G7.lgN lgp
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [if_neg (by omega), if_neg (by omega)]
    simp

section Num

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ} {ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

def ea_cN (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (J : ℕ) (s : ZMod (2 * ν)) : ℕ :=
  (nu t lam0 w J ((ea_eS hn).symm s) 1).toNat

def ea_hT (t : ℕ) (lam0 : Fin n' → Fin (k1 + 1) → ℤ) (w : ℕ → Fin n' → ℤ) (J : ℕ) (s : ZMod (2 * ν))
    (x : Fin (ea_cN hn t lam0 w J s)) : ℕ := ea_colH t lam0 w J ((ea_eS hn).symm s) x.val

def ea_tT (TT : Finset (Fin n')) : Finset (ZMod (2 * ν)) := TT.map (ea_eS hn).toEmbedding

theorem ea_mem_tT (s : ZMod (2 * ν)) : s ∈ ea_tT hn TT ↔ (ea_eS hn).symm s ∈ TT := by
  unfold ea_tT
  rw [Finset.mem_map_equiv]

variable (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m)

include h hJ1 hJ

theorem ea_alG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      al TT lam0 ((ea_eS hn).symm s) := by
  unfold Formalism.InvariantFactorPaths.G7.alG al
  by_cases hs : (ea_eS hn).symm s ∈ TT
  · rw [if_pos ((ea_mem_tT hn s).2 hs), if_pos hs]
    have e := ea_card_fin (ea_cN hn t lam0 w J s) (fun x => ea_colH t lam0 w J ((ea_eS hn).symm s) x = 1)
    unfold ea_hT
    rw [e]
    exact ea_card_one h hJ1 hJ _
  · rw [if_neg (fun h' => hs ((ea_mem_tT hn s).1 h')), if_neg hs]
    rfl

theorem ea_cN_cast (s : ZMod (2 * ν)) :
    ((ea_cN hn t lam0 w J s : ℕ) : ℤ) = nu t lam0 w J ((ea_eS hn).symm s) 1 :=
  Int.toNat_of_nonneg (ea_nu_nonneg h hJ1 hJ _ 1)

theorem ea_al_eq (s : Fin n') (hs : s ∈ TT) : al TT lam0 s = nu t lam0 w J s 1 - nu t lam0 w J s 2 := by
  have hk : 2 ≤ k1 + 1 := by
    have := h.two_r
    have := h.r_pos
    omega
  unfold al
  rw [if_pos hs, ea_nu_head J s le_rfl (by omega), ea_nu_head J s (by omega : 1 ≤ 2) hk]
  ring

theorem ea_capG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      cap t TT lam0 w J ((ea_eS hn).symm s) := by
  have hA := ea_alG hn h hJ1 hJ s
  have hC := ea_cN_cast hn h hJ1 hJ s
  unfold Formalism.InvariantFactorPaths.G7.capG cap
  by_cases hs : (ea_eS hn).symm s ∈ TT
  · rw [if_pos hs]
    have hal := ea_al_eq h hJ1 hJ _ hs
    have h2 := ea_nu_nonneg h hJ1 hJ ((ea_eS hn).symm s) 2
    have hle : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s ≤
        ea_cN hn t lam0 w J s := by
      have : ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) ≤
          ((ea_cN hn t lam0 w J s : ℕ) : ℤ) := by rw [hA, hC, hal]; omega
      exact_mod_cast this
    rw [Nat.cast_sub hle, hA, hC, hal]
    ring
  · rw [if_neg hs]
    have h0 : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s = 0 := by
      unfold Formalism.InvariantFactorPaths.G7.alG
      rw [if_neg (mt (ea_mem_tT hn s).1 hs)]
    rw [h0, Nat.sub_zero, hC]

theorem ea_lsG (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℤ) =
      lsz t TT lam0 w J ((ea_eS hn).symm s) := by
  have hle : Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s ≤
      ∑ c : Fin (ea_cN hn t lam0 w J s), ea_hT hn t lam0 w J s c := by
    unfold Formalism.InvariantFactorPaths.G7.alG
    split_ifs
    · rw [Finset.card_filter]
      exact Finset.sum_le_sum fun c _ => by split_ifs with h1 <;> omega
    · exact Nat.zero_le _
  unfold Formalism.InvariantFactorPaths.G7.lsG lsz
  rw [Nat.cast_sub hle, ea_alG hn h hJ1 hJ s, ← ea_sum_colH h hJ1 hJ]
  congr 2
  unfold ea_hT ea_cN
  exact Fin.sum_univ_eq_sum_range (fun x => ea_colH t lam0 w J ((ea_eS hn).symm s) x) _

end Num

section Num2

variable {n' k1 : ℕ} {p t m c r : ℕ} {TT : Finset (Fin n')} {a b : Fin n' → ℤ}
  {lam0 : Fin n' → Fin (k1 + 1) → ℤ} {w : ℕ → Fin n' → ℤ} {ν : ℕ} [NeZero ν] (hn : n' = 2 * ν)

theorem ea_dSet (s : Fin n') : Formalism.InvariantFactorPaths.G7.dSet (ea_tT hn TT) (ea_eS hn s) = dSet TT s := by
  unfold Formalism.InvariantFactorPaths.G7.dSet dSet ea_tT
  rw [Finset.filter_map, Finset.map_eq_image, Finset.image_image]
  congr 1
  · funext s'
    simp only [Function.comp_apply, Equiv.coe_toEmbedding]
    rw [ea_eS_sub_val]
  · ext s'
    simp only [Finset.mem_filter, Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]

theorem ea_sum_tT {M : Type} [AddCommMonoid M] (f : ZMod (2 * ν) → M) :
    ∑ s ∈ ea_tT hn TT, f s = ∑ s ∈ TT, f (ea_eS hn s) := Finset.sum_map _ _ _

variable (h : Std p n' k1 t m c r TT a b lam0 w) {J : ℕ} (hJ1 : 1 ≤ J) (hJ : J ≤ m)

include h hJ1 hJ

theorem ea_alG_R (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℝ) =
      (al TT lam0 ((ea_eS hn).symm s) : ℝ) := by
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (ea_alG hn h hJ1 hJ s)

theorem ea_capG_R (s : ZMod (2 * ν)) :
    ((Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℕ) : ℝ) =
      (cap t TT lam0 w J ((ea_eS hn).symm s) : ℝ) := by
  exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (ea_capG hn h hJ1 hJ s)

theorem ea_deLoss :
    Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
      (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
      (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J)) = de p t TT lam0 w J := by
  have hal : ∀ s, ((Formalism.InvariantFactorPaths.G7.lgN p (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J)
      (ea_hT hn t lam0 w J) s) : ℕ) : ℝ) = (lgp p (al TT lam0 ((ea_eS hn).symm s)) : ℝ) := by
    intro s; rw [ea_lg, ea_alG hn h hJ1 hJ s]
  have hls : ∀ s, ((Formalism.InvariantFactorPaths.G7.lgN p (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J)
      (ea_hT hn t lam0 w J) s) : ℕ) : ℝ) = (lgp p (lsz t TT lam0 w J ((ea_eS hn).symm s)) : ℝ) := by
    intro s; rw [ea_lg, ea_lsG hn h hJ1 hJ s]
  unfold Formalism.InvariantFactorPaths.G7.deLoss de
  congr 1
  · rw [← (ea_eS hn).sum_comp]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hal, hls, Equiv.symm_apply_apply]
  · rw [ea_sum_tT hn]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [hal, Equiv.symm_apply_apply]

theorem gain_of_capacity_loss :
    Formalism.GrowthSums.excessGain (p : ℝ) (ea_tT hn TT) (Formalism.InvariantFactorPaths.G7.dSet (ea_tT hn TT))
      (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
        (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
        (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))) = gA p t TT lam0 w J := by
  unfold Formalism.GrowthSums.excessGain gA
  rw [ea_deLoss hn h hJ1 hJ, ea_sum_tT hn]
  simp only [← ea_eS_posAdd hn, ea_dSet hn, ea_alG_R hn h hJ1 hJ, ea_capG_R hn h hJ1 hJ,
    Equiv.symm_apply_apply]

theorem ea_gainG :
    Formalism.GrowthSums.gainG (p : ℝ) (ea_tT hn TT) (Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT))
      (fun s => (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (fun s => (Formalism.InvariantFactorPaths.G7.capG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ))
      (Formalism.InvariantFactorPaths.G7.deLoss p (NN k1 t (J - 1)) (NN k1 t J) (ea_tT hn TT)
        (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))
        (Formalism.InvariantFactorPaths.G7.lsG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J))) = gB p t TT lam0 w J := by
  have hodd : Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) = (TT.filter fun s => IsOddPos s).map (ea_eS hn).toEmbedding := by
    unfold Formalism.InvariantFactorPaths.G7.oddT ea_tT
    rw [Finset.filter_map]
    congr 1
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]
    exact Iff.rfl
  have hg : Formalism.GrowthSums.gamP (p : ℝ) = gam p := by
    unfold Formalism.GrowthSums.gamP Formalism.GrowthSums.rhoP gam; ring
  unfold Formalism.GrowthSums.gainG gB
  rw [ea_deLoss hn h hJ1 hJ, ea_sum_tT hn, hodd, Finset.sum_map, hg]
  simp only [Equiv.coe_toEmbedding, ← ea_eS_posAdd hn, ea_alG_R hn h hJ1 hJ, ea_capG_R hn h hJ1 hJ,
    Equiv.symm_apply_apply]

theorem ea_sumEven :
    ∑ s ∈ ea_tT hn TT \ Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT),
      (Formalism.InvariantFactorPaths.G7.alG (ea_tT hn TT) (ea_cN hn t lam0 w J) (ea_hT hn t lam0 w J) s : ℝ) =
      ((∑ s ∈ TT.filter (fun s => ¬ IsOddPos s), al TT lam0 s : ℤ) : ℝ) := by
  have hodd : Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) = (TT.filter fun s => IsOddPos s).map (ea_eS hn).toEmbedding := by
    unfold Formalism.InvariantFactorPaths.G7.oddT ea_tT
    rw [Finset.filter_map]
    congr 1
    ext s
    rw [Finset.mem_filter, Finset.mem_filter]
    simp only [Function.comp_apply, Equiv.coe_toEmbedding, ea_eS_val]
    exact Iff.rfl
  have hev : ea_tT hn TT \ Formalism.InvariantFactorPaths.G7.oddT (ea_tT hn TT) =
      (TT.filter fun s => ¬ IsOddPos s).map (ea_eS hn).toEmbedding := by
    rw [hodd]
    unfold ea_tT
    rw [← Finset.map_sdiff]
    congr 1
    ext s
    simp only [Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [hev, Finset.sum_map, Int.cast_sum]
  simp only [Equiv.coe_toEmbedding, ea_alG_R hn h hJ1 hJ, Equiv.symm_apply_apply]

end Num2

theorem ea_brNum {p : ℕ} [Fact p.Prime] (X : Sys p) : ea_BrNum X := by
  intro v j hj
  exact ⟨gain_of_capacity_loss (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj,
    ea_gainG (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj,
    ea_sumEven (ea_hn X v) (X.std v) (J := j + 1) (by omega) hj⟩

end Formalism.MainNotions.FormalGroupSystem.Pf
