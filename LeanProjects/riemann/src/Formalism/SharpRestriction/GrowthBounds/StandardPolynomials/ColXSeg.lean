import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.ColDef
import Formalism.SharpRestriction.GrowthBounds.BinomialRatio.OtherStart

noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf.GenusGluing

open Formalism.MainNotions.G MvPolynomial

variable (X : Loc) (j : Fin (numSeg X.TT))

theorem posS_zero : posS X j 0 = ((segStart X.TT j).val : ℤ) := rfl

theorem posS_succ_lt (a : Fin (2 * segS X.TT j + 1)) (h : (a : ℕ) < 2 * segS X.TT j) :
    posS X j a.succ = ((segStart X.TT j).val : ℤ) +
      ((segDists X.TT j).get (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) : ℕ) := by
  simp only [posS, Fin.cons_succ, dif_pos h]

theorem posS_succ_ge (a : Fin (2 * segS X.TT j + 1)) (h : ¬ (a : ℕ) < 2 * segS X.TT j) :
    posS X j a.succ = ((segStart X.TT j).val : ℤ) + (segG X.TT j : ℕ) := by
  simp only [posS, Fin.cons_succ, dif_neg h]

theorem lamS_zero : lamS X j 0 = (topStart X j, true) := rfl

theorem lamS_succ_lt (a : Fin (2 * segS X.TT j + 1)) (h : (a : ℕ) < 2 * segS X.TT j) :
    lamS X j a.succ = (topOdd X j ⟨(a : ℕ) / 2, by omega⟩, decide ((a : ℕ) % 2 = 0)) := by
  simp only [lamS, Fin.cons_succ, dif_pos h]

theorem lamS_succ_ge (a : Fin (2 * segS X.TT j + 1)) (h : ¬ (a : ℕ) < 2 * segS X.TT j) :
    lamS X j a.succ = (topEnd X j, true) := by
  simp only [lamS, Fin.cons_succ, dif_neg h]

theorem segG_pos' : 0 < segG X.TT j := by
  unfold segG
  split_ifs with h
  · exact lt_of_le_of_lt (Nat.zero_le _) (segStart X.TT j).isLt
  · omega

theorem position_le_segment_end (i : Fin (2 * segS X.TT j + 1 + 1)) : posS X j i ≤ zS X j := by
  refine Fin.cases ?_ (fun a => ?_) i
  · rw [posS_zero]; unfold zS; omega
  · by_cases h : (a : ℕ) < 2 * segS X.TT j
    · rw [posS_succ_lt X j a h]; unfold zS
      have := (dist_pos_lt X.TT j ⟨(a : ℕ) / 2, by omega⟩).2
      omega
    · rw [posS_succ_ge X j a h]; unfold zS; exact le_rfl

theorem posS_mono : Monotone (posS X j) := by
  intro i i'
  refine Fin.cases ?_ (fun a => ?_) i
  · intro _
    refine Fin.cases le_rfl (fun a' => ?_) i'
    by_cases h : (a' : ℕ) < 2 * segS X.TT j
    · rw [posS_zero, posS_succ_lt X j a' h]; omega
    · rw [posS_zero, posS_succ_ge X j a' h]; omega
  · refine Fin.cases ?_ (fun a' => ?_) i'
    · intro h; exact absurd h (by simp)
    · intro hle
      have hle' : (a : ℕ) ≤ (a' : ℕ) := Fin.succ_le_succ_iff.mp hle
      by_cases h' : (a' : ℕ) < 2 * segS X.TT j
      · have h : (a : ℕ) < 2 * segS X.TT j := by omega
        rw [posS_succ_lt X j a h, posS_succ_lt X j a' h']
        have := (dist_strictMono X.TT j).monotone
          (show (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) ≤ ⟨(a' : ℕ) / 2, by omega⟩ from by
            simp only [Fin.le_def]; omega)
        omega
      · rw [posS_succ_ge X j a' h']
        exact position_le_segment_end X j a.succ

theorem posS_lt (i i' : Fin (2 * segS X.TT j + 1 + 1)) (hlt : i < i') (hv : (lamS X j i').2 = true) :
    posS X j i < posS X j i' := by
  revert hlt hv
  refine Fin.cases ?_ (fun a' => ?_) i'
  · intro h; exact absurd h (by simp)
  · intro hlt hv
    by_cases h' : (a' : ℕ) < 2 * segS X.TT j
    · rw [lamS_succ_lt X j a' h'] at hv
      have hev : (a' : ℕ) % 2 = 0 := by simpa using hv
      rw [posS_succ_lt X j a' h']
      revert hlt
      refine Fin.cases ?_ (fun a => ?_) i
      · intro _
        rw [posS_zero]
        have := (dist_pos_lt X.TT j ⟨(a' : ℕ) / 2, by omega⟩).1
        omega
      · intro hlt
        have hlt' : (a : ℕ) < (a' : ℕ) := Fin.succ_lt_succ_iff.mp hlt
        rw [posS_succ_lt X j a (by omega)]
        have := (dist_strictMono X.TT j)
          (show (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)) < ⟨(a' : ℕ) / 2, by omega⟩ from by
            simp only [Fin.lt_def]; omega)
        omega
    · rw [posS_succ_ge X j a' h']
      revert hlt
      refine Fin.cases ?_ (fun a => ?_) i
      · intro _
        rw [posS_zero]
        have := segG_pos' X j
        omega
      · intro hlt
        have hlt' : (a : ℕ) < (a' : ℕ) := Fin.succ_lt_succ_iff.mp hlt
        have ha' := a'.2
        rw [posS_succ_lt X j a (by omega)]
        have := (dist_pos_lt X.TT j ⟨(a : ℕ) / 2, by omega⟩).2
        omega

theorem next_val : ((segStart X.TT j).val + segG X.TT j) % X.n' = (segNext X.TT j).val := by
  have e := congrArg Fin.val (posAdd_cdist (segStart X.TT j) (segNext X.TT j))
  have e' : ((segStart X.TT j).val + cdist (segStart X.TT j) (segNext X.TT j)) % X.n' = (segNext X.TT j).val := e
  unfold segG
  split_ifs with h
  · rw [h, Nat.add_zero] at e'
    rw [Nat.add_mod_right]; exact e'
  · exact e'

theorem pos_congr (i : Fin (2 * segS X.TT j + 1 + 1)) :
    (hhLetters X.TT).pos (lamS X j i) % (X.n' : ℤ) = posS X j i % (X.n' : ℤ) := by
  refine Fin.cases ?_ (fun a => ?_) i
  · rfl
  · by_cases h : (a : ℕ) < 2 * segS X.TT j
    · rw [lamS_succ_lt X j a h, posS_succ_lt X j a h]
      show (((segPos X.TT j ⟨(a : ℕ) / 2, by omega⟩).val : ℕ) : ℤ) % (X.n' : ℤ) = _
      have e : (segPos X.TT j ⟨(a : ℕ) / 2, by omega⟩).val =
          ((segStart X.TT j).val + (segDists X.TT j).get (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j))) % X.n' := rfl
      simp only [e, Int.natCast_mod, Int.emod_emod_of_dvd _ (dvd_refl _), Nat.cast_add]
    · rw [lamS_succ_ge X j a h, posS_succ_ge X j a h]
      show (((segNext X.TT j).val : ℕ) : ℤ) % (X.n' : ℤ) = _
      simp only [← next_val X j, Int.natCast_mod, Int.emod_emod_of_dvd _ (dvd_refl _), Nat.cast_add]

theorem topOdd_inj (i i' : Fin (segS X.TT j)) (h : topOdd X j i = topOdd X j i') : i = i' := by
  have h1 : segPos X.TT j i = segPos X.TT j i' := congrArg Subtype.val h
  have a1 := (pos_spec X.TT j i).2
  have a2 := (pos_spec X.TT j i').2
  rw [h1, a2] at a1
  exact (dist_strictMono X.TT j).injective a1.symm

theorem topOdd_ne_end (i : Fin (segS X.TT j)) (j' : Fin (numSeg X.TT)) : topOdd X j i ≠ topEnd X j' := by
  intro h
  have h1 : segPos X.TT j i = segNext X.TT j' := congrArg Subtype.val h
  have a1 := (pos_mem X.TT j i).2
  rw [h1] at a1
  exact a1 (next_mem X.TT j').2

theorem topOdd_ne_start (i : Fin (segS X.TT j)) : topOdd X j i ≠ topStart X j := by
  intro h
  exact pos_ne_start X.TT j i (congrArg Subtype.val h)

theorem topStart_ne_end (h2 : 2 ≤ numSeg X.TT) : topStart X j ≠ topEnd X j := by
  intro h
  have h1 : segStart X.TT j = segNext X.TT j := congrArg Subtype.val h
  have a := (segG_eq X.TT h2 j).2
  rw [← h1] at a
  have hx := (segStart X.TT j).isLt
  have : cdist (segStart X.TT j) (segStart X.TT j) = 0 := by
    unfold cdist
    have e : (segStart X.TT j).val + X.n' - (segStart X.TT j).val = X.n' := by omega
    rw [e, Nat.mod_self]
  omega

theorem lamS_injective (h2 : 2 ≤ numSeg X.TT) : Function.Injective (lamS X j) := by
  intro i i'
  refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) i' <;> intro hii
  · rfl
  · exfalso
    rw [lamS_zero] at hii
    by_cases hb : (b : ℕ) < 2 * segS X.TT j
    · rw [lamS_succ_lt X j b hb] at hii
      exact topOdd_ne_start X j _ (Prod.ext_iff.1 hii).1.symm
    · rw [lamS_succ_ge X j b hb] at hii
      exact topStart_ne_end X j h2 (Prod.ext_iff.1 hii).1
  · exfalso
    rw [lamS_zero] at hii
    by_cases ha : (a : ℕ) < 2 * segS X.TT j
    · rw [lamS_succ_lt X j a ha] at hii
      exact topOdd_ne_start X j _ (Prod.ext_iff.1 hii).1
    · rw [lamS_succ_ge X j a ha] at hii
      exact topStart_ne_end X j h2 (Prod.ext_iff.1 hii).1.symm
  · congr 1
    have ha' := a.isLt
    have hb' := b.isLt
    by_cases ha : (a : ℕ) < 2 * segS X.TT j <;> by_cases hb : (b : ℕ) < 2 * segS X.TT j
    · rw [lamS_succ_lt X j a ha, lamS_succ_lt X j b hb] at hii
      obtain ⟨h1, h3⟩ := Prod.ext_iff.1 hii
      have e1 := congrArg Fin.val (topOdd_inj X j _ _ h1)
      simp only at e1
      have e2 : ((a : ℕ) % 2 = 0 ↔ (b : ℕ) % 2 = 0) := by simpa using h3
      ext
      omega
    · rw [lamS_succ_lt X j a ha, lamS_succ_ge X j b hb] at hii
      exact absurd (Prod.ext_iff.1 hii).1 (topOdd_ne_end X j _ j)
    · rw [lamS_succ_ge X j a ha, lamS_succ_lt X j b hb] at hii
      exact absurd (Prod.ext_iff.1 hii).1.symm (topOdd_ne_end X j _ j)
    · ext
      omega

theorem lamS_ne_endFalse (i : Fin (2 * segS X.TT j + 1 + 1)) (j' : Fin (numSeg X.TT)) :
    lamS X j i ≠ (topEnd X j', false) := by
  refine Fin.cases ?_ (fun a => ?_) i
  · rw [lamS_zero]
    simp
  · by_cases h : (a : ℕ) < 2 * segS X.TT j
    · rw [lamS_succ_lt X j a h]
      intro he
      exact topOdd_ne_end X j _ j' (Prod.ext_iff.1 he).1
    · rw [lamS_succ_ge X j a h]
      simp

theorem lev_succ (C0 CE1 CE2 : ℝ) (a : Fin (2 * segS X.TT j + 1)) (b : Fin X.m) :
    X.p ^ (zS X j - posS X j a.succ).toNat = symLev X.p C0 CE1 CE2 X j (Sum.inl (a.castSucc, b)) := by
  by_cases h : (a : ℕ) < 2 * segS X.TT j
  · rw [posS_succ_lt X j a h]
    have e : symLev X.p C0 CE1 CE2 X j (Sum.inl (a.castSucc, b)) =
        (X.seg C0 CE1 CE2 j).P X.p ⟨(a : ℕ) / 2, by omega⟩ := by
      unfold symLev
      simp only [Fin.val_castSucc]
      rw [dif_pos h]
    rw [e]
    show _ = X.p ^ (segG X.TT j - (segDists X.TT j).get (⟨(a : ℕ) / 2, by omega⟩ : Fin (segS X.TT j)))
    congr 1
    unfold zS
    omega
  · rw [posS_succ_ge X j a h]
    have e : symLev X.p C0 CE1 CE2 X j (Sum.inl (a.castSucc, b)) = 1 := by
      unfold symLev
      simp only [Fin.val_castSucc]
      rw [dif_neg h]
    rw [e]
    unfold zS
    simp

theorem lev_zero (C0 CE1 CE2 : ℝ) : X.p ^ (zS X j - posS X j 0).toNat = (X.seg C0 CE1 CE2 j).Qj X.p := by
  rw [posS_zero]
  show _ = X.p ^ segG X.TT j
  congr 1
  unfold zS
  omega

theorem lev_le (hp : 0 < X.p) (hG : segG X.TT j ≤ X.G') (i : Fin (2 * segS X.TT j + 1 + 1)) :
    X.p ^ (zS X j - posS X j i).toNat ≤ X.p ^ X.G' := by
  refine Nat.pow_le_pow_right hp ?_
  have h0 : posS X j 0 ≤ posS X j i := posS_mono X j (Fin.zero_le _)
  rw [posS_zero] at h0
  unfold zS
  omega

theorem phiS_succ (C0 CE1 CE2 : ℝ) (a : Fin (2 * segS X.TT j + 1)) (b : Fin X.m) :
    phiS X j (a.succ, Fin.natAdd 1 b) = symVar C0 CE1 CE2 X j (Sum.inl (a.castSucc, b)) := by
  have ec : Fin.cast (Nat.add_comm 1 X.m) (Fin.natAdd 1 b) = b.succ := by
    apply Fin.ext; simp
  unfold phiS
  simp only [ec]
  by_cases h : (a : ℕ) < 2 * segS X.TT j
  · rw [lamS_succ_lt X j a h]
    unfold symVar
    simp only [Fin.val_castSucc]
    rw [dif_pos h]
  · rw [lamS_succ_ge X j a h]
    unfold symVar
    simp only [Fin.val_castSucc]
    rw [dif_neg h]
    have : (a : ℕ) = 2 * segS X.TT j := by have := a.2; omega
    simp [this]

theorem phiS_zero [NeZero X.m] : phiS X j (0, Fin.castAdd X.m 0) = ((topStart X j, true), 0) := by
  unfold phiS
  rw [lamS_zero]
  rfl

theorem phiS_odd (l : Fin (segS X.TT j)) :
    phiS X j (⟨2 * l.val + 1, by have := l.2; omega⟩, Fin.castAdd X.m 0) = ((topOdd X j l, true), 0) := by
  have e : (⟨2 * l.val + 1, by have := l.2; omega⟩ : Fin (2 * segS X.TT j + 1 + 1)) =
      (⟨2 * l.val, by have := l.2; omega⟩ : Fin (2 * segS X.TT j + 1)).succ := rfl
  unfold phiS
  simp only [e]
  rw [lamS_succ_lt X j _ (by have := l.2; simp only; omega)]
  have e2 : (⟨(2 * l.val) / 2, by have := l.2; omega⟩ : Fin (segS X.TT j)) = l := by
    apply Fin.ext; simp
  simp only [e2]
  simp
  rfl

end Formalism.MainNotions.ColumnSystems.Pf.GenusGluing
