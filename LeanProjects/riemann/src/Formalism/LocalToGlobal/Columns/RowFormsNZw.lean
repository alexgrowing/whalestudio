import Mathlib
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Columns.GenericUnipotentCharacter
import Formalism.LocalToGlobal.Columns.RowForms

open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions

section PosX

variable (R : Ranks)

def posXn (i : ℕ) : ℕ :=
  if i < R.k - 1 then i
  else if i < R.r then R.k - 1 + (i - (R.k - 1)) * (R.t + 1)
  else R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1)

def invXn (y : ℕ) : ℕ :=
  if y < R.k - 1 then y
  else if (y - (R.k - 1)) % (R.t + 1) = 0 then R.k - 1 + (y - (R.k - 1)) / (R.t + 1)
  else R.r + ((y - (R.k - 1)) / (R.t + 1)) * R.t + ((y - (R.k - 1)) % (R.t + 1) - 1)

theorem nz_t_pos : 0 < R.t := by
  have := R.rank_add_five_le
  omega

theorem nz_r_eq : R.r = R.k - 1 + R.m := by
  have := R.m_add_three_le_k
  unfold Ranks.r
  omega

theorem nz_rankX : R.N R.m - 1 = R.k - 1 + R.m * (R.t + 1) := by
  have := R.m_add_three_le_k
  unfold Ranks.N
  omega

theorem nz_posXn_hi {i : ℕ} (h : R.r ≤ i) :
    posXn R i = R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by
  have := nz_r_eq R
  unfold posXn
  rw [if_neg (by omega), if_neg (by omega)]

theorem nz_invXn_posXn (i : ℕ) : invXn R (posXn R i) = i := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  by_cases h1 : i < R.k - 1
  · unfold posXn invXn
    rw [if_pos h1, if_pos h1]
  by_cases h2 : i < R.r
  · have e0 : posXn R i = R.k - 1 + (i - (R.k - 1)) * (R.t + 1) := by
      unfold posXn
      rw [if_neg h1, if_pos h2]
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) (i - (R.k - 1)) 0 (by omega)
    have e1 : R.k - 1 + (i - (R.k - 1)) * (R.t + 1) - (R.k - 1) = (i - (R.k - 1)) * (R.t + 1) + 0 := by omega
    unfold invXn
    rw [e0, if_neg (by omega), e1, d1, d2, if_pos rfl]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    obtain ⟨d1, d2⟩ := divmod (R.t + 1) ((i - R.r) / R.t) ((i - R.r) % R.t + 1) (by omega)
    have e1 : R.k - 1 + ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) - (R.k - 1) =
        ((i - R.r) / R.t) * (R.t + 1) + ((i - R.r) % R.t + 1) := by omega
    have e2 := Nat.div_add_mod (i - R.r) R.t
    rw [Nat.mul_comm] at e2
    unfold invXn
    rw [nz_posXn_hi R (Nat.not_lt.mp h2), if_neg (by omega), e1, d1, d2, if_neg (by omega)]
    omega

theorem nz_posXn_lt {i : ℕ} (h : i < R.N R.m - 1) : posXn R i < R.N R.m - 1 := by
  have hr := nz_r_eq R
  have ht := nz_t_pos R
  have hn := nz_rankX R
  have hn' := rank_X'_eq R
  by_cases h1 : i < R.k - 1
  · unfold posXn
    rw [if_pos h1]
    exact h
  by_cases h2 : i < R.r
  · have h3 : (i - (R.k - 1) + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h3
    unfold posXn
    rw [if_neg h1, if_pos h2]
    omega
  · have hm : (i - R.r) % R.t < R.t := Nat.mod_lt _ ht
    have hd : (i - R.r) / R.t < R.m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; omega)
    have h3 : ((i - R.r) / R.t + 1) * (R.t + 1) ≤ R.m * (R.t + 1) := Nat.mul_le_mul_right _ hd
    rw [Nat.add_mul, Nat.one_mul] at h3
    rw [nz_posXn_hi R (Nat.not_lt.mp h2)]
    omega

def posXf (i : Fin (R.N R.m - 1)) : Fin (R.N R.m - 1) := ⟨posXn R i.1, nz_posXn_lt R i.2⟩

theorem nz_posXf_inj : Function.Injective (posXf R) := by
  intro a b h
  have h1 : posXn R a.1 = posXn R b.1 := congrArg Fin.val h
  apply Fin.ext
  rw [← nz_invXn_posXn R a.1, ← nz_invXn_posXn R b.1, h1]

def posX : Equiv.Perm (Fin (R.N R.m - 1)) :=
  Equiv.ofBijective (posXf R) (Finite.injective_iff_bijective.mp (nz_posXf_inj R))

theorem nz_posX_val (i : Fin (R.N R.m - 1)) : (posX R i).1 = posXn R i.1 := rfl

theorem nz_coarseX {a : ℕ} (h1 : R.r ≤ a) (h2 : a < R.N R.m - 1) :
    coarse R.r (List.replicate R.m R.t) a = (a - R.r) / R.t + 1 := by
  have hn' := rank_X'_eq R
  rw [coarse_of_le h1, blkIdx_replicate (nz_t_pos R) R.m (a - R.r) (by omega)]

def sX (B : ℕ) : ℚ := ((R.t : ℚ) - 1) / 2 - (((R.N R.m - 1 : ℕ) : ℚ) - 1) / 2 + (R.k : ℚ) + (B : ℚ) * ((R.t : ℚ) + 1)

theorem nz_sX_int (B : ℕ) : ∃ z : ℤ, sX R B = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨c, hc⟩ := R.t_odd
  have hk := R.m_add_three_le_k
  have hn : ((R.N R.m - 1 : ℕ) : ℚ) = (R.k : ℚ) + (R.m : ℚ) * ((R.t : ℚ) + 1) - 1 := by
    have : R.N R.m - 1 + 1 = R.k + R.m * (R.t + 1) := by
      unfold Ranks.N
      omega
    have h2 : ((R.N R.m - 1 + 1 : ℕ) : ℚ) = ((R.k + R.m * (R.t + 1) : ℕ) : ℚ) := by rw [this]
    push_cast at h2
    linarith
  unfold sX
  rw [hn, ha, hc]
  exact ⟨(c : ℤ) - ((a : ℤ) + (R.m : ℤ) * ((c : ℤ) + 1) - 1) + ((a : ℤ) + a) + (B : ℤ) * (2 * (c : ℤ) + 1 + 1), by push_cast; ring⟩

variable {R}

theorem RowPar.nz_sgTrue_pos (P : HCParam R) (a : Fin (R.N R.m - 1)) (h : R.r ≤ a.1) :
    (((RowPar.of P).sgTrue).w (posX R a) : ℚ) = -(RowPar.of P).eAt ((a.1 - R.r) / R.t) + sX R ((a.1 - R.r) / R.t) := by
  have ht := nz_t_pos R
  have hk := R.m_add_three_le_k
  have hm : (a.1 - R.r) % R.t < R.t := Nat.mod_lt _ ht
  rw [RowPar.sgTrue_eq P (posX R a), nz_posX_val, nz_posXn_hi R h,
    RowPar.sgHC_e _ ((a.1 - R.r) / R.t) ((a.1 - R.r) % R.t + 1) (by omega) (by omega)]
  unfold rhoVec sX
  rw [nz_posX_val, nz_posXn_hi R h]
  have hk1 : ((R.k - 1 : ℕ) : ℚ) = (R.k : ℚ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    simp
  push_cast
  rw [hk1]
  ring

end PosX

section WtsX

variable {X : Fields} {Word : Type} {R : Ranks} {W : Wts X Word R}

theorem nz_sg_val (hW : W.Ok) (τ : X.Tau) (a : Fin (R.N R.m - 1)) (h : R.r ≤ a.1) :
    ((W.sgTrue τ).w (posX R a) : ℚ) = -(W.row τ).eAt ((a.1 - R.r) / R.t) + sX R ((a.1 - R.r) / R.t) := by
  obtain ⟨P, hP⟩ := hW.row_ok τ
  unfold Wts.sgTrue
  rw [← hP]
  exact RowPar.nz_sgTrue_pos P a h

theorem nz_sg_const (hW : W.Ok) (τ : X.Tau) (a b : Fin (R.N R.m - 1)) (ha : R.r ≤ a.1) (hb : R.r ≤ b.1)
    (hab : coarse R.r (List.replicate R.m R.t) a.1 = coarse R.r (List.replicate R.m R.t) b.1) :
    (W.sgTrue τ).w (posX R a) = (W.sgTrue τ).w (posX R b) := by
  rw [nz_coarseX R ha a.2, nz_coarseX R hb b.2] at hab
  have h1 : (a.1 - R.r) / R.t = (b.1 - R.r) / R.t := by omega
  have h2 : ((W.sgTrue τ).w (posX R a) : ℚ) = ((W.sgTrue τ).w (posX R b) : ℚ) := by
    rw [nz_sg_val hW τ a ha, nz_sg_val hW τ b hb, h1]
  exact_mod_cast h2

theorem nz_sg_even (hW : W.Ok) (hf : Even X.f) (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ))
    (a : Fin (R.N R.m - 1)) (ha : R.r ≤ a.1) : Even (∑ τ, (W.sgTrue τ).w (posX R a)) := by
  have hn' := rank_X'_eq R
  have hB : (a.1 - R.r) / R.t < R.m := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; have := a.2; omega)
  obtain ⟨z, hz⟩ := he ⟨(a.1 - R.r) / R.t, hB⟩
  obtain ⟨y, hy⟩ := nz_sX_int R ((a.1 - R.r) / R.t)
  obtain ⟨c, hc⟩ := hf
  have h1 : ((∑ τ, (W.sgTrue τ).w (posX R a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun τ _ => nz_sg_val hW τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ]
    have h2 : ∑ τ, (W.row τ).eAt ((a.1 - R.r) / R.t) = 2 * (z : ℚ) := by
      rw [← hz]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold RowPar.eAt
      rw [dif_pos hB]
    have h3 : Fintype.card X.Tau = c + c := hc
    rw [h2, h3, hy, nsmul_eq_mul]
    push_cast
    ring
  have h4 : ∑ τ, (W.sgTrue τ).w (posX R a) = 2 * (-z + (c : ℤ) * y) := by exact_mod_cast h1
  rw [h4]
  exact even_two_mul _

end WtsX

section PosV

variable (R : Ranks) (j : ℕ)

def pV : ℕ := min (RowPar.pOf R j) R.r

def posVn (i : ℕ) : ℕ :=
  if i < pV R j then i else if i < R.r then i + R.t else i - R.r + pV R j

theorem nz_pV_le : pV R j ≤ R.r := min_le_right _ _

theorem nz_posVn_lt {i : ℕ} (h : i < R.nV) : posVn R j i < R.nV := by
  have h1 := nz_pV_le R j
  unfold Ranks.nV at h ⊢
  unfold posVn
  split_ifs <;> omega

def posVf (i : Fin R.nV) : Fin R.nV := ⟨posVn R j i.1, nz_posVn_lt R j i.2⟩

theorem nz_posVf_inj : Function.Injective (posVf R j) := by
  intro a b h
  have h1 : posVn R j a.1 = posVn R j b.1 := congrArg Fin.val h
  have h2 := nz_pV_le R j
  have ha := a.2
  have hb := b.2
  unfold Ranks.nV at ha hb
  apply Fin.ext
  unfold posVn at h1
  split_ifs at h1 <;> omega

def posV : Equiv.Perm (Fin R.nV) :=
  Equiv.ofBijective (posVf R j) (Finite.injective_iff_bijective.mp (nz_posVf_inj R j))

theorem nz_posV_val (i : Fin R.nV) : (posV R j i).1 = posVn R j i.1 := rfl

variable {R j}

theorem nz_pV_eq (h2 : j ≤ R.m) : pV R j = RowPar.pOf R j := by
  have := R.m_add_three_le_k
  unfold pV RowPar.pOf Ranks.r
  omega

def sV (R : Ranks) (j : ℕ) : ℚ := ((R.k : ℚ) - (R.m : ℚ)) / 2 + (j : ℚ) - 1

theorem nz_sV_int (R : Ranks) (j : ℕ) : ∃ z : ℤ, sV R j = z := by
  obtain ⟨a, ha⟩ := R.k_even
  obtain ⟨b, hb⟩ := R.m_even
  unfold sV
  rw [ha, hb]
  exact ⟨(a : ℤ) - b + j - 1, by push_cast; ring⟩

theorem RowPar.nz_lamVQ_pos (S : RowPar R) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (a : Fin R.nV) (h : R.r ≤ a.1) :
    S.lamVQ j (posV R j a) = -S.eAt (j - 1) + sV R j := by
  have hp := nz_pV_eq h2
  have hle := nz_pV_le R j
  have ha := a.2
  unfold Ranks.nV at ha
  have e : (posV R j a).1 = a.1 - R.r + RowPar.pOf R j := by
    rw [nz_posV_val]
    unfold posVn
    rw [if_neg (by omega), if_neg (by omega), hp]
  unfold RowPar.lamVQ
  rw [e, if_neg (by omega), if_pos (by omega)]
  unfold RowPar.dV sV
  rw [RowPar.cast_pOf h1, RowPar.cast_qOf h2]
  ring

end PosV

section WtsV

variable {X : Fields} {Word : Type} {R : Ranks} {W : Wts X Word R} {j : ℕ}

theorem nz_lamV_val (hW : W.Ok) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (τ : X.Tau) (a : Fin R.nV) (h : R.r ≤ a.1) :
    ((W.lamV j τ).w (posV R j a) : ℚ) = -(W.row τ).eAt (j - 1) + sV R j := by
  rw [Wts.lamV_eq hW h1 h2 τ (posV R j a)]
  exact RowPar.nz_lamVQ_pos _ h1 h2 a h

theorem nz_lamV_const (hW : W.Ok) (h1 : 1 ≤ j) (h2 : j ≤ R.m) (τ : X.Tau) (a b : Fin R.nV) (ha : R.r ≤ a.1)
    (hb : R.r ≤ b.1) : (W.lamV j τ).w (posV R j a) = (W.lamV j τ).w (posV R j b) := by
  have h3 : ((W.lamV j τ).w (posV R j a) : ℚ) = ((W.lamV j τ).w (posV R j b) : ℚ) := by
    rw [nz_lamV_val hW h1 h2 τ a ha, nz_lamV_val hW h1 h2 τ b hb]
  exact_mod_cast h3

theorem nz_lamV_even (hW : W.Ok) (hf : Even X.f) (he : ∀ j : Fin R.m, ∃ z : ℤ, ∑ τ, (W.row τ).e j = 2 * (z : ℚ))
    (h1 : 1 ≤ j) (h2 : j ≤ R.m) (a : Fin R.nV) (ha : R.r ≤ a.1) : Even (∑ τ, (W.lamV j τ).w (posV R j a)) := by
  have hB : j - 1 < R.m := by omega
  obtain ⟨z, hz⟩ := he ⟨j - 1, hB⟩
  obtain ⟨y, hy⟩ := nz_sV_int R j
  obtain ⟨c, hc⟩ := hf
  have h3 : ((∑ τ, (W.lamV j τ).w (posV R j a) : ℤ) : ℚ) = ((2 * (-z + (c : ℤ) * y) : ℤ) : ℚ) := by
    push_cast
    rw [Finset.sum_congr rfl fun τ _ => nz_lamV_val hW h1 h2 τ a ha, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_const, Finset.card_univ]
    have h4 : ∑ τ, (W.row τ).eAt (j - 1) = 2 * (z : ℚ) := by
      rw [← hz]
      refine Finset.sum_congr rfl fun τ _ => ?_
      unfold RowPar.eAt
      rw [dif_pos hB]
    have h5 : Fintype.card X.Tau = c + c := hc
    rw [h4, h5, hy, nsmul_eq_mul]
    push_cast
    ring
  have h6 : ∑ τ, (W.lamV j τ).w (posV R j a) = 2 * (-z + (c : ℤ) * y) := by exact_mod_cast h3
  rw [h6]
  exact even_two_mul _

end WtsV

end Formalism.L2.Col
