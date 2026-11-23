import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.RestValBdG

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords

namespace DdG

theorem mapDomain_le {α β : Type} (f : α → β) (mo : α →₀ ℕ) (b : β) (a0 : α)
    (h : ∀ a, f a = b → a = a0) : Finsupp.mapDomain f mo b ≤ mo a0 := by
  classical
  simp only [Finsupp.mapDomain, Finsupp.sum]
  rw [Finsupp.finset_sum_apply]
  by_cases ha : a0 ∈ mo.support
  · rw [← Finset.sum_erase_add _ _ ha]
    have hz : ∑ x ∈ mo.support.erase a0, (Finsupp.single (f x) (mo x)) b = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finsupp.single_apply, if_neg]
      intro hfx
      exact (Finset.ne_of_mem_erase hx) (h x hfx)
    rw [hz, zero_add, Finsupp.single_apply]
    split_ifs <;> omega
  · have hz : ∀ x ∈ mo.support, (Finsupp.single (f x) (mo x)) b = 0 := by
      intro x hx
      rw [Finsupp.single_apply, if_neg]
      intro hfx
      exact ha (h x hfx ▸ hx)
    rw [Finset.sum_eq_zero hz]
    exact Nat.zero_le _

theorem multideg_mapDomain_le {α β : Type} {n : ℕ} (g : α → β) (mo : α × Fin n →₀ ℕ) (b : β) (a0 : α)
    (hU : ∀ a, g a = b → a = a0) :
    multideg (Finsupp.mapDomain (fun v : α × Fin n => (g v.1, v.2)) mo) b ≤ ∑ c, mo (a0, c) := by
  unfold multideg
  apply Finset.sum_le_sum
  intro c _
  apply mapDomain_le
  rintro ⟨a, c'⟩ hv
  simp only [Prod.mk.injEq] at hv
  rw [hU a hv.1, hv.2]

theorem sumIteLe {α β : Type} [Fintype α] (g : α → β) (h : α → ℕ) (b : β) (t0 : α)
    (hu : ∀ t, g t = b → t = t0) : (∑ t, if g t = b then h t else 0) ≤ h t0 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ t0)]
  have hz : ∑ t ∈ Finset.univ.erase t0, (if g t = b then h t else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    rw [if_neg]
    intro hgt
    exact Finset.ne_of_mem_erase ht (hu t hgt)
  rw [hz, zero_add]
  split_ifs <;> omega

theorem sumIteZero {α β : Type} [Fintype α] (g : α → β) (h : α → ℕ) (b : β)
    (hu : ∀ t, g t ≠ b) : (∑ t, if g t = b then h t else 0) = 0 := Finset.sum_eq_zero fun t _ => if_neg (hu t)

theorem multideg_of_mem_Pol {R : Type} [CommRing R] [Nontrivial R] {ι : Type} {n : ℕ} {dd : ι → ℕ}
    {E : ι × Fin n →₀ ℕ} (h : monomial E (1 : R) ∈ Pol R n dd) (i : ι) : multideg E i = dd i := by
  have h' : monomial E (1 : R) ∈ MvPolynomial.restrictSupport R {m : ι × Fin n →₀ ℕ | ∀ i, multideg m i = dd i} := h
  rw [MvPolynomial.mem_restrictSupport_iff] at h'
  have hE : E ∈ (monomial E (1 : R)).support := by
    rw [MvPolynomial.support_monomial, if_neg one_ne_zero]
    exact Finset.mem_singleton_self E
  exact h' hE i

theorem real_le {p : ℕ} (hp : 0 < p) (D a b : ℕ) (h : p ^ D * a ≤ b) :
    (a : ℝ) ≤ (b : ℝ) / (p : ℝ) ^ D + (b : ℝ) / (p : ℝ) ^ D / 100 := by
  have hpD : (0 : ℝ) < (p : ℝ) ^ D := pow_pos (by exact_mod_cast hp) D
  have h1 : (a : ℝ) ≤ (b : ℝ) / (p : ℝ) ^ D := by
    rw [le_div_iff₀ hpD, mul_comm]
    exact_mod_cast h
  have h2 : (0 : ℝ) ≤ (b : ℝ) / (p : ℝ) ^ D / 100 := by positivity
  linarith

section Fr

variable {n' r : ℕ} [NeZero n'] (Fr : Frames n' r)

theorem fr_le_add (hm : ∀ j : ℤ, ∀ i, i + 1 < r → Fr.fr j i < Fr.fr j (i + 1)) (j : ℤ) (i : ℕ) :
    ∀ e : ℕ, i + e < r → Fr.fr j i ≤ Fr.fr j (i + e)
  | 0, _ => le_rfl
  | e + 1, h => (fr_le_add hm j i e (by omega)).trans (hm j (i + e) (by omega)).le

theorem fr_le (hm : ∀ j : ℤ, ∀ i, i + 1 < r → Fr.fr j i < Fr.fr j (i + 1)) (j : ℤ) {i k : ℕ}
    (hik : i ≤ k) (hk : k < r) : Fr.fr j i ≤ Fr.fr j k := by
  obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hik
  exact fr_le_add Fr hm j i e hk

theorem fr_lt (hm : ∀ j : ℤ, ∀ i, i + 1 < r → Fr.fr j i < Fr.fr j (i + 1)) (j : ℤ) {i k : ℕ}
    (hik : i < k) (hk : k < r) : Fr.fr j i < Fr.fr j k := lt_of_lt_of_le (hm j i (by omega)) (fr_le Fr hm j (Nat.succ_le_of_lt hik) hk)

theorem fr_inj (hm : ∀ j : ℤ, ∀ i, i + 1 < r → Fr.fr j i < Fr.fr j (i + 1)) (j : ℤ) {i k : ℕ}
    (hi : i < r) (hk : k < r) (h : Fr.fr j i = Fr.fr j k) : i = k := by
  rcases lt_trichotomy i k with hlt | heq | hgt
  · exact absurd h (fr_lt Fr hm j hlt hk).ne
  · exact heq
  · exact absurd h (fr_lt Fr hm j hgt hi).ne'

theorem eq_fr (hgap : ∀ j : ℤ, ∀ i, ∀ x : ℤ, i + 1 < r → Fr.fr j i < x → x < Fr.fr j (i + 1) → posOf n' x ∉ Fr.TT)
    (hr : 1 ≤ r) (a x : ℤ) (h0 : Fr.fr a 0 ≤ x) (h1 : x ≤ Fr.fr a (r - 1)) (hx : posOf n' x ∈ Fr.TT) :
    ∃ i, i < r ∧ x = Fr.fr a i := by
  classical
  let S := (Finset.range r).filter (fun i => Fr.fr a i ≤ x)
  have h0S : (0 : ℕ) ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), h0⟩
  have hne : S.Nonempty := ⟨0, h0S⟩
  obtain ⟨i, hiS, himax⟩ : ∃ i ∈ S, ∀ k ∈ S, k ≤ i :=
    ⟨S.max' hne, S.max'_mem hne, fun k hk => S.le_max' k hk⟩
  have hir : i < r := Finset.mem_range.mp (Finset.mem_filter.mp hiS).1
  have hix : Fr.fr a i ≤ x := (Finset.mem_filter.mp hiS).2
  by_cases hlast : i + 1 < r
  · have hnot : ¬ (Fr.fr a (i + 1) ≤ x) := by
      intro hle
      have hmem : i + 1 ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlast, hle⟩
      have := himax _ hmem
      omega
    push_neg at hnot
    rcases lt_or_eq_of_le hix with hlt | heq
    · exact absurd hx (hgap a i x hlast hlt hnot)
    · exact ⟨i, hir, heq.symm⟩
  · have hi1 : i = r - 1 := by omega
    refine ⟨i, hir, le_antisymm ?_ hix⟩
    rw [hi1]
    exact h1

theorem llPos_mem (j : ℤ) (l : ℕ) (hl : l < (Fr.LLset j).card) : llPos Fr j l ∈ Fr.LLset j := by
  unfold llPos
  have hlen : l < ((Fr.LLset j).sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hl
  rw [List.getD_eq_getElem _ _ hlen]
  exact (Finset.mem_sort _).mp (List.getElem_mem hlen)

theorem llPos_inj (j : ℤ) {l l' : ℕ} (hl : l < (Fr.LLset j).card) (hl' : l' < (Fr.LLset j).card)
    (h : llPos Fr j l = llPos Fr j l') : l = l' := by
  unfold llPos at h
  have hl1 : l < ((Fr.LLset j).sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hl
  have hl2 : l' < ((Fr.LLset j).sort (· ≤ ·)).length := by rw [Finset.length_sort]; exact hl'
  rw [List.getD_eq_getElem _ _ hl1, List.getD_eq_getElem _ _ hl2] at h
  exact (List.Nodup.getElem_inj_iff (Finset.sort_nodup _ _)).mp h

theorem exists_llPos (j x : ℤ) (hx : x ∈ Fr.LLset j) :
    ∃ l, l < (Fr.LLset j).card ∧ llPos Fr j l = x := by
  have hx' : x ∈ (Fr.LLset j).sort (· ≤ ·) := (Finset.mem_sort _).mpr hx
  obtain ⟨l, hl, hlx⟩ := List.getElem_of_mem hx'
  refine ⟨l, by rwa [Finset.length_sort] at hl, ?_⟩
  unfold llPos
  rw [List.getD_eq_getElem _ _ hl, hlx]

theorem posOf_add_n (x : ℤ) : posOf n' (x + n') = posOf n' x := by
  apply Fin.ext
  simp [posOf]

theorem shift (hper : ∀ j : ℤ, ∀ i, Fr.fr (j + Fr.J) i = Fr.fr j i + n') {J : ℕ} [NeZero J] (hJ : J = Fr.J)
    (j : ZMod J) :
    ∃ s : ℤ, (s = 0 ∨ s = n') ∧ ∀ k, Fr.fr (segZ j) k = Fr.fr (segZ (j + 1) - 1) k + s ∧
      Fr.fr (segZ j + 1) k = Fr.fr (segZ (j + 1)) k + s := by
  have hv : (j + 1 : ZMod J).val = (j.val + 1) % J := by
    rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod]
  have hjlt : j.val < J := ZMod.val_lt j
  unfold segZ
  rcases Nat.lt_or_ge (j.val + 1) J with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at hv
    refine ⟨0, Or.inl rfl, fun k => ?_⟩
    rw [hv]
    push_cast
    simp
  · have heq : j.val + 1 = J := by omega
    rw [heq, Nat.mod_self] at hv
    refine ⟨n', Or.inr rfl, fun k => ?_⟩
    rw [hv]
    have e1 : ((j.val : ℕ) : ℤ) = (-1 : ℤ) + (Fr.J : ℤ) := by rw [← hJ]; omega
    have e2 : ((j.val : ℕ) : ℤ) + 1 = (0 : ℤ) + (Fr.J : ℤ) := by rw [← hJ]; omega
    constructor
    · rw [e1, hper]; simp
    · rw [e2, hper]; simp

end Fr

section Ph

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ}

def eV (Dt : SignedChainData p O r J) : ML J Dt.nL r × Fin r → (TL J Dt.nL r × Fin r →₀ ℕ)
  | (ML.ll j l, a) => Finsupp.single (⟨j, Sum.inl l⟩, a) 1
  | (ML.lab j m, a) => Finsupp.single (⟨j, Sum.inr m⟩, a) 1
  | (ML.wc j m, a) => Finsupp.single (⟨j, Sum.inr m⟩, a) (Dt.P j m)
  | (ML.tp j m _, a) => Finsupp.single (⟨j, Sum.inr m⟩, a) 1

theorem ph_monomial_one (Dt : SignedChainData p O r J) (mo : ML J Dt.nL r × Fin r →₀ ℕ) :
    Dt.ph (monomial mo (1 : KK O)) = monomial (∑ v ∈ mo.support, mo v • eV Dt v) 1 := by
  have hX : ∀ v, Dt.ph (X v) = monomial (eV Dt v) (1 : KK O) := by
    rintro ⟨y, a⟩
    cases y <;> simp only [SignedChainData.ph, MvPolynomial.aeval_X, eV]
    all_goals first
      | rfl
      | exact MvPolynomial.X_pow_eq_monomial
  rw [MvPolynomial.monomial_eq, MvPolynomial.C_1, one_mul, Finsupp.prod, map_prod]
  simp only [map_pow, hX, MvPolynomial.monomial_pow, one_pow]
  rw [MvPolynomial.monomial_sum_one]

theorem le_multideg (Dt : SignedChainData p O r J) (mo : ML J Dt.nL r × Fin r →₀ ℕ) (y0 : ML J Dt.nL r)
    (t : TL J Dt.nL r) (k : ℕ) (he : ∀ c, eV Dt (y0, c) = Finsupp.single (t, c) k) :
    k * ∑ c, mo (y0, c) ≤ multideg (∑ v ∈ mo.support, mo v • eV Dt v) t := by
  unfold multideg
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [Finsupp.finset_sum_apply]
  by_cases hc : (y0, c) ∈ mo.support
  · calc k * mo (y0, c) = (mo (y0, c) • eV Dt (y0, c)) (t, c) := by
          rw [he c, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ mo.support, (mo v • eV Dt v) (t, c) :=
          Finset.single_le_sum (f := fun v => (mo v • eV Dt v) (t, c)) (fun _ _ => Nat.zero_le _) hc
  · have h0 : mo (y0, c) = 0 := by rw [Finsupp.mem_support_iff, not_not] at hc; exact hc
    rw [h0, mul_zero]
    exact Nat.zero_le _

end Ph

end DdG

open DdG in

theorem restDdG_holds : RestDdG := by
  intro p _ n' r K _ _ _ O _ _ _ _S Fr TT L₁ L₂ N₁ G' deg d Y cP hF J _ Dt dPl dNo ka rho No Go hMH
  obtain ⟨⟨hTied, -, -⟩, hBlock, -, -, hPol⟩ := hMH
  obtain ⟨hJ, hnL, -, hdd, hgP, -⟩ := hTied
  have hr : 2 ≤ r := hF.two_le_r
  obtain ⟨-, hval, -⟩ := hF.frames
  obtain ⟨-, hper, hmono, hsep, -, hgap, -⟩ := hval
  have hdeg : ∀ s, d s ≤ deg s := fun s => by
    by_cases hs : s ∈ Fr.TT
    · exact (hF.d_top s hs).le
    · rw [hF.d_off s hs]; exact Nat.zero_le _
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hblk : ∀ t : TL J Dt.nL r, lowP Fr p t * (dPl t + dNo t) ≤ deg (posOf n' (posTL Fr t)) := fun t =>
    calc lowP Fr p t * (dPl t + dNo t) ≤ ∑ c, rho (t, c) + lowP Fr p t * (dPl t + dNo t) := Nat.le_add_left _ _
      _ = d (posOf n' (posTL Fr t)) := hBlock.2 t
      _ ≤ deg (posOf n' (posTL Fr t)) := hdeg _
  intro δ hocc j x hx hWL
  obtain ⟨mo', hmo', hδ⟩ := hocc
  obtain ⟨mo, hmo, rfl⟩ : ∃ mo ∈ Go.support,
      Finsupp.mapDomain (fun v : ML J Dt.nL r × Fin r => (mlPos Fr Dt.nL v.1, v.2)) mo = mo' := by
    by_contra hne
    simp only [not_exists, not_and] at hne
    apply (mem_support_iff.1 hmo')
    unfold xiPl
    exact coeff_rename_eq_zero _ _ _ fun u hu => by
      by_contra hc
      exact hne u (mem_support_iff.2 hc) hu
  have hEd : ∀ i, multideg (∑ v ∈ mo.support, mo v • eV Dt v) i = dPl i := by
    intro i
    have hE := hPol mo hmo
    rw [DdG.ph_monomial_one] at hE
    rw [← hdd]
    exact DdG.multideg_of_mem_Pol hE i
  have hsepj : Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) 0 := by
    have := hsep (segZ j - 1)
    rwa [sub_add_cancel] at this
  have hLL : ∀ (j' : ZMod J) (l : Fin (Dt.nL j')),
      Fr.fr (segZ j' - 1) (r - 1) < llPos Fr (segZ j') l.val ∧ llPos Fr (segZ j') l.val < Fr.fr (segZ j') 0 := by
    intro j' l
    have hm := DdG.llPos_mem Fr (segZ j') l.val (by rw [← hnL j']; exact l.2)
    unfold Frames.LLset at hm
    rw [Finset.mem_filter, Finset.mem_Ioo] at hm
    exact hm.1
  rcases hWL with hW | hL
  ·
    unfold Frames.letters at hx
    rw [Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨i, hi, rfl⟩ := DdG.eq_fr Fr hgap (by omega) (segZ j - 1) x hx.1.1 hW hx.2
    obtain ⟨m, hmv⟩ : ∃ m : Fin r, m.val = r - 1 - i := ⟨⟨r - 1 - i, by omega⟩, rfl⟩
    have hmi : r - 1 - m.val = i := by omega
    have hAB : Fr.fr (segZ j - 1) i ≤ Fr.fr (segZ j - 1) (r - 1) := DdG.fr_le Fr hmono _ (by omega) (by omega)
    have hU : ∀ y : ML J Dt.nL r, mlPos Fr Dt.nL y = (j, Fr.fr (segZ j - 1) i) → y = ML.wc (j - 1) m := by
      intro y hy
      cases y with
      | ll j'' l =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨rfl, h2⟩ := hy
        have := (hLL j'' l).1
        omega
      | lab j'' m' =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨rfl, h2⟩ := hy
        have := DdG.fr_le Fr hmono (segZ j'') (Nat.zero_le (r - 1 - m'.val)) (by omega)
        omega
      | wc j'' m' =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨h1, h2⟩ := hy
        obtain rfl : j'' = j - 1 := eq_sub_of_add_eq h1
        rw [sub_add_cancel] at h2
        have := DdG.fr_inj Fr hmono (segZ j - 1) (show r - 1 - m'.val < r by omega) hi h2
        have := m'.2
        congr 1
        exact Fin.ext (by omega)
      | tp j'' m' h =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨rfl, h2⟩ := hy
        have := DdG.fr_le Fr hmono (segZ j'') (Nat.zero_le (r - 1 - m'.val)) (by omega)
        omega
    have hV : ∀ t : TL J Dt.nL r, tlPos Fr Dt.nL t ≠ (j, Fr.fr (segZ j - 1) i) := by
      rintro ⟨j'', l | m'⟩ ht
      · simp only [tlPos, posTL, Prod.mk.injEq] at ht
        obtain ⟨rfl, h2⟩ := ht
        have := (hLL j'' l).1
        omega
      · simp only [tlPos, posTL, Prod.mk.injEq] at ht
        obtain ⟨rfl, h2⟩ := ht
        have := DdG.fr_le Fr hmono (segZ j'') (Nat.zero_le (r - 1 - m'.val)) (by omega)
        omega
    have h1 : δ (j, Fr.fr (segZ j - 1) i) ≤ ∑ c, mo (ML.wc (j - 1) m, c) := by
      rw [← hδ]
      exact DdG.multideg_mapDomain_le _ mo _ _ hU
    have h2 : dNoOf p O Fr Dt dNo (j, Fr.fr (segZ j - 1) i) = 0 := by unfold dNoOf; convert DdG.sumIteZero _ dNo _ hV
    have h3 : Dt.P (j - 1) m * ∑ c, mo (ML.wc (j - 1) m, c) ≤ dPl ⟨j - 1, Sum.inr m⟩ := by
      rw [← hEd]
      exact DdG.le_multideg Dt mo _ _ _ fun c => rfl
    have h4 := hblk ⟨j - 1, Sum.inr m⟩
    obtain ⟨s, hs, hsh⟩ := DdG.shift Fr hper hJ (j - 1)
    rw [sub_add_cancel] at hsh
    have hposTL : posTL Fr (⟨j - 1, Sum.inr m⟩ : TL J Dt.nL r) = Fr.fr (segZ j - 1) i + s := by
      show Fr.fr (segZ (j - 1)) (r - 1 - m.val) = _
      rw [hmi, (hsh i).1]
    have hlow : lowP Fr p (⟨j - 1, Sum.inr m⟩ : TL J Dt.nL r) =
        p ^ (Fr.fr (segZ j - 1) (r - 1) - Fr.fr (segZ j - 1) i).toNat := by
      show p ^ (Fr.fr (segZ (j - 1)) (r - 1) - posTL Fr (⟨j - 1, Sum.inr m⟩ : TL J Dt.nL r)).toNat = _
      rw [hposTL, (hsh (r - 1)).1]
      congr 2
      ring
    have hP : Dt.P (j - 1) m = p ^ (Fr.fr (segZ j) (r - 1) - Fr.fr (segZ j - 1) (r - 1)).toNat := by
      unfold SignedChainData.P
      rw [hgP, (hsh (r - 1)).1, (hsh (r - 1)).2]
      congr 2
      ring
    have hpos : posOf n' (posTL Fr (⟨j - 1, Sum.inr m⟩ : TL J Dt.nL r)) = posOf n' (Fr.fr (segZ j - 1) i) := by
      rw [hposTL]
      rcases hs with rfl | rfl
      · simp
      · exact DdG.posOf_add_n _
    have hBC : Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) (r - 1) :=
      hsepj.trans_le (DdG.fr_le Fr hmono _ (Nat.zero_le _) (by omega))
    have hexp : (Fr.fr (segZ j - 1) (r - 1) - Fr.fr (segZ j - 1) i).toNat +
        (Fr.fr (segZ j) (r - 1) - Fr.fr (segZ j - 1) (r - 1)).toNat =
        (Fr.fr (segZ j) (r - 1) - Fr.fr (segZ j - 1) i).toNat := by
      rw [← Int.toNat_add (by linarith) (by linarith)]
      congr 1
      ring
    rw [hlow, hpos] at h4
    rw [hP] at h3
    have hnat : p ^ (Fr.fr (segZ j) (r - 1) - Fr.fr (segZ j - 1) i).toNat *
        (δ (j, Fr.fr (segZ j - 1) i) + dNoOf p O Fr Dt dNo (j, Fr.fr (segZ j - 1) i)) ≤
        deg (posOf n' (Fr.fr (segZ j - 1) i)) := by
      rw [h2, add_zero, ← hexp, pow_add]
      calc _ ≤ p ^ (Fr.fr (segZ j - 1) (r - 1) - Fr.fr (segZ j - 1) i).toNat *
              p ^ (Fr.fr (segZ j) (r - 1) - Fr.fr (segZ j - 1) (r - 1)).toNat * ∑ c, mo (ML.wc (j - 1) m, c) :=
            Nat.mul_le_mul_left _ h1
        _ ≤ p ^ (Fr.fr (segZ j - 1) (r - 1) - Fr.fr (segZ j - 1) i).toNat * dPl ⟨j - 1, Sum.inr m⟩ := by
            rw [mul_assoc]; exact Nat.mul_le_mul_left _ h3
        _ ≤ p ^ (Fr.fr (segZ j - 1) (r - 1) - Fr.fr (segZ j - 1) i).toNat *
              (dPl ⟨j - 1, Sum.inr m⟩ + dNo ⟨j - 1, Sum.inr m⟩) := Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
        _ ≤ _ := h4
    unfold levDeg Frames.dist
    exact DdG.real_le hp _ _ _ hnat
  ·
    obtain ⟨l0, hl0, hxl⟩ := DdG.exists_llPos Fr (segZ j) x hL
    have hl0' : l0 < Dt.nL j := by rw [hnL j]; exact hl0
    have hxI : Fr.fr (segZ j - 1) (r - 1) < x ∧ x < Fr.fr (segZ j) 0 := by
      have hm := hL
      unfold Frames.LLset at hm
      rw [Finset.mem_filter, Finset.mem_Ioo] at hm
      exact hm.1
    have hU : ∀ y : ML J Dt.nL r, mlPos Fr Dt.nL y = (j, x) → y = ML.ll j ⟨l0, hl0'⟩ := by
      intro y hy
      cases y with
      | ll j'' l =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨rfl, h2⟩ := hy
        have := DdG.llPos_inj Fr (segZ j'') (by rw [← hnL]; exact l.2) hl0 (h2.trans hxl.symm)
        congr 1
        exact Fin.ext this
      | lab j'' m' =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨rfl, h2⟩ := hy
        have := DdG.fr_le Fr hmono (segZ j'') (Nat.zero_le (r - 1 - m'.val)) (by omega)
        omega
      | wc j'' m' =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨h1, h2⟩ := hy
        obtain rfl : j'' = j - 1 := eq_sub_of_add_eq h1
        rw [sub_add_cancel] at h2
        have := DdG.fr_le Fr hmono (segZ j - 1) (show r - 1 - m'.val ≤ r - 1 by omega) (by omega)
        omega
      | tp j'' m' h =>
        simp only [mlPos, Prod.mk.injEq] at hy
        obtain ⟨rfl, h2⟩ := hy
        have := DdG.fr_le Fr hmono (segZ j'') (Nat.zero_le (r - 1 - m'.val)) (by omega)
        omega
    have hV : ∀ t : TL J Dt.nL r, tlPos Fr Dt.nL t = (j, x) → t = ⟨j, Sum.inl ⟨l0, hl0'⟩⟩ := by
      rintro ⟨j'', l | m'⟩ ht
      · simp only [tlPos, posTL, Prod.mk.injEq] at ht
        obtain ⟨rfl, h2⟩ := ht
        have := DdG.llPos_inj Fr (segZ j'') (by rw [← hnL]; exact l.2) hl0 (h2.trans hxl.symm)
        rw [show l = ⟨l0, hl0'⟩ from Fin.ext this]
      · simp only [tlPos, posTL, Prod.mk.injEq] at ht
        obtain ⟨rfl, h2⟩ := ht
        have := DdG.fr_le Fr hmono (segZ j'') (Nat.zero_le (r - 1 - m'.val)) (by omega)
        omega
    have h1 : δ (j, x) ≤ ∑ c, mo (ML.ll j ⟨l0, hl0'⟩, c) := by
      rw [← hδ]
      exact DdG.multideg_mapDomain_le _ mo _ _ hU
    have h1' : ∑ c, mo (ML.ll j ⟨l0, hl0'⟩, c) ≤ dPl ⟨j, Sum.inl ⟨l0, hl0'⟩⟩ := by
      have := DdG.le_multideg Dt mo (ML.ll j ⟨l0, hl0'⟩) ⟨j, Sum.inl ⟨l0, hl0'⟩⟩ 1 fun c => rfl
      rwa [hEd, one_mul] at this
    have h2 : dNoOf p O Fr Dt dNo (j, x) ≤ dNo ⟨j, Sum.inl ⟨l0, hl0'⟩⟩ := by unfold dNoOf; convert DdG.sumIteLe _ dNo _ _ hV
    have h4 := hblk ⟨j, Sum.inl ⟨l0, hl0'⟩⟩
    have hposTL : posTL Fr (⟨j, Sum.inl ⟨l0, hl0'⟩⟩ : TL J Dt.nL r) = x := hxl
    have hlow : lowP Fr p (⟨j, Sum.inl ⟨l0, hl0'⟩⟩ : TL J Dt.nL r) = p ^ (Fr.fr (segZ j) (r - 1) - x).toNat := by
      show p ^ (Fr.fr (segZ j) (r - 1) - posTL Fr (⟨j, Sum.inl ⟨l0, hl0'⟩⟩ : TL J Dt.nL r)).toNat = _
      rw [hposTL]
    rw [hlow, hposTL] at h4
    have hnat : p ^ (Fr.fr (segZ j) (r - 1) - x).toNat * (δ (j, x) + dNoOf p O Fr Dt dNo (j, x)) ≤
        deg (posOf n' x) :=
      (Nat.mul_le_mul_left _ (Nat.add_le_add (h1.trans h1') h2)).trans h4
    unfold levDeg Frames.dist
    exact DdG.real_le hp _ _ _ hnat

end Formalism.MainNotions.Proposition5Numerics
