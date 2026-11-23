import Formalism.SharpRestriction.GrowthBounds.PolynomialLevels.TlNonempty
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.PreChainLe
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDd
import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MemSupportSumMonomial

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.NormalSetCounting

open Formalism.MainNotions.G Formalism.GradedWeylDivisibility Formalism.MainNotions.SourceCleaning Formalism.MainNotions.Pf14 Formalism.MainNotions.PlaneGramData Formalism.MainNotions.TestSideCounting Formalism.MainNotions.TestSideWords Formalism.MainNotions.Proposition5Numerics Formalism.MainNotions.PairMembershipBlocks

section Congr

variable {R : Type} [CommRing R] {ι : Type} {n : ℕ}

theorem twistSub_congr (LL LL' : Letters ι) (S S' : Set ι) (j : Fin n) (F : MvPolynomial (ι × Fin n) R)
    (h : ∀ v ∈ F.vars, (v.1 ∈ S ↔ v.1 ∈ S') ∧ LL.vec v.1 = LL'.vec v.1) :
    twistSub LL S j F = twistSub LL' S' j F := by
  apply MvPolynomial.hom_congr_vars _ _ rfl
  · exact RingHom.ext fun a => by simp [twistSub]
  · intro v hv _
    obtain ⟨h1, h2⟩ := h v hv
    simp only [twistSub, coe_eval₂Hom, eval₂_X, h2]
    by_cases hs : v.1 ∈ S
    · simp [hs, h1.mp hs]
    · simp [hs, mt h1.mpr hs]

theorem lowest_weight_congr [NeZero n] (LL LL' : Letters ι) (S S' : Set ι) (F : MvPolynomial (ι × Fin n) R)
    (h : ∀ v ∈ F.vars, (v.1 ∈ S ↔ v.1 ∈ S') ∧ LL.vec v.1 = LL'.vec v.1) :
    lam1S LL S F = lam1S LL' S' F := by
  simp only [lam1S, sDegs, twistSub_congr LL LL' S S' 0 F h]

theorem lowest_weight_nonpos_off_set [NeZero n] (LL : Letters ι) (S : Set ι) (F : MvPolynomial (ι × Fin n) R)
    (h : ∀ v ∈ F.vars, v.1 ∉ S) : lam1S LL S F ≤ 0 := by
  rw [lowest_weight_congr LL LL S ∅ F (fun v hv => ⟨by simp [h v hv], rfl⟩)]
  have h0 := (Joints.StandardMonomialSpace.lowest_degree_le_iff LL ∅ F 0).mpr
    (fun k hk => le_of_eq (by simpa using Joints.StandardMonomialSpace.sDegs_empty_subset LL 0 F k hk))
  simpa using h0

end Congr

section Geo

variable {n' r : ℕ} [NeZero n'] [NeZero r] {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] {nL : ZMod J → ℕ}

private theorem posTL_mem_Ioc_fr_last (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (t : TL J nL r) :
    Fr.fr (segZ t.1 - 1) (r - 1) < posTL Fr t ∧ posTL Fr t ≤ Fr.fr (segZ t.1) (r - 1) := by
  have hr : 0 < r := NeZero.pos r
  have hmono := hV.2.2.1
  obtain ⟨j, s⟩ := t
  have hgap : Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) 0 := by
    have h := hV.2.2.2.1 (segZ j - 1)
    simpa using h
  cases s with
  | inl l =>
    have hmem := DdG.llPos_mem Fr (segZ j) l.val (by rw [← hnL j]; exact l.isLt)
    simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem
    have h0 : Fr.fr (segZ j) 0 ≤ Fr.fr (segZ j) (r - 1) := DdG.fr_le Fr hmono (segZ j) (Nat.zero_le _) (by omega)
    show Fr.fr (segZ j - 1) (r - 1) < llPos Fr (segZ j) l.val ∧ llPos Fr (segZ j) l.val ≤ Fr.fr (segZ j) (r - 1)
    exact ⟨hmem.1.1, by linarith [hmem.1.2]⟩
  | inr m =>
    have hm := m.isLt
    show Fr.fr (segZ j - 1) (r - 1) < Fr.fr (segZ j) (r - 1 - m.val) ∧
      Fr.fr (segZ j) (r - 1 - m.val) ≤ Fr.fr (segZ j) (r - 1)
    exact ⟨lt_of_lt_of_le hgap (DdG.fr_le Fr hmono (segZ j) (Nat.zero_le _) (by omega)),
      DdG.fr_le Fr hmono (segZ j) (by omega) (by omega)⟩

private theorem fr_last_strictMono (hV : Fr.Valid L₁ N₁) : StrictMono (fun s : ℤ => Fr.fr s (r - 1)) := by
  have hr : 0 < r := NeZero.pos r
  apply strictMono_int_of_lt_succ
  intro s
  exact lt_of_lt_of_le (hV.2.2.2.1 s) (DdG.fr_le Fr hV.2.2.1 (s + 1) (Nat.zero_le _) (by omega))

private theorem posTL_injective (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) :
    Function.Injective (posTL Fr : TL J nL r → ℤ) := by
  have hr : 0 < r := NeZero.pos r
  have hmono := hV.2.2.1
  have hsm := fr_last_strictMono hV
  have hseg : ∀ t t' : TL J nL r, posTL Fr t = posTL Fr t' → segZ t.1 ≤ segZ t'.1 := by
    intro t t' h
    by_contra hlt
    push_neg at hlt
    have h1 := posTL_mem_Ioc_fr_last hV hnL t
    have h2 := posTL_mem_Ioc_fr_last hV hnL t'
    have h3 : Fr.fr (segZ t'.1) (r - 1) ≤ Fr.fr (segZ t.1 - 1) (r - 1) := hsm.monotone (by omega)
    linarith [h1.1, h2.2]
  intro t t' h
  have hj : t.1 = t'.1 := by
    have h4 := le_antisymm (hseg t t' h) (hseg t' t h.symm)
    unfold segZ at h4
    exact ZMod.val_injective J (by exact_mod_cast h4)
  obtain ⟨j, s⟩ := t
  obtain ⟨j', s'⟩ := t'
  simp only at hj
  subst hj
  cases s with
  | inl l =>
    cases s' with
    | inl l' =>
      have h' : llPos Fr (segZ j) l.val = llPos Fr (segZ j) l'.val := h
      have he := DdG.llPos_inj Fr (segZ j) (by rw [← hnL j]; exact l.isLt) (by rw [← hnL j]; exact l'.isLt) h'
      rw [Fin.ext he]
    | inr m =>
      exfalso
      have hm := m.isLt
      have h' : llPos Fr (segZ j) l.val = Fr.fr (segZ j) (r - 1 - m.val) := h
      have hmem := DdG.llPos_mem Fr (segZ j) l.val (by rw [← hnL j]; exact l.isLt)
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem
      have h5 := DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)
      linarith [hmem.1.2]
  | inr m =>
    cases s' with
    | inl l' =>
      exfalso
      have hm := m.isLt
      have h' : Fr.fr (segZ j) (r - 1 - m.val) = llPos Fr (segZ j) l'.val := h
      have hmem := DdG.llPos_mem Fr (segZ j) l'.val (by rw [← hnL j]; exact l'.isLt)
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hmem
      have h5 := DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (r - 1 - m.val)) (by omega)
      linarith [hmem.1.2]
    | inr m' =>
      have hm := m.isLt
      have hm' := m'.isLt
      have h' : Fr.fr (segZ j) (r - 1 - m.val) = Fr.fr (segZ j) (r - 1 - m'.val) := h
      have he := DdG.fr_inj Fr hmono (segZ j) (by omega) (by omega) h'
      have hmm : m = m' := Fin.ext (by omega)
      rw [hmm]

theorem gT_posTL (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (t : TL J nL r) :
    gT Fr nL (posTL Fr t) = t := by
  unfold gT
  exact Function.leftInverse_invFun (posTL_injective hV hnL) t

theorem tl_surj (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (x : ℤ)
    (hx : x ∈ Fr.letters (segZ j)) (hW : ¬ Fr.IsW (segZ j) x) : ∃ s, posTL Fr (⟨j, s⟩ : TL J nL r) = x := by
  have hr : 0 < r := NeZero.pos r
  have hl := hx
  simp only [Frames.letters, Finset.mem_filter, Finset.mem_Icc] at hl
  have hw : Fr.fr (segZ j - 1) (r - 1) < x := by
    unfold Frames.IsW at hW
    push_neg at hW
    exact hW
  by_cases hlt : x < Fr.fr (segZ j) 0
  · have hLL : x ∈ Fr.LLset (segZ j) := by
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo]
      exact ⟨⟨hw, hlt⟩, hl.2⟩
    obtain ⟨l, hl1, hl2⟩ := DdG.exists_llPos Fr (segZ j) x hLL
    exact ⟨Sum.inl ⟨l, by rw [hnL j]; exact hl1⟩, hl2⟩
  · push_neg at hlt
    obtain ⟨i, hi, hxi⟩ := DdG.eq_fr Fr hV.2.2.2.2.2.1 (by omega) (segZ j) x hlt hl.1.2 hl.2
    refine ⟨Sum.inr ⟨r - 1 - i, by omega⟩, ?_⟩
    show Fr.fr (segZ j) (r - 1 - (r - 1 - i)) = x
    rw [hxi]
    congr 1
    omega

theorem segZ_natCast (i : ℕ) (hi : i < J) : segZ ((i : ℕ) : ZMod J) = (i : ℤ) := by
  unfold segZ
  rw [ZMod.val_natCast_of_lt hi]

theorem tl_surj' (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (i : ℕ)
    (hi : i < Fr.J) (x : ℤ) (hx : x ∈ Fr.letters i) (hW : ¬ Fr.IsW i x) :
    ∃ t : TL J nL r, segZ t.1 = (i : ℤ) ∧ posTL Fr t = x := by
  have hiJ : i < J := by rw [hJ]; exact hi
  have hs := segZ_natCast (J := J) i hiJ
  have hx' : x ∈ Fr.letters (segZ ((i : ℕ) : ZMod J)) := by rw [hs]; exact hx
  have hW' : ¬ Fr.IsW (segZ ((i : ℕ) : ZMod J)) x := by rw [hs]; exact hW
  obtain ⟨s, hs2⟩ := tl_surj hV hnL ((i : ℕ) : ZMod J) x hx' hW'
  exact ⟨⟨(i : ZMod J), s⟩, hs, hs2⟩

theorem mem_NSet_inl (j : ZMod J) (l : Fin (nL j)) (u : ℕ) :
    (⟨j, Sum.inl l⟩ : TL J nL r) ∈ NSet nL j u ↔ l.val < u := by
  simp [NSet]

theorem mem_NSet_inr (j : ZMod J) (m : Fin r) (u : ℕ) :
    (⟨j, Sum.inr m⟩ : TL J nL r) ∈ NSet nL j u ↔ nL j + (r - 1 - m.val) < u := by
  simp [NSet]

theorem mem_NSet_fst {j : ZMod J} {u : ℕ} {t : TL J nL r} (h : t ∈ NSet nL j u) : t.1 = j := by
  rcases h with ⟨l, rfl, _⟩ | ⟨m, rfl, _⟩ <;> rfl

private theorem posU_strictMono (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (a b : ℕ) (hab : a < b) (hb : b < nL j + r) :
    posU Fr (nL j) (segZ j) a < posU Fr (nL j) (segZ j) b := by
  have hmono := hV.2.2.1
  unfold posU
  by_cases hb' : b < nL j
  · have ha' : a < nL j := lt_trans hab hb'
    rw [if_pos ha', if_pos hb']
    exact Formalism.MainNotions.Proposition5Numerics.llPos_lt _ _ _ hab (by rw [← hnL j]; exact hb')
  · rw [if_neg hb']
    by_cases ha' : a < nL j
    · rw [if_pos ha']
      have hm := Formalism.MainNotions.Proposition5Numerics.llPos_mem Fr (segZ j) a (by rw [← hnL j]; exact ha')
      simp only [Frames.LLset, Finset.mem_filter, Finset.mem_Ioo] at hm
      have h2 := Formalism.MainNotions.Proposition5Numerics.DdG.fr_le Fr hmono (segZ j) (Nat.zero_le (b - nL j)) (by omega)
      exact lt_of_lt_of_le hm.1.2 h2
    · rw [if_neg ha']
      exact Formalism.MainNotions.Proposition5Numerics.DdG.fr_lt Fr hmono (segZ j) (by omega) (by omega)

private theorem posU_lt_posU_iff (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (a b : ℕ) (ha : a < nL j + r) (hb : b < nL j + r) :
    posU Fr (nL j) (segZ j) a < posU Fr (nL j) (segZ j) b ↔ a < b := by
  constructor
  · intro h
    by_contra hc
    rcases (not_lt.mp hc).lt_or_eq with hc | hc
    · exact lt_asymm h (posU_strictMono hV hnL j b a hc ha)
    · subst hc
      exact lt_irrefl _ h
  · intro h
    exact posU_strictMono hV hnL j a b h hb

private theorem posU_le_posU_iff (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (a b : ℕ) (ha : a < nL j + r) (hb : b < nL j + r) :
    posU Fr (nL j) (segZ j) a ≤ posU Fr (nL j) (segZ j) b ↔ a ≤ b := by
  rw [← not_lt, ← not_lt, posU_lt_posU_iff hV hnL j b a hb ha]

theorem NSet_lt (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (s : Fin (nL j) ⊕ Fin r) :
    (⟨j, s⟩ : TL J nL r) ∈ NSet nL j u ↔ posTL Fr (⟨j, s⟩ : TL J nL r) < posU Fr (nL j) (segZ j) u := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  cases s with
  | inl l =>
    rw [mem_NSet_inl]
    have hl := l.isLt
    have hp : posTL Fr (⟨j, Sum.inl l⟩ : TL J nL r) = posU Fr (nL j) (segZ j) l.val := by
      simp [posTL, posU, l.isLt]
    rw [hp, posU_lt_posU_iff hV hnL j _ _ (by omega) hu]
  | inr m =>
    rw [mem_NSet_inr]
    have hp : posTL Fr (⟨j, Sum.inr m⟩ : TL J nL r) = posU Fr (nL j) (segZ j) (nL j + (r - 1 - m.val)) := by
      simp [posTL, posU]
    rw [hp, posU_lt_posU_iff hV hnL j _ _ (by omega) hu]

theorem NSet_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card) (j : ZMod J) (u : ℕ)
    (hu : u < nL j + r) (s : Fin (nL j) ⊕ Fin r) :
    (⟨j, s⟩ : TL J nL r) ∈ NSet nL j (u + 1) ↔ posTL Fr (⟨j, s⟩ : TL J nL r) ≤ posU Fr (nL j) (segZ j) u := by
  have hr : 0 < r := Nat.pos_of_ne_zero (NeZero.ne r)
  cases s with
  | inl l =>
    rw [mem_NSet_inl, Nat.lt_succ_iff]
    have hl := l.isLt
    have hp : posTL Fr (⟨j, Sum.inl l⟩ : TL J nL r) = posU Fr (nL j) (segZ j) l.val := by
      simp [posTL, posU, l.isLt]
    rw [hp, posU_le_posU_iff hV hnL j _ _ (by omega) hu]
  | inr m =>
    rw [mem_NSet_inr, Nat.lt_succ_iff]
    have hp : posTL Fr (⟨j, Sum.inr m⟩ : TL J nL r) = posU Fr (nL j) (segZ j) (nL j + (r - 1 - m.val)) := by
      simp [posTL, posU]
    rw [hp, posU_le_posU_iff hV hnL j _ _ (by omega) hu]

end Geo

section Fac

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {n' r : ℕ} [NeZero n'] [NeZero r]
  {Fr : Frames n' r} {L₁ N₁ : ℕ} {J : ℕ} [NeZero J] (Dt : SignedChainData p O r J) {K : ℕ} [NeZero K]

theorem trueLet_vec (hV : Fr.Valid L₁ N₁) (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val)))
    (t : TL J Dt.nL r) : Dt.trueLet.vec t = LZ.vec (posTL Fr t) := by
  obtain ⟨j, l | m⟩ := t
  · simp only [SignedChainData.trueLet, LZ, posTL]
    exact hsgn j l
  · simp only [SignedChainData.trueLet, LZ, posTL]
    have h := (hV.2.2.2.2.1 (segZ j) (r - 1 - m.val) (by have := NeZero.pos r; omega)).2
    simp [h]

private theorem exists_gT_eq_and_posTL_eq_of_not_isW (hV : Fr.Valid L₁ N₁) {nL : ZMod J → ℕ} (hnL : ∀ j, nL j = (Fr.LLset (segZ j)).card)
    (j : ZMod J) (x : ℤ) (hx : x ∈ Fr.letters (segZ j)) (hW : ¬ Fr.IsW (segZ j) x) :
    ∃ s, gT Fr nL x = (⟨j, s⟩ : TL J nL r) ∧ posTL Fr (⟨j, s⟩ : TL J nL r) = x := by
  obtain ⟨s, hs⟩ := tl_surj hV hnL j x hx hW
  exact ⟨s, by rw [← hs, gT_posTL hV hnL], hs⟩

theorem Rn_vars (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card) (j : ZMod J)
    (A : MvPolynomial (ℤ × Fin K) O)
    (hA : A ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) v.1}) :
    ∀ v ∈ (Rn Fr Dt.nL A).vars, v.1.1 = j := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (vars_rename _ _ hv)
  have hw' : w ∈ A.vars := vars_map _ _ hw
  obtain ⟨hx, hW⟩ := (mem_supported.mp hA) hw'
  obtain ⟨s, hs, -⟩ := exists_gT_eq_and_posTL_eq_of_not_isW hV hnL j w.1 hx hW
  simp [hs]

theorem lam_Rn_le (hV : Fr.Valid L₁ N₁) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val))) (j : ZMod J)
    (A : MvPolynomial (ℤ × Fin K) O)
    (hA : A ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) v.1})
    (S : Set (TL J Dt.nL r)) (Sz : Set ℤ)
    (hS : ∀ s, (⟨j, s⟩ : TL J Dt.nL r) ∈ S ↔ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) ∈ Sz) :
    lam1S Dt.trueLet S (Rn Fr Dt.nL A) ≤ lam1S LZ Sz A := by
  have hinj : Function.Injective (algebraMap O (KK O)) := IsFractionRing.injective O (FractionRing O)
  obtain ⟨A', rfl⟩ : ∃ A' : MvPolynomial ({x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K) O,
      rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (v.1.val, v.2)) A' = A := by
    refine exists_rename_eq_of_vars_subset_range A _ ?_ ?_
    · rintro ⟨a, b⟩ ⟨c, d⟩ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext (Subtype.ext h.1) h.2
    · intro v hv
      obtain ⟨hx, hW⟩ := (mem_supported.mp hA) hv
      exact ⟨(⟨v.1, hx, hW⟩, v.2), rfl⟩
  have hgood : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      ∃ s, gT Fr Dt.nL i.val = (⟨j, s⟩ : TL J Dt.nL r) ∧ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) = i.val :=
    fun i => exists_gT_eq_and_posTL_eq_of_not_isW hV hnL j i.val i.2.1 i.2.2
  have hpos : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      posTL Fr (gT Fr Dt.nL i.val) = i.val := by
    intro i
    obtain ⟨s, hs, hs'⟩ := hgood i
    rw [hs, hs']
  have hinj2 : Function.Injective
      (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => gT Fr Dt.nL i.val) := by
    intro a b h
    apply Subtype.ext
    rw [← hpos a, ← hpos b]
    exact congrArg (posTL Fr) h
  have hvec : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      Dt.trueLet.vec (gT Fr Dt.nL i.val) = (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val).vec i := by
    intro i
    obtain ⟨s, hs, hs'⟩ := hgood i
    rw [hs, trueLet_vec Dt hV hsgn, hs']
  have hmem : ∀ i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x},
      gT Fr Dt.nL i.val ∈ S ↔ i ∈ {i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} | i.val ∈ Sz} := by
    intro i
    obtain ⟨s, hs, hs'⟩ := hgood i
    rw [hs, hS s, hs']
    rfl
  have hR : Rn Fr Dt.nL (rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (v.1.val, v.2)) A') =
      rename (fun v : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} × Fin K => (gT Fr Dt.nL v.1.val, v.2))
        (MvPolynomial.map (algebraMap O (KK O)) A') := by
    unfold Rn
    rw [map_rename, rename_rename]
    rfl
  apply le_of_eq
  rw [hR]
  unfold lam1S
  rw [symbolGeneratorData.md_sDegs_rename (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => gT Fr Dt.nL i.val) hinj2
      (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val) Dt.trueLet
      {i | i.val ∈ Sz} S hvec hmem,
    Joints.StandardMonomialSpace.sDegs_map _ hinj,
    symbolGeneratorData.md_sDegs_rename (fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => i.val) Subtype.val_injective
      (Letters.mk fun i : {x : ℤ // x ∈ Fr.letters (segZ j) ∧ ¬ Fr.IsW (segZ j) x} => LZ.vec i.val) LZ
      {i | i.val ∈ Sz} Sz (fun _ => rfl) (fun _ => Iff.rfl)]

theorem lam_prod_le (hV : Fr.Valid L₁ N₁) (hJ : J = Fr.J) (hnL : ∀ j, Dt.nL j = (Fr.LLset (segZ j)).card)
    (hsgn : ∀ j l, Dt.sgn j l = decide (Even (llPos Fr (segZ j) l.val)))
    (G : ℤ → MvPolynomial (ℤ × Fin K) O)
    (hG : ∀ i : ℕ, i < Fr.J → G i ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters i ∧ ¬ Fr.IsW i v.1})
    (j : ZMod J) (S : Set (TL J Dt.nL r)) (Sz : Set ℤ) (hSj : ∀ t ∈ S, t.1 = j)
    (hS : ∀ s, (⟨j, s⟩ : TL J Dt.nL r) ∈ S ↔ posTL Fr (⟨j, s⟩ : TL J Dt.nL r) ∈ Sz) :
    lam1S Dt.trueLet S (∏ i ∈ Finset.range Fr.J, Rn Fr Dt.nL (G i)) ≤ lam1S LZ Sz (G (segZ j)) := by
  have hjlt : j.val < Fr.J := hJ ▸ ZMod.val_lt j
  have hmemr : j.val ∈ Finset.range Fr.J := Finset.mem_range.mpr hjlt
  rw [← Finset.mul_prod_erase _ _ hmemr]
  have h1 : lam1S Dt.trueLet S (Rn Fr Dt.nL (G (j.val : ℤ))) ≤ lam1S LZ Sz (G (segZ j)) :=
    lam_Rn_le Dt hV hnL hsgn j (G (j.val : ℤ)) (hG j.val hjlt) S Sz hS
  have h2 : lam1S Dt.trueLet S (∏ i ∈ (Finset.range Fr.J).erase j.val, Rn Fr Dt.nL (G (i : ℤ))) ≤ 0 := by
    apply lowest_weight_nonpos_off_set
    intro v hv hvS
    obtain ⟨i, hi, hvi⟩ := Finset.mem_biUnion.mp (vars_prod _ hv)
    obtain ⟨hne, hir⟩ := Finset.mem_erase.mp hi
    have hiJ : i < J := hJ ▸ Finset.mem_range.mp hir
    have hGi : G (i : ℤ) ∈ supported O {v : ℤ × Fin K | v.1 ∈ Fr.letters (segZ ((i : ℕ) : ZMod J)) ∧
        ¬ Fr.IsW (segZ ((i : ℕ) : ZMod J)) v.1} := by
      rw [segZ_natCast i hiJ]
      exact hG i (Finset.mem_range.mp hir)
    have hv1 := Rn_vars Dt hV hnL ((i : ℕ) : ZMod J) (G (i : ℤ)) hGi v hvi
    have hv2 := hSj v.1 hvS
    apply hne
    rw [← hv2, hv1, ZMod.val_natCast_of_lt hiJ]
  calc lam1S Dt.trueLet S (Rn Fr Dt.nL (G (j.val : ℤ)) * ∏ i ∈ (Finset.range Fr.J).erase j.val, Rn Fr Dt.nL (G (i : ℤ)))
      ≤ lam1S Dt.trueLet S (Rn Fr Dt.nL (G (j.val : ℤ))) + lam1S Dt.trueLet S (∏ i ∈ (Finset.range Fr.J).erase j.val, Rn Fr Dt.nL (G (i : ℤ))) :=
        GLWeightTheory.flt_lam1S_mul_le _ _ _ _
    _ ≤ lam1S LZ Sz (G (segZ j)) + 0 := add_le_add h1 h2
    _ = lam1S LZ Sz (G (segZ j)) := add_zero _

end Fac

end Formalism.MainNotions.NormalSetCounting
