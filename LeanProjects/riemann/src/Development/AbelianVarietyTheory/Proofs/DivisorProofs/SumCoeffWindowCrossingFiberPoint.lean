import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperFact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WinSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagDegreeEqFormDegree

noncomputable section

open MvPolynomial GlobalTheory.FlagPoly GlobalTheory.FlagForm GlobalTheory.FlagCurve GlobalTheory.FlagFormDeg Formalism.DegreeFormula

namespace GlobalTheory.FlagCurveCore

section General

variable {σ β : Type} [DecidableEq σ] [DecidableEq β]

def splitAt (z : σ) : MvPolynomial σ ℝ →ₐ[ℝ] Polynomial (MvPolynomial σ ℝ) :=
  aeval fun y => if y = z then Polynomial.X else Polynomial.C (X y)

theorem splitAt_self (z : σ) : splitAt z (X z) = Polynomial.X := by simp [splitAt]

theorem splitAt_ne {z y : σ} (h : y ≠ z) : splitAt z (X y) = Polynomial.C (X y) := by simp [splitAt, h]

theorem splitAt_C (z : σ) (a : ℝ) : splitAt z (C a) = Polynomial.C (C a) := by
  simp [splitAt, Polynomial.algebraMap_apply]

theorem coeff_splitAt (z : σ) (Q : MvPolynomial σ ℝ) (e : σ →₀ ℕ) (he : e z = 0) (k : ℕ) :
    coeff (e + Finsupp.single z k) Q = coeff e ((splitAt z Q).coeff k) := by
  induction Q using MvPolynomial.induction_on generalizing e k with
  | C a =>
    rw [splitAt_C, Polynomial.coeff_C]
    by_cases hk : k = 0
    · subst hk; simp
    · rw [if_neg hk, coeff_C, if_neg, coeff_zero]
      intro h
      have := DFunLike.congr_fun h z
      simp [he] at this
      exact hk this.symm
  | add p q hp hq => simp [hp e he k, hq e he k]
  | mul_X p y hp =>
    rw [map_mul]
    by_cases hy : y = z
    · subst hy
      rw [splitAt_self]
      cases k with
      | zero => simp [coeff_mul_X', he]
      | succ k =>
        rw [Polynomial.coeff_mul_X, Finsupp.single_add, ← add_assoc, coeff_mul_X, hp e he]
    · rw [splitAt_ne hy, Polynomial.coeff_mul_C, coeff_mul_X', coeff_mul_X']
      have h1 : (y ∈ (e + Finsupp.single z k).support) ↔ y ∈ e.support := by
        simp [Finsupp.single_apply, Ne.symm hy]
      by_cases h2 : y ∈ e.support
      · rw [if_pos h2, if_pos (h1.2 h2), ← hp _ (by simp [he])]
        congr 1
        ext w
        by_cases hw : w = z
        · subst hw; simp [he, Finsupp.single_apply, hy]
        · simp [Finsupp.single_apply, Ne.symm hw]
      · rw [if_neg h2, if_neg (fun h => h2 (h1.1 h))]

def coProd {E R : Type} [DecidableEq E] [CommRing R] (A : Finset E) (f : E → R) : R :=
  ∑ p ∈ A, ∏ q ∈ A.erase p, f q

theorem coProd_union {E R : Type} [DecidableEq E] [CommRing R] {A B : Finset E} (h : Disjoint A B) (f : E → R) :
    coProd (A ∪ B) f = coProd A f * ∏ q ∈ B, f q + (∏ q ∈ A, f q) * coProd B f := by
  rw [coProd, Finset.sum_union h, coProd, coProd, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (Finset.disjoint_left.1 h hp),
      Finset.prod_union (h.mono_left (Finset.erase_subset _ _))]
  · refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.erase_union_distrib, Finset.erase_eq_of_notMem (Finset.disjoint_right.1 h hp),
      Finset.prod_union (h.mono_right (Finset.erase_subset _ _))]

theorem coProd_map {E E' R : Type} [DecidableEq E] [DecidableEq E'] [CommRing R] (A : Finset E) (g : E ↪ E')
    (f : E' → R) : coProd (A.map g) f = coProd A fun a => f (g a) := by
  rw [coProd, Finset.sum_map, coProd]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Finset.map_erase, Finset.prod_map]

theorem coeff_prod_card {E R : Type} [CommRing R] [Nontrivial R] (A : Finset E) (f : E → R) :
    (∏ q ∈ A, (Polynomial.X - Polynomial.C (f q))).coeff A.card = 1 := by
  have h := (Polynomial.monic_prod_X_sub_C f A).coeff_natDegree
  rwa [Polynomial.natDegree_finset_prod_X_sub_C_eq_card] at h

theorem coeff_coProd_card {E R : Type} [DecidableEq E] [CommRing R] [Nontrivial R] (A : Finset E) (f : E → R) :
    (coProd A fun q => Polynomial.X - Polynomial.C (f q)).coeff A.card = 0 := by
  rw [coProd, Polynomial.finset_sum_coeff]
  refine Finset.sum_eq_zero fun p hp => Polynomial.coeff_eq_zero_of_natDegree_lt ?_
  rw [Polynomial.natDegree_finset_prod_X_sub_C_eq_card]
  exact Finset.card_erase_lt_of_mem hp

theorem coeff_coProd_pred {E R : Type} [DecidableEq E] [CommRing R] [Nontrivial R] (A : Finset E) (f : E → R) :
    (coProd A fun q => Polynomial.X - Polynomial.C (f q)).coeff (A.card - 1) = (A.card : R) := by
  rw [coProd, Polynomial.finset_sum_coeff, Finset.sum_congr rfl (g := fun _ => (1 : R))]
  · simp
  · intro p hp
    rw [← Finset.card_erase_of_mem hp, coeff_prod_card]

def chPairs (blk : σ → β) (pos : σ → ℕ) (s : Finset σ) : Finset (σ × σ) :=
  (s ×ˢ s).filter fun p => blk p.1 = blk p.2 ∧ pos p.1 < pos p.2

def dif (p : σ × σ) : MvPolynomial σ ℝ := X p.1 - X p.2

def chExp (blk : σ → β) (pos : σ → ℕ) (s : Finset σ) : σ →₀ ℕ := ∑ p ∈ chPairs blk pos s, Finsupp.single p.1 1

theorem chain_coeff (blk : σ → β) (pos : σ → ℕ) (hinj : ∀ a b, blk a = blk b → pos a = pos b → a = b)
    (s : Finset σ) :
    coeff (chExp blk pos s) (∏ p ∈ chPairs blk pos s, dif p) = 1 ∧
      ∀ c : β → ℝ, coeff (chExp blk pos s) ((∑ x ∈ s, C (c (blk x)) * X x) * coProd (chPairs blk pos s) dif) =
        ∑ x ∈ s, c (blk x) - ∑ b ∈ s.image blk, c b := by
  induction s using Finset.induction_on_min_value pos with
  | empty => simp [chExp, chPairs]
  | insert z s hz hmin ih =>
    obtain ⟨ih1, ih2⟩ := ih
    set P := s.filter fun b => blk b = blk z with hP
    let g : σ ↪ σ × σ := ⟨fun b => (z, b), fun a b h => (Prod.mk.inj h).2⟩
    have hg : ∀ b, g b = (z, b) := fun _ => rfl
    have hW : chPairs blk pos (insert z s) = chPairs blk pos s ∪ P.map g := by
      ext ⟨a, b⟩
      simp only [chPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_union, Finset.mem_map, hP,
        hg, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨rfl | ha, rfl | hb⟩, h1, h2⟩
        · omega
        · exact Or.inr ⟨b, ⟨hb, h1.symm⟩, rfl, rfl⟩
        · have := hmin a ha; omega
        · exact Or.inl ⟨⟨ha, hb⟩, h1, h2⟩
      · rintro (⟨⟨ha, hb⟩, h1, h2⟩ | ⟨x, ⟨hx, h1⟩, rfl, rfl⟩)
        · exact ⟨⟨Or.inr ha, Or.inr hb⟩, h1, h2⟩
        · refine ⟨⟨Or.inl rfl, Or.inr hx⟩, h1.symm, lt_of_le_of_ne (hmin x hx) fun h => hz ?_⟩
          rw [hinj _ _ h1.symm h]; exact hx
    have hmem : ∀ p ∈ chPairs blk pos s, p.1 ≠ z ∧ p.2 ≠ z := by
      intro p hp
      simp only [chPairs, Finset.mem_filter, Finset.mem_product] at hp
      exact ⟨fun h => hz (h ▸ hp.1.1), fun h => hz (h ▸ hp.1.2)⟩
    have hdisj : Disjoint (chPairs blk pos s) (P.map g) := by
      rw [Finset.disjoint_left]
      intro p hp hq
      obtain ⟨x, -, rfl⟩ := Finset.mem_map.1 hq
      exact (hmem _ hp).1 rfl
    have hE : chExp blk pos (insert z s) = chExp blk pos s + Finsupp.single z P.card := by
      rw [chExp, hW, Finset.sum_union hdisj, Finset.sum_map, chExp]
      simp [hg]
    have hE0 : chExp blk pos s z = 0 := by
      rw [chExp, Finsupp.finset_sum_apply]
      exact Finset.sum_eq_zero fun p hp => by simp [Finsupp.single_apply, (hmem p hp).1]
    have hdif : ∀ p ∈ chPairs blk pos s, splitAt z (dif p) = Polynomial.C (dif p) := by
      intro p hp
      rw [dif, map_sub, map_sub, splitAt_ne (hmem p hp).1, splitAt_ne (hmem p hp).2]
    have hD : splitAt z (∏ p ∈ chPairs blk pos s, dif p) = Polynomial.C (∏ p ∈ chPairs blk pos s, dif p) := by
      rw [map_prod, map_prod]
      exact Finset.prod_congr rfl hdif
    have hG : splitAt z (coProd (chPairs blk pos s) dif) = Polynomial.C (coProd (chPairs blk pos s) dif) := by
      simp only [coProd, map_prod, map_sum]
      exact Finset.sum_congr rfl fun p _ => Finset.prod_congr rfl fun q hq => hdif q (Finset.mem_of_mem_erase hq)
    have hdif' : ∀ b ∈ P, splitAt z (dif (g b)) = Polynomial.X - Polynomial.C (X b) := by
      intro b hb
      have : b ≠ z := fun h => hz (h ▸ (Finset.mem_filter.1 hb).1)
      change splitAt z (X z - X b) = _
      rw [map_sub, splitAt_self, splitAt_ne this]
    have hM : splitAt z (∏ p ∈ P.map g, dif p) = ∏ b ∈ P, (Polynomial.X - Polynomial.C (X b)) := by
      rw [Finset.prod_map, map_prod]
      exact Finset.prod_congr rfl hdif'
    have hGP : splitAt z (coProd (P.map g) dif) = coProd P fun b => (Polynomial.X - Polynomial.C (X b)) := by
      rw [coProd_map]
      simp only [coProd, map_prod, map_sum]
      exact Finset.sum_congr rfl fun p _ => Finset.prod_congr rfl fun q hq => hdif' q (Finset.mem_of_mem_erase hq)
    constructor
    · rw [hE, coeff_splitAt _ _ _ hE0, hW, Finset.prod_union hdisj, map_mul, hD, hM, Polynomial.coeff_C_mul,
        coeff_prod_card, mul_one, ih1]
    · intro c
      have hL : splitAt z (∑ x ∈ s, C (c (blk x)) * X x) = Polynomial.C (∑ x ∈ s, C (c (blk x)) * X x) := by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun x hx => ?_
        have : x ≠ z := fun h => hz (h ▸ hx)
        rw [map_mul, map_mul, splitAt_C, splitAt_ne this]
      rw [hE, coeff_splitAt _ _ _ hE0, hW, coProd_union hdisj, Finset.sum_insert hz, Finset.sum_insert hz, map_mul,
        map_add, map_add, map_mul, map_mul, map_mul, hD, hM, hG, hGP, hL, splitAt_C, splitAt_self, add_mul,
        Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_add, Polynomial.coeff_C_mul,
        Polynomial.coeff_C_mul, coeff_prod_card, coeff_coProd_card, mul_one, mul_zero, add_zero, coeff_add, ih2,
        mul_assoc, Polynomial.coeff_C_mul, coeff_C_mul, Finset.image_insert]
      rcases P.eq_empty_or_nonempty with h0 | h0
      · have hn : blk z ∉ s.image blk := by
          intro h
          obtain ⟨x, hx, hx'⟩ := Finset.mem_image.1 h
          have : x ∈ P := Finset.mem_filter.2 ⟨hx, hx'⟩
          simp [h0] at this
        rw [Finset.sum_insert hn, h0]
        simp
      · have hn : blk z ∈ s.image blk := by
          obtain ⟨x, hx⟩ := h0
          exact Finset.mem_image.2 ⟨x, (Finset.mem_filter.1 hx).1, (Finset.mem_filter.1 hx).2⟩
        have hpos : 0 < P.card := h0.card_pos
        have h3 := ih2 fun b => if b = blk z then 1 else 0
        have h4 : (∑ x ∈ s, C (if blk x = blk z then (1 : ℝ) else 0) * X x : MvPolynomial σ ℝ) = ∑ x ∈ P, X x := by
          rw [hP, Finset.sum_filter]
          exact Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
        rw [h4, Finset.sum_boole, Finset.sum_ite_eq', if_pos hn, ← hP] at h3
        have h5 : ∀ F : Polynomial (MvPolynomial σ ℝ), (Polynomial.X * F).coeff P.card = F.coeff (P.card - 1) := by
          intro F
          rw [← Polynomial.coeff_X_mul F, Nat.sub_add_cancel hpos]
        rw [Finset.insert_eq_of_mem hn, h5,
          Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C_mul,
          Polynomial.prod_X_sub_C_coeff_card_pred _ _ hpos, coeff_coProd_pred, coeff_add, mul_neg, coeff_neg,
          mul_comm (coProd _ _), h3, mul_comm _ (P.card : MvPolynomial σ ℝ), ← map_natCast C, coeff_C_mul, ih1]
        ring

end General

theorem apolar_monomial_left {V : Type} [Fintype V] [DecidableEq V] (e : V →₀ ℕ) (k : ℝ) (Q : MvPolynomial V ℝ) :
    apolar (monomial e k) Q = (k * ∏ x, ((e x).factorial : ℝ)) * coeff e Q := by
  induction Q using MvPolynomial.induction_on' with
  | monomial u a =>
    rw [apolar_monomial, coeff_monomial, coeff_monomial]
    by_cases h : e = u
    · subst h
      simp only [if_true]
      ring
    · simp [h, Ne.symm h]
  | add p q hp hq => simp [hp, hq, mul_add]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ℕ}

def blkOf (j : ℕ) (x : ι × Fin N) : ι × Bool := (x.1, decide ((x.2 : ℕ) < j))

def ends : ι × Fin N × Fin N ↪ (ι × Fin N) × (ι × Fin N) :=
  ⟨fun e => ((e.1, e.2.1), (e.1, e.2.2)), fun a b h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.1 (Prod.ext h.1.2 h.2.2)⟩

omit [Fintype ι] [DecidableEq ι] in
theorem ends_apply (e : ι × Fin N × Fin N) : ends e = ((e.1, e.2.1), (e.1, e.2.2)) := rfl

theorem chPairs_eq (j : ℕ) :
    chPairs (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ)) Finset.univ = (winSet ι N j).map ends := by
  ext ⟨⟨s, a⟩, ⟨t, b⟩⟩
  simp only [chPairs, blkOf, winSet, ends_apply, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_map, Prod.mk.injEq, decide_eq_decide, Fin.lt_def]
  constructor
  · rintro ⟨⟨rfl, h1⟩, h2⟩
    exact ⟨(s, a, b), ⟨h2, by simp only; omega⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
  · rintro ⟨⟨u, a', b'⟩, ⟨h1, h2⟩, ⟨rfl, rfl⟩, rfl, rfl⟩
    simp only at h1 h2 ⊢
    exact ⟨⟨trivial, by omega⟩, h1⟩

theorem sum_fin_ite (p : ℕ → Prop) [DecidablePred p] (l u : ℕ) (h : ∀ b, (b < N ∧ p b) ↔ (l ≤ b ∧ b < u)) :
    ∑ b : Fin N, (if p b then 1 else 0 : ℕ) = u - l := by
  rw [Fin.sum_univ_eq_sum_range (fun b => if p b then 1 else 0), ← Finset.card_filter, ← Nat.card_Ico]
  congr 1
  ext b
  simp [h]

theorem chExp_eq {j : ℕ} (hj : j < N) (x : ι × Fin N) :
    chExp (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ)) Finset.univ x =
      if (x.2 : ℕ) < j then j - 1 - (x.2 : ℕ) else N - 1 - (x.2 : ℕ) := by
  obtain ⟨s, i⟩ := x
  have h : chExp (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ)) Finset.univ (s, i) =
      ∑ b : Fin N, (if ((i : ℕ) < j ↔ (b : ℕ) < j) ∧ (i : ℕ) < b then 1 else 0 : ℕ) := by
    rw [chExp, Finsupp.finset_sum_apply, chPairs, Finset.sum_filter, Finset.univ_product_univ, Fintype.sum_prod_type,
      Finset.sum_eq_single (s, i), Fintype.sum_prod_type, Finset.sum_eq_single s]
    · simp [blkOf]
    · intro t _ ht
      simp [blkOf, Ne.symm ht]
    · simp
    · intro y _ hy
      simp [Finsupp.single_apply, hy]
    · simp
  rw [h]
  have := i.2
  dsimp only
  split_ifs with hi
  · rw [sum_fin_ite (fun b => ((i : ℕ) < j ↔ b < j) ∧ (i : ℕ) < b) (i + 1) j (fun b => by omega)]
    omega
  · rw [sum_fin_ite (fun b => ((i : ℕ) < j ↔ b < j) ∧ (i : ℕ) < b) (i + 1) N (fun b => by omega)]
    omega

theorem exists_fibPt {j : ℕ} (hj : j < N) :
    ∃ k : ℝ, fibPt ι N j = monomial (chExp (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ)) Finset.univ) k := by
  refine ⟨∏ x : ι × Fin N, (-1) ^ (chExp (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ)) Finset.univ x), ?_⟩
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), map_prod, ← Finset.prod_mul_distrib, fibPt]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [← chExp_eq hj, neg_pow, map_pow, map_neg, map_one]

theorem coeff_toForm (P : Pol ι N) (S : Finset (ι × Fin N × Fin N)) (hS : ∀ e ∈ S, e.2.1 < e.2.2) :
    coeff (mono S) (toForm P : FormPol ι N) = (-1) ^ S.card * apolar P (∏ e ∈ S, dif (ends e)) := by
  rw [mono, toForm, coeff_aeval_lin rootForm inc pderiv_rootForm constantCoeff_rootForm, ← smul_eq_mul, ← map_smul]
  congr 1
  rw [← C_mul', map_pow, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e he => ?_
  simp [inc, hS e he, sub_mul, Finset.sum_sub_distrib, apply_ite (C : ℝ → Pol ι N), ite_mul, dif, ends_apply]

def wt (N j : ℕ) (b : ι × Bool) : ℝ := if b.2 then (N : ℝ) - j else -j

theorem sum_low {j : ℕ} (hj : j < N) : ∑ b : Fin N, (if (b : ℕ) < j then 1 else 0 : ℝ) = j := by
  have := sum_fin_ite (N := N) (fun b => b < j) 0 j (fun b => by omega)
  exact_mod_cast this

theorem sum_high {j : ℕ} (hj : j < N) : ∑ b : Fin N, (if j ≤ (b : ℕ) then 1 else 0 : ℝ) = N - j := by
  have := sum_fin_ite (N := N) (fun b => j ≤ b) j N (fun b => by omega)
  rw [← Nat.cast_sub hj.le, ← this]
  push_cast
  rfl

theorem sum_cr {M : Type} [AddCommGroup M] [Module ℝ M] {j : ℕ} (hj : j < N) (v : ι × Fin N → M) :
    ∑ q ∈ crSet ι N j, (v (q.1, q.2.1) - v (q.1, q.2.2)) = ∑ x, wt N j (blkOf j x) • v x := by
  rw [crSet, Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Fintype.sum_prod_type]
  have h1 : ∀ a b : Fin N, (if a < b ∧ (a : ℕ) < j ∧ j ≤ (b : ℕ) then v (τ, a) - v (τ, b) else 0) =
      (if j ≤ (b : ℕ) then 1 else 0 : ℝ) • (if (a : ℕ) < j then v (τ, a) else 0) -
        (if (a : ℕ) < j then 1 else 0 : ℝ) • (if j ≤ (b : ℕ) then v (τ, b) else 0) := by
    intro a b
    by_cases ha : (a : ℕ) < j <;> by_cases hb : j ≤ (b : ℕ) <;> simp [ha, hb]
    intro h
    rw [Fin.le_def] at h
    omega
  simp only [h1, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun a b : Fin N =>
    (if (a : ℕ) < j then 1 else 0 : ℝ) • (if j ≤ (b : ℕ) then v (τ, b) else 0))]
  simp only [← Finset.sum_smul, sum_low hj, sum_high hj]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : (a : ℕ) < j
  · simp [wt, blkOf, ha, not_le.2 ha]
  · simp [wt, blkOf, ha, not_lt.1 ha]

theorem sum_coeff_fibPt (ι : Type) [Fintype ι] [DecidableEq ι] (N j : ℕ) (h1 : 1 ≤ j) (hj : j < N) :
    ∑ p ∈ winSet ι N j, ∑ q ∈ crSet ι N j,
        coeff (mono (insert q ((winSet ι N j).erase p))) (toForm (fibPt ι N j) : FormPol ι N) =
      (Fintype.card ι : ℝ) * (2 * (j : ℝ) - N) * coeff (mono (winSet ι N j)) (toForm (fibPt ι N j) : FormPol ι N) := by
  obtain ⟨k, hk⟩ := exists_fibPt (ι := ι) hj
  obtain ⟨hD, hG⟩ := chain_coeff (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ))
    (fun a b h h' => Prod.ext (Prod.mk.inj h).1 (Fin.ext h')) Finset.univ
  have hG := hG (wt N j)
  rw [chPairs_eq] at hD hG
  rw [Finset.prod_map] at hD
  have hw : ∀ e ∈ winSet ι N j, e.2.1 < e.2.2 := fun e he => (Finset.mem_filter.1 he).2.1
  have himg : (Finset.univ : Finset (ι × Fin N)).image (blkOf j) = Finset.univ := by
    refine Finset.eq_univ_of_forall fun ⟨τ, b⟩ => Finset.mem_image.2 ?_
    cases b
    · exact ⟨(τ, ⟨j, hj⟩), Finset.mem_univ _, by simp [blkOf]⟩
    · exact ⟨(τ, ⟨0, by omega⟩), Finset.mem_univ _, by simp [blkOf]; omega⟩
  have h0 : ∑ x : ι × Fin N, wt N j (blkOf j x) = 0 := by
    simpa using (sum_cr (ι := ι) hj fun _ => (1 : ℝ)).symm
  have h2 : ∑ b : ι × Bool, wt N j b = (Fintype.card ι : ℝ) * (N - 2 * j) := by
    rw [Fintype.sum_prod_type]
    simp [wt]
    ring
  simp only [C_mul'] at hG
  rw [himg, h0, h2, coProd_map, ← sum_cr hj, coProd, Finset.mul_sum, coeff_sum] at hG
  rw [coeff_toForm _ _ hw, hk, apolar_monomial_left, hD]
  rw [Finset.sum_congr rfl (g := fun p => (-1) ^ (winSet ι N j).card * ((k * ∏ x,
    ((chExp (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ)) Finset.univ x).factorial : ℝ)) *
      coeff (chExp (blkOf j) (fun x : ι × Fin N => (x.2 : ℕ)) Finset.univ)
        ((∑ q ∈ crSet ι N j, (X (q.1, q.2.1) - X (q.1, q.2.2) : Pol ι N)) *
          ∏ q ∈ (winSet ι N j).erase p, dif (ends q)))), ← Finset.mul_sum, ← Finset.mul_sum, hG]
  · ring
  · intro p hp
    rw [Finset.sum_mul, coeff_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hq' := (Finset.mem_filter.1 hq).2
    have hn : q ∉ (winSet ι N j).erase p := fun h => by
      have := (Finset.mem_filter.1 (Finset.mem_of_mem_erase h)).2
      omega
    rw [coeff_toForm, apolar_monomial_left, Finset.card_insert_of_notMem hn, Finset.card_erase_add_one hp,
      Finset.prod_insert hn]
    · rfl
    · intro e he
      rcases Finset.mem_insert.1 he with rfl | he
      · exact hq'.1
      · exact hw e (Finset.mem_of_mem_erase he)

end GlobalTheory.FlagCurveCore
