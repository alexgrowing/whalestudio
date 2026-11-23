import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial

noncomputable section

namespace Formalism.CohomologicalDescent.LR

open Formalism.GradedWeylDivisibility

section

variable {R : Type*} [CommRing R] {r n : ℕ}

def lrfc_iota : MvPolynomial (Fin r × Fin n) R →+*
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  MvPolynomial.map (C : R →+* MvPolynomial (Fin r × Fin n) R)

def lrfc_coeffT (d : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    MvPolynomial (Fin r × Fin n) R :=
  ∑ m ∈ G.support, monomial m (coeff d (coeff m G))

theorem lrfc_coeff_coeffT (d m : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    coeff m (lrfc_coeffT d G) = coeff d (coeff m G) := by
  classical
  unfold lrfc_coeffT
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, coeff_zero]

theorem lrfc_coeffT_add (d : Fin r × Fin n →₀ ℕ)
    (G H : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_coeffT d (G + H) = lrfc_coeffT d G + lrfc_coeffT d H := by
  ext m
  simp [lrfc_coeff_coeffT]

theorem lrfc_coeffT_zero (d : Fin r × Fin n →₀ ℕ) :
    lrfc_coeffT (R := R) d 0 = 0 := by
  ext m
  simp [lrfc_coeff_coeffT]

theorem lrfc_coeffT_sum {ι : Type*} (s : Finset ι) (d : Fin r × Fin n →₀ ℕ)
    (G : ι → MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_coeffT d (∑ i ∈ s, G i) = ∑ i ∈ s, lrfc_coeffT d (G i) := by
  ext m
  simp [lrfc_coeff_coeffT, coeff_sum]

theorem lrfc_coeffT_monomial (d u : Fin r × Fin n →₀ ℕ) (c : MvPolynomial (Fin r × Fin n) R) :
    lrfc_coeffT d (monomial u c) = monomial u (coeff d c) := by
  classical
  ext m
  rw [lrfc_coeff_coeffT, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem lrfc_coeffT_C_monomial_mul (d s : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_coeffT d (C (monomial s 1) * G) = if s ≤ d then lrfc_coeffT (d - s) G else 0 := by
  classical
  ext m
  rw [lrfc_coeff_coeffT, coeff_C_mul, coeff_monomial_mul', one_mul]
  split_ifs
  · rw [lrfc_coeff_coeffT]
  · simp

theorem lrfc_coeffT_iota (d : Fin r × Fin n →₀ ℕ) (F : MvPolynomial (Fin r × Fin n) R) :
    lrfc_coeffT d (lrfc_iota F) = if d = 0 then F else 0 := by
  classical
  ext m
  rw [lrfc_coeff_coeffT, lrfc_iota, coeff_map, coeff_C]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

end

section

variable {R : Type*} [CommRing R] {r n : ℕ}

def lrfc_tau (l : Fin r × Fin r × (Fin r × Fin n)) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => X v + if v.1 = l.2.1 then C (X l.2.2) * X (l.1, v.2) else 0

theorem lrfc_tau_iota (l : Fin r × Fin r × (Fin r × Fin n)) (F : MvPolynomial (Fin r × Fin n) R) :
    lrfc_tau l (lrfc_iota F) =
      Polynomial.eval₂ lrfc_iota (C (X l.2.2)) (rowGen R l.1 l.2.1 F) := by
  have h : ((lrfc_tau (R := R) l).toRingHom.comp lrfc_iota) =
      (Polynomial.eval₂RingHom lrfc_iota (C (X l.2.2))).comp (rowGen R l.1 l.2.1).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [lrfc_tau, lrfc_iota, rowGen]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      simp only [lrfc_tau, lrfc_iota, rowGen, aeval_X, map_X, Polynomial.coe_eval₂RingHom]
      split_ifs
      · simp
        exact mul_comm _ _
      · simp
  exact congrArg (fun φ => φ F) h

def lrfc_Phi (L : List (Fin r × Fin r × (Fin r × Fin n))) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  L.foldr (fun l φ => (lrfc_tau l).comp φ) (AlgHom.id _ _)

theorem lrfc_Phi_nil (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_Phi [] G = G := rfl

theorem lrfc_Phi_cons (l : Fin r × Fin r × (Fin r × Fin n)) (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_Phi (l :: w) G = lrfc_tau l (lrfc_Phi w G) := rfl

theorem lrfc_Phi_append_single (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (l : Fin r × Fin r × (Fin r × Fin n))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    lrfc_Phi (w ++ [l]) G = lrfc_Phi w (lrfc_tau l G) := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [List.cons_append, lrfc_Phi_cons, ih, lrfc_Phi_cons]

theorem lrfc_applyWord_append_single (w : List (Fin r × Fin r × ℕ)) (x : Fin r × Fin r × ℕ)
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (w ++ [x]) F = applyWord R w (rowDiv R x.1 x.2.1 x.2.2 F) := by
  simp [applyWord, List.foldr_append]

theorem lrfc_applyWord_zero (w : List (Fin r × Fin r × ℕ)) :
    applyWord R w (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih]
    simp [rowDiv]

theorem lrfc_coeffT_Phi (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hL : (L.map (·.2.2)).Nodup) (F : MvPolynomial (Fin r × Fin n) R) (d : Fin r × Fin n →₀ ℕ) :
    lrfc_coeffT d (lrfc_Phi L (lrfc_iota F)) =
      if (∀ u, u ∉ L.map (·.2.2) → d u = 0) then
        applyWord R (L.map fun l => (l.1, l.2.1, d l.2.2)) F else 0 := by
  classical
  induction L using List.reverseRecOn generalizing F d with
  | nil =>
    rw [lrfc_Phi_nil, lrfc_coeffT_iota]
    have : (∀ u, u ∉ ([] : List (Fin r × Fin r × (Fin r × Fin n))).map (·.2.2) → d u = 0) ↔ d = 0 := by
      simp [Finsupp.ext_iff]
    simp only [this]
    rfl
  | append_singleton w l ih =>
    obtain ⟨s, a, v⟩ := l
    have hL' : (w.map (·.2.2) ++ [v]).Nodup := by simpa using hL
    have hw : (w.map (·.2.2)).Nodup := hL'.sublist (List.sublist_append_left _ _)
    have hv : v ∉ w.map (·.2.2) := by
      rw [List.nodup_append] at hL'
      intro h
      exact hL'.2.2 v h v (by simp) rfl
    rw [lrfc_Phi_append_single, lrfc_tau_iota, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      map_sum, lrfc_coeffT_sum]
    have key : ∀ (j : ℕ) (c : MvPolynomial (Fin r × Fin n) R),
        lrfc_coeffT d (lrfc_Phi w (lrfc_iota c * C (X (s, a, v).2.2) ^ j)) =
          if j ≤ d v then lrfc_coeffT (d - Finsupp.single v j) (lrfc_Phi w (lrfc_iota c)) else 0 := by
      intro j c
      have e0 : (C (X (s, a, v).2.2) : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) ^ j =
          C (X v ^ j) := (map_pow C (X v) j).symm
      rw [e0, map_mul]
      have hC : lrfc_Phi w (C (X v ^ j)) = C (X v ^ j : MvPolynomial (Fin r × Fin n) R) :=
        (lrfc_Phi w).commutes (X v ^ j)
      rw [hC, mul_comm, X_pow_eq_monomial, lrfc_coeffT_C_monomial_mul]
      simp only [Finsupp.single_le_iff]
    simp only [key, ih hw]
    rw [Finset.sum_eq_single (d v)]
    · simp only [le_refl, if_true]
      have hfill : w.map (fun l => (l.1, l.2.1, (d - Finsupp.single v (d v)) l.2.2)) =
          w.map (fun l => (l.1, l.2.1, d l.2.2)) := by
        apply List.map_congr_left
        intro l hl
        have hne : l.2.2 ≠ v := by
          intro h; exact hv (List.mem_map.mpr ⟨l, hl, h⟩)
        simp [Finsupp.single_apply, Ne.symm hne]
      have hcond : (∀ u, u ∉ w.map (·.2.2) → (d - Finsupp.single v (d v)) u = 0) ↔
          (∀ u, u ∉ (w ++ [(s, a, v)]).map (·.2.2) → d u = 0) := by
        constructor
        · intro h u hu
          simp only [List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton,
            not_or] at hu
          have := h u hu.1
          simpa [Finsupp.single_apply, Ne.symm hu.2] using this
        · intro h u hu
          by_cases huv : u = v
          · subst huv; simp
          · have := h u (by simp [hu, huv])
            simp [this]
      rw [hfill]
      simp only [hcond]
      split_ifs
      · rw [List.map_append, List.map_cons, List.map_nil, lrfc_applyWord_append_single]
        rfl
      · rfl
    · intro j _ hj
      split_ifs with h1 h2
      · exfalso
        have := h2 v hv
        simp at this
        omega
      · rfl
      · rfl
    · intro hnot
      rw [Polynomial.notMem_support_iff.mp hnot]
      simp [lrfc_applyWord_zero]

end

section

variable {R : Type*} [CommRing R] {r n : ℕ}

def lrf_L (r n : ℕ) : List (Fin r × Fin r × (Fin r × Fin n)) :=
  (List.finRange n).reverse.flatMap fun s =>
    (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some ((⟨s.val, h.2⟩ : Fin r), a, (a, s)) else none

theorem lrf_mem_col (s : Fin n) (l : Fin r × Fin r × (Fin r × Fin n)) :
    (l ∈ (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some ((⟨s.val, h.2⟩ : Fin r), a, (a, s)) else none) ↔
      l.1.val = s.val ∧ s.val < l.2.1.val ∧ l.2.2 = (l.2.1, s) := by
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨a, -, ha⟩
    split_ifs at ha with h
    rw [Option.some.injEq] at ha
    subst ha
    exact ⟨rfl, h.1, rfl⟩
  · obtain ⟨x, a, v⟩ := l
    rintro ⟨h1, h2, h3⟩
    simp only at h1 h2 h3
    refine ⟨a, List.mem_finRange a, ?_⟩
    have hr : s.val < r := lt_trans h2 a.isLt
    rw [dif_pos ⟨h2, hr⟩, h3]
    congr 2
    exact Fin.ext h1.symm

theorem lrf_mem_L (l : Fin r × Fin r × (Fin r × Fin n)) :
    l ∈ lrf_L r n ↔ l.1.val = l.2.2.2.val ∧ l.2.2.2.val < l.2.1.val ∧ l.2.2.1 = l.2.1 := by
  unfold lrf_L
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨s, -, hs⟩
    rw [lrf_mem_col] at hs
    obtain ⟨h1, h2, h3⟩ := hs
    rw [h3]
    exact ⟨h1, h2, rfl⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨l.2.2.2, by simp, ?_⟩
    rw [lrf_mem_col]
    exact ⟨h1, h2, Prod.ext h3 rfl⟩

theorem lrf_mem_vars (v : Fin r × Fin n) :
    v ∈ (lrf_L r n).map (·.2.2) ↔ v.2.val < v.1.val := by
  rw [List.mem_map]
  constructor
  · rintro ⟨l, hl, rfl⟩
    rw [lrf_mem_L] at hl
    rw [hl.2.2]
    exact hl.2.1
  · intro h
    refine ⟨(⟨v.2.val, lt_trans h v.1.isLt⟩, v.1, v), ?_, rfl⟩
    rw [lrf_mem_L]
    exact ⟨rfl, h, rfl⟩

theorem lrf_pairwise :
    (lrf_L r n).Pairwise fun l l' => l.2.2 ≠ l'.2.2 ∧ l.2.1 ≠ l'.1 := by
  unfold lrf_L
  rw [List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_filterMap]
    refine (List.sortedLT_finRange r).pairwise.imp ?_
    intro a a' haa b hb b' hb'
    split_ifs at hb with h
    split_ifs at hb' with h'
    rw [Option.some.injEq] at hb hb'
    subst hb
    subst hb'
    refine ⟨fun e => ?_, fun e => ?_⟩
    · exact (ne_of_lt haa) (congrArg Prod.fst e)
    · have := congrArg Fin.val e
      simp only at this
      omega
  · rw [List.pairwise_reverse]
    refine (List.sortedLT_finRange n).pairwise.imp ?_
    intro s s' hss x hx y hy
    rw [lrf_mem_col] at hx hy
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rw [hx.2.2, hy.2.2] at e
      exact (ne_of_gt hss) (congrArg Prod.snd e)
    · have := congrArg Fin.val e
      have h3 : s.val < s'.val := hss
      omega

theorem lrf_nodup : ((lrf_L r n).map (·.2.2)).Nodup := by
  rw [List.Nodup, List.pairwise_map]
  exact (lrf_pairwise (r := r) (n := n)).imp fun h => h.1

theorem lrf_wordOf (e d : Fin r × Fin n →₀ ℕ) (h : ∀ (a : Fin r) (s : Fin n), s.val < a.val → d (a, s) = e (a, s)) :
    (lrf_L r n).map (fun l => (l.1, l.2.1, d l.2.2)) = wordOf e := by
  unfold lrf_L wordOf
  rw [List.map_flatMap]
  congr 1
  funext s
  rw [List.map_filterMap]
  congr 1
  funext a
  split_ifs with h'
  · simp [h a s h'.1]
  · rfl

def lrf_idS (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R :=
  fun u => C (idFrame R r n u)

def lrf_ell (R : Type*) [CommRing R] (r n : ℕ) : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R :=
  fun v => C (idFrame R r n v) + if v.2.val < v.1.val then X v else 0

theorem lrf_pt (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hP : L.Pairwise fun l l' => l.2.2 ≠ l'.2.2 ∧ l.2.1 ≠ l'.1)
    (hM : ∀ l ∈ L, l.1.val = l.2.2.2.val ∧ l.2.2.1 = l.2.1) (v : Fin r × Fin n) :
    eval (lrf_idS R r n) (lrfc_Phi L (X v)) =
      C (idFrame R r n v) + if v ∈ L.map (·.2.2) then X v else 0 := by
  classical
  induction L using List.reverseRecOn generalizing v with
  | nil => simp [lrfc_Phi_nil, lrf_idS]
  | append_singleton w l ih =>
    rw [List.pairwise_append] at hP
    obtain ⟨hPw, -, hPl⟩ := hP
    have hMw : ∀ l ∈ w, l.1.val = l.2.2.2.val ∧ l.2.2.1 = l.2.1 := fun x hx => hM x (by simp [hx])
    have hMl := hM l (by simp)
    have ihw := ih hPw hMw
    have hlw : l.2.2 ∉ w.map (·.2.2) := by
      intro h
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
      exact (hPl x hx l (by simp)).1 hxe
    have hmem : ∀ u : Fin r × Fin n, u ∈ (w ++ [l]).map (·.2.2) ↔ (u ∈ w.map (·.2.2) ∨ u = l.2.2) := by
      intro u
      simp
    rw [lrfc_Phi_append_single, lrfc_tau, aeval_X]
    by_cases hv : v.1 = l.2.1
    · rw [if_pos hv, map_add, map_mul, map_add, map_mul, ihw v, ihw (l.1, v.2)]
      have hC : lrfc_Phi w (C (X l.2.2)) = C (X l.2.2 : MvPolynomial (Fin r × Fin n) R) :=
        (lrfc_Phi w).commutes (X l.2.2)
      rw [hC, eval_C]
      have hs : (l.1, v.2) ∉ w.map (·.2.2) := by
        intro h
        obtain ⟨x, hx, hxe⟩ := List.mem_map.mp h
        apply (hPl x hx l (by simp)).2
        rw [← (hMw x hx).2, hxe]
      rw [if_neg hs, add_zero]
      by_cases hc : l.1.val = v.2.val
      · have hvl : v = l.2.2 := by
          refine Prod.ext (by rw [hv, hMl.2]) (Fin.ext ?_)
          rw [← hc, hMl.1]
        have h1 : idFrame R r n (l.1, v.2) = 1 := by simp [idFrame, hc]
        rw [h1, if_neg (by rw [hvl]; exact hlw), if_pos ((hmem v).2 (Or.inr hvl)), ← hvl]
        simp
      · have hvl : v ≠ l.2.2 := by
          intro h
          apply hc
          rw [h, hMl.1]
        have h1 : idFrame R r n (l.1, v.2) = 0 := by simp [idFrame, hc]
        rw [h1]
        have e : (v ∈ (w ++ [l]).map (·.2.2)) ↔ v ∈ w.map (·.2.2) := by
          rw [hmem]
          exact or_iff_left hvl
        simp only [e]
        simp
    · have hvl : v ≠ l.2.2 := by
        intro h
        apply hv
        rw [h, hMl.2]
      have e : (v ∈ (w ++ [l]).map (·.2.2)) ↔ v ∈ w.map (·.2.2) := by
        rw [hmem]
        exact or_iff_left hvl
      rw [if_neg hv, add_zero, ihw v]
      simp only [e]

theorem lrf_pt_L (v : Fin r × Fin n) :
    eval (lrf_idS R r n) (lrfc_Phi (lrf_L r n) (X v)) = lrf_ell R r n v := by
  rw [lrf_pt (lrf_L r n) lrf_pairwise (fun l hl => ⟨((lrf_mem_L l).1 hl).1, ((lrf_mem_L l).1 hl).2.2⟩) v]
  simp only [lrf_mem_vars, lrf_ell]

theorem lrf_eval_Phi (F : MvPolynomial (Fin r × Fin n) R) :
    eval (lrf_idS R r n) (lrfc_Phi (lrf_L r n) (lrfc_iota F)) = eval₂ C (lrf_ell R r n) F := by
  have h : ((eval (lrf_idS R r n)).comp ((lrfc_Phi (R := R) (lrf_L r n)).toRingHom.comp lrfc_iota)) =
      eval₂Hom C (lrf_ell R r n) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, lrfc_iota,
        map_C, coe_eval₂Hom, eval₂_C]
      have hC : lrfc_Phi (lrf_L r n) (C (C c)) = C (C c : MvPolynomial (Fin r × Fin n) R) :=
        (lrfc_Phi (lrf_L r n)).commutes (C c)
      rw [hC, eval_C]
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, lrfc_iota,
        map_X, coe_eval₂Hom, eval₂_X]
      exact lrf_pt_L v
  exact congrArg (fun φ => φ F) h

theorem lrf_eval_coeffT (d : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval (idFrame R r n) (lrfc_coeffT d G) = coeff d (eval (lrf_idS R r n) G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [lrfc_coeffT_monomial, eval_monomial, eval_monomial]
    have h : (u.prod fun i k => lrf_idS R r n i ^ k) = C (u.prod fun i k => idFrame R r n i ^ k) := by
      simp only [lrf_idS, Finsupp.prod, map_prod, map_pow]
    rw [h, mul_comm c, coeff_C_mul, mul_comm]
  | add p q hp hq => rw [lrfc_coeffT_add, map_add, map_add, coeff_add, hp, hq]

def lrf_off (m : Fin r × Fin n →₀ ℕ) : Fin r × Fin n →₀ ℕ := m.filter fun v => v.2.val < v.1.val

theorem lrf_prod_lower (m : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) :
    (m.prod fun v k => lrf_ell R r n v ^ k) = monomial (lrf_off m) 1 := by
  classical
  rw [← Finsupp.prod_filter_mul_prod_filter_not (fun v : Fin r × Fin n => v.2.val < v.1.val)]
  have h2 : ((m.filter fun v : Fin r × Fin n => ¬ v.2.val < v.1.val).prod fun v k => lrf_ell R r n v ^ k) = 1 := by
    refine Finset.prod_eq_one fun v hv => ?_
    rw [Finsupp.support_filter, Finset.mem_filter, Finsupp.mem_support_iff] at hv
    have h3 : ¬ v.1.val < v.2.val := fun h => hv.1 (hm v.1 v.2 h)
    have h4 : v.1.val = v.2.val := by omega
    have h5 : lrf_ell R r n v = 1 := by simp [lrf_ell, idFrame, h4]
    beta_reduce
    rw [h5, one_pow]
  have h1 : ((m.filter fun v : Fin r × Fin n => v.2.val < v.1.val).prod fun v k => lrf_ell R r n v ^ k) =
      (m.filter fun v : Fin r × Fin n => v.2.val < v.1.val).prod fun v k => (X v : MvPolynomial (Fin r × Fin n) R) ^ k := by
    refine Finset.prod_congr rfl fun v hv => ?_
    rw [Finsupp.support_filter, Finset.mem_filter] at hv
    have h4 : ¬ v.1.val = v.2.val := by omega
    have h5 : lrf_ell R r n v = X v := by simp [lrf_ell, idFrame, h4, hv.2]
    beta_reduce
    rw [h5]
  rw [h1, h2, mul_one, lrf_off, monomial_eq, C_1, one_mul]

theorem lrf_prod_upper (m : Fin r × Fin n →₀ ℕ) (hm : ¬ LowerTri m) :
    (m.prod fun v k => lrf_ell R r n v ^ k) = 0 := by
  classical
  unfold LowerTri at hm
  push Not at hm
  obtain ⟨a, s, has, hne⟩ := hm
  refine Finset.prod_eq_zero (i := (a, s)) (Finsupp.mem_support_iff.mpr hne) ?_
  have h4 : ¬ a.val = s.val := by omega
  have h6 : ¬ s.val < a.val := by omega
  have h5 : lrf_ell R r n (a, s) = 0 := by simp [lrf_ell, idFrame, h4, h6]
  beta_reduce
  rw [h5, zero_pow hne]

theorem lrf_unique (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e) (hoff : lrf_off m = lrf_off e)
    (hcol : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s)) : m = e := by
  classical
  have hlow : ∀ (a : Fin r) (s : Fin n), s.val < a.val → m (a, s) = e (a, s) := by
    intro a s h
    have h1 := DFunLike.congr_fun hoff (a, s)
    simpa [lrf_off, Finsupp.filter_apply, h] using h1
  have hne : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = e (a, s) := by
    intro a s h
    rcases lt_or_gt_of_ne h with h' | h'
    · rw [hm a s h', he a s h']
    · exact hlow a s h'
  ext ⟨a, s⟩
  by_cases h : a.val = s.val
  · have h1 := hcol s
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ (fun a => e (a, s)) (Finset.mem_univ a)] at h1
    have h2 : ∑ x ∈ Finset.univ.erase a, m (x, s) = ∑ x ∈ Finset.univ.erase a, e (x, s) := by
      refine Finset.sum_congr rfl fun x hx => hne x s ?_
      intro hxs
      exact (Finset.ne_of_mem_erase hx) (Fin.ext (by omega))
    omega
  · exact hne a s h

theorem lrf_coeff_ell (ν : Fin n → ℕ) (F : MvPolynomial (Fin r × Fin n) R) (e : Fin r × Fin n →₀ ℕ)
    (hF : IsWeightedHomogeneous (colW r n) F ν) (he : LowerTri e) (hcol : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s) :
    coeff (lrf_off e) (eval₂ C (lrf_ell R r n) F) = coeff e F := by
  classical
  rw [eval₂_eq', coeff_sum]
  have key : ∀ m ∈ F.support, coeff (lrf_off e) (C (coeff m F) * ∏ i, lrf_ell R r n i ^ m i) =
      if m = e then coeff m F else 0 := by
    intro m hm
    have hp : (∏ i, lrf_ell R r n i ^ m i) = m.prod fun v k => lrf_ell R r n v ^ k := by
      rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
    rw [hp, coeff_C_mul]
    by_cases hl : LowerTri m
    · rw [lrf_prod_lower m hl, coeff_monomial]
      by_cases hme : m = e
      · subst hme
        simp
      · rw [if_neg hme, if_neg, mul_zero]
        intro hoff
        apply hme
        refine lrf_unique m e hl he hoff fun s => ?_
        rw [hcol s, ← lccomp_weight_colW_apply, hF (mem_support_iff.mp hm)]
    · rw [lrf_prod_upper m hl, coeff_zero, mul_zero, if_neg]
      rintro rfl
      exact hl he
  rw [Finset.sum_congr rfl key, Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · exact (notMem_support_iff.mp h).symm

end

theorem coefficient_word : CoeffWord := by
  intro R _ r n ν F e hF he hcol
  classical
  have hd : ∀ (a : Fin r) (s : Fin n), s.val < a.val → lrf_off e (a, s) = e (a, s) := by
    intro a s h
    simp [lrf_off, Finsupp.filter_apply, h]
  have h1 := lrfc_coeffT_Phi (lrf_L r n) lrf_nodup F (lrf_off e)
  have hc : ∀ u, u ∉ (lrf_L r n).map (·.2.2) → lrf_off e u = 0 := by
    intro u hu
    rw [lrf_mem_vars] at hu
    simp [lrf_off, Finsupp.filter_apply, hu]
  rw [if_pos hc, lrf_wordOf e (lrf_off e) hd] at h1
  rw [← h1, lrf_eval_coeffT, lrf_eval_Phi, lrf_coeff_ell ν F e hF he hcol]

end Formalism.CohomologicalDescent.LR
