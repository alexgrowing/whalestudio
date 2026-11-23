import Formalism.LocalToGlobal.GroupLattices.FockModels.TransposeWords.FockPairingHighestWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.ColSums

open MvPolynomial

noncomputable section

namespace Formalism.L2.G.Model.TS

open Formalism.GradedWeylDivisibility

section

variable {R : Type*} [CommRing R] {r n : ℕ}

def cwl_iota : MvPolynomial (Fin r × Fin n) R →+*
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  MvPolynomial.map (C : R →+* MvPolynomial (Fin r × Fin n) R)

def cwl_coeffT (d : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    MvPolynomial (Fin r × Fin n) R :=
  ∑ m ∈ G.support, monomial m (coeff d (coeff m G))

theorem cwl_coeff_coeffT (d m : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    coeff m (cwl_coeffT d G) = coeff d (coeff m G) := by
  classical
  unfold cwl_coeffT
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, coeff_zero]

theorem cwl_coeffT_add (d : Fin r × Fin n →₀ ℕ)
    (G H : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_coeffT d (G + H) = cwl_coeffT d G + cwl_coeffT d H := by
  ext m
  simp [cwl_coeff_coeffT]

theorem cwl_coeffT_zero (d : Fin r × Fin n →₀ ℕ) :
    cwl_coeffT (R := R) d 0 = 0 := by
  ext m
  simp [cwl_coeff_coeffT]

theorem cwl_coeffT_sum {ι : Type*} (s : Finset ι) (d : Fin r × Fin n →₀ ℕ)
    (G : ι → MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_coeffT d (∑ i ∈ s, G i) = ∑ i ∈ s, cwl_coeffT d (G i) := by
  ext m
  simp [cwl_coeff_coeffT, coeff_sum]

theorem cwl_coeffT_monomial (d u : Fin r × Fin n →₀ ℕ) (c : MvPolynomial (Fin r × Fin n) R) :
    cwl_coeffT d (monomial u c) = monomial u (coeff d c) := by
  classical
  ext m
  rw [cwl_coeff_coeffT, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

theorem cwl_coeffT_C_monomial_mul (d s : Fin r × Fin n →₀ ℕ)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_coeffT d (C (monomial s 1) * G) = if s ≤ d then cwl_coeffT (d - s) G else 0 := by
  classical
  ext m
  rw [cwl_coeff_coeffT, coeff_C_mul, coeff_monomial_mul', one_mul]
  split_ifs
  · rw [cwl_coeff_coeffT]
  · simp

theorem cwl_coeffT_iota (d : Fin r × Fin n →₀ ℕ) (F : MvPolynomial (Fin r × Fin n) R) :
    cwl_coeffT d (cwl_iota F) = if d = 0 then F else 0 := by
  classical
  ext m
  rw [cwl_coeff_coeffT, cwl_iota, coeff_map, coeff_C]
  split_ifs with h1 h2 h2 <;> simp_all [eq_comm]

def cwl_tau (l : Fin r × Fin r × (Fin r × Fin n)) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => X v + if v.1 = l.2.1 then C (X l.2.2) * X (l.1, v.2) else 0

theorem cwl_tau_iota (l : Fin r × Fin r × (Fin r × Fin n)) (F : MvPolynomial (Fin r × Fin n) R) :
    cwl_tau l (cwl_iota F) =
      Polynomial.eval₂ cwl_iota (C (X l.2.2)) (rowGen R l.1 l.2.1 F) := by
  have h : ((cwl_tau (R := R) l).toRingHom.comp cwl_iota) =
      (Polynomial.eval₂RingHom cwl_iota (C (X l.2.2))).comp (rowGen R l.1 l.2.1).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [cwl_tau, cwl_iota, rowGen]
    · intro i
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      simp only [cwl_tau, cwl_iota, rowGen, aeval_X, map_X, Polynomial.coe_eval₂RingHom]
      split_ifs
      · simp
        exact mul_comm _ _
      · simp
  exact congrArg (fun φ => φ F) h

def cwl_Phi (L : List (Fin r × Fin r × (Fin r × Fin n))) :
    MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) →ₐ[MvPolynomial (Fin r × Fin n) R]
      MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R) :=
  L.foldr (fun l φ => (cwl_tau l).comp φ) (AlgHom.id _ _)

theorem cwl_Phi_nil (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_Phi [] G = G := rfl

theorem cwl_Phi_cons (l : Fin r × Fin r × (Fin r × Fin n)) (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_Phi (l :: w) G = cwl_tau l (cwl_Phi w G) := rfl

theorem cwl_Phi_append_single (w : List (Fin r × Fin r × (Fin r × Fin n)))
    (l : Fin r × Fin r × (Fin r × Fin n))
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    cwl_Phi (w ++ [l]) G = cwl_Phi w (cwl_tau l G) := by
  induction w with
  | nil => rfl
  | cons x w ih => rw [List.cons_append, cwl_Phi_cons, ih, cwl_Phi_cons]

theorem cwl_applyWord_append_single (w : List (Fin r × Fin r × ℕ)) (x : Fin r × Fin r × ℕ)
    (F : MvPolynomial (Fin r × Fin n) R) :
    applyWord R (w ++ [x]) F = applyWord R w (rowDiv R x.1 x.2.1 x.2.2 F) := by
  simp [applyWord, List.foldr_append]

theorem cwl_applyWord_zero (w : List (Fin r × Fin r × ℕ)) :
    applyWord R w (0 : MvPolynomial (Fin r × Fin n) R) = 0 := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih]
    simp [rowDiv]

theorem cwl_coeffT_Phi (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (hL : (L.map (·.2.2)).Nodup) (F : MvPolynomial (Fin r × Fin n) R) (d : Fin r × Fin n →₀ ℕ) :
    cwl_coeffT d (cwl_Phi L (cwl_iota F)) =
      if (∀ u, u ∉ L.map (·.2.2) → d u = 0) then
        applyWord R (L.map fun l => (l.1, l.2.1, d l.2.2)) F else 0 := by
  classical
  induction L using List.reverseRecOn generalizing F d with
  | nil =>
    rw [cwl_Phi_nil, cwl_coeffT_iota]
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
    rw [cwl_Phi_append_single, cwl_tau_iota, Polynomial.eval₂_eq_sum, Polynomial.sum_def,
      map_sum, cwl_coeffT_sum]
    have key : ∀ (j : ℕ) (c : MvPolynomial (Fin r × Fin n) R),
        cwl_coeffT d (cwl_Phi w (cwl_iota c * C (X (s, a, v).2.2) ^ j)) =
          if j ≤ d v then cwl_coeffT (d - Finsupp.single v j) (cwl_Phi w (cwl_iota c)) else 0 := by
      intro j c
      have hC : cwl_Phi w (C (X v ^ j) : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) =
          C (X v ^ j) := (cwl_Phi w).commutes (X v ^ j)
      have hp : (C (X v) : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) ^ j = C (X v ^ j) :=
        (C.map_pow _ _).symm
      simp only
      rw [hp, map_mul, hC, mul_comm, X_pow_eq_monomial, cwl_coeffT_C_monomial_mul]
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
        simp [Ne.symm hne]
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
      · rw [List.map_append, List.map_cons, List.map_nil, cwl_applyWord_append_single]
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
      simp [cwl_applyWord_zero]

theorem cw_eval_coeffT (d : Fin r × Fin n →₀ ℕ) (y : Fin r × Fin n → R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_coeffT d G) = coeff d (eval (fun v => C (y v)) G) := by
  induction G using MvPolynomial.induction_on' with
  | monomial u c =>
    rw [cwl_coeffT_monomial, eval_monomial, eval_monomial]
    have h : (u.prod fun v k => (C (y v) : MvPolynomial (Fin r × Fin n) R) ^ k) =
        C (u.prod fun v k => y v ^ k) := by
      simp [Finsupp.prod, map_prod]
    rw [h, mul_comm c, coeff_C_mul, mul_comm]
  | add p q hp hq => rw [cwl_coeffT_add, map_add, map_add, coeff_add, hp, hq]

def cwUpd (l : Fin r × Fin r × (Fin r × Fin n)) (y : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R) :
    Fin r × Fin n → MvPolynomial (Fin r × Fin n) R :=
  fun v => y v + if v.1 = l.2.1 then X l.2.2 * y (l.1, v.2) else 0

theorem cw_eval_tau (l : Fin r × Fin r × (Fin r × Fin n)) (y : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_tau l G) = eval (cwUpd l y) G := by
  have h : (eval y).comp (cwl_tau (R := R) l).toRingHom = eval (cwUpd l y) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [cwl_tau]
    · intro v
      simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        cwl_tau, aeval_X, cwUpd, eval_X, map_add]
      split_ifs <;> simp
  exact congrArg (fun φ => φ G) h

theorem cw_eval_Phi (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (y : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R)
    (G : MvPolynomial (Fin r × Fin n) (MvPolynomial (Fin r × Fin n) R)) :
    eval y (cwl_Phi L G) = eval (L.foldl (fun y l => cwUpd l y) y) G := by
  induction L generalizing y with
  | nil => rfl
  | cons l w ih => rw [cwl_Phi_cons, cw_eval_tau, ih]; rfl

theorem cw_foldl_point (L : List (Fin r × Fin r × (Fin r × Fin n)))
    (h1 : ∀ l ∈ L, l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val)
    (h2 : L.Pairwise fun l l' => l'.1.val ≤ l.1.val ∧ l.2.2 ≠ l'.2.2) :
    L.foldl (fun y l => cwUpd l y) (idFrame (MvPolynomial (Fin r × Fin n) R) r n) =
      fun v => idFrame (MvPolynomial (Fin r × Fin n) R) r n v + if v ∈ L.map (·.2.2) then X v else 0 := by
  classical
  induction L using List.reverseRecOn with
  | nil => funext v; simp
  | append_singleton w l ih =>
    have h1w : ∀ l ∈ w, l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val :=
      fun x hx => h1 x (by simp [hx])
    rw [List.pairwise_append] at h2
    obtain ⟨h2w, -, h2l⟩ := h2
    have hl := h1 l (by simp)
    rw [List.foldl_append, ih h1w h2w]
    funext v
    simp only [List.foldl_cons, List.foldl_nil, cwUpd]
    have hno : (l.1, v.2) ∉ w.map (·.2.2) := by
      intro hmem
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
      have a1 := h1w x hx
      have a2 := (h2l x hx l (by simp)).1
      have a3 : x.2.2.1 = l.1 := by rw [hxe]
      have a4 : x.2.1 = l.1 := by rw [← a1.1, a3]
      rw [a4] at a1
      omega
    have hlw : l.2.2 ∉ w.map (·.2.2) := by
      intro hmem
      obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hmem
      exact (h2l x hx l (by simp)).2 hxe
    rw [if_neg hno, add_zero]
    by_cases hv : v = l.2.2
    · subst hv
      have e1 : l.2.2.1 = l.2.1 := hl.1
      have e2 : idFrame (MvPolynomial (Fin r × Fin n) R) r n (l.1, l.2.2.2) = 1 := by
        simp [idFrame, hl.2.1]
      rw [if_neg hlw, if_pos e1, e2]
      simp
    · have hcond : ¬ (v.1 = l.2.1 ∧ l.1.val = v.2.val) := by
        rintro ⟨c1, c2⟩
        apply hv
        apply Prod.ext
        · rw [c1, hl.1]
        · apply Fin.ext; rw [← c2, hl.2.1]
      have e3 : (if v.1 = l.2.1 then X l.2.2 * idFrame (MvPolynomial (Fin r × Fin n) R) r n (l.1, v.2) else 0) = 0 := by
        split_ifs with c1
        · have : ¬ l.1.val = v.2.val := fun c2 => hcond ⟨c1, c2⟩
          simp [idFrame, this]
        · rfl
      rw [e3, add_zero]
      simp [hv]

def cwLetters (r n : ℕ) : List (Fin r × Fin r × (Fin r × Fin n)) :=
  ((List.finRange n).reverse.flatMap fun s =>
    (List.finRange r).filterMap fun a =>
      if h : s.val < a.val ∧ s.val < r then some (⟨s.val, h.2⟩, a, (a, s)) else none)

theorem cw_mem_letters (l : Fin r × Fin r × (Fin r × Fin n)) :
    l ∈ cwLetters r n ↔ l.2.2.1 = l.2.1 ∧ l.2.2.2.val = l.1.val ∧ l.1.val < l.2.1.val := by
  obtain ⟨s, a, a', s'⟩ := l
  simp only [cwLetters, List.mem_flatMap, List.mem_reverse, List.mem_finRange, true_and, List.mem_filterMap]
  constructor
  · rintro ⟨t, b, hb⟩
    split_ifs at hb with h
    · simp only [Option.some.injEq, Prod.mk.injEq] at hb
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hb
      exact ⟨rfl, rfl, h.1⟩
  · rintro ⟨e1, e2, e3⟩
    have e1' : a' = a := e1
    have e2' : s'.val = s.val := e2
    have e3' : s.val < a.val := e3
    subst e1'
    refine ⟨s', a', ?_⟩
    rw [dif_pos ⟨by omega, by omega⟩]
    simp only [Option.some.injEq, Prod.mk.injEq, and_true]
    exact Fin.ext e2'

theorem cw_letters_pairwise :
    (cwLetters r n).Pairwise fun l l' => l'.1.val ≤ l.1.val ∧ l.2.2 ≠ l'.2.2 := by
  unfold cwLetters
  rw [List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_filterMap]
    refine (List.pairwise_lt_finRange r).imp ?_
    intro a a' haa b hb b' hb'
    split_ifs at hb with h
    split_ifs at hb' with h'
    simp only [Option.some.injEq] at hb hb'
    subst hb hb'
    refine ⟨le_refl _, ?_⟩
    intro hc
    simp only [Prod.mk.injEq, and_true] at hc
    exact absurd hc (ne_of_lt haa)
  · rw [List.pairwise_reverse]
    refine (List.pairwise_lt_finRange n).imp ?_
    intro s s' hss x hx y hy
    simp only [List.mem_filterMap, List.mem_finRange, true_and] at hx hy
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    split_ifs at ha with h
    split_ifs at hb with h'
    simp only [Option.some.injEq] at ha hb
    subst ha hb
    refine ⟨le_of_lt hss, ?_⟩
    intro hc
    simp only [Prod.mk.injEq] at hc
    exact absurd hc.2 (ne_of_gt hss)

theorem cw_wordOf (e : Fin r × Fin n →₀ ℕ) :
    wordOf e = (cwLetters r n).map fun l => (l.1, l.2.1, e l.2.2) := by
  unfold wordOf cwLetters
  rw [List.map_flatMap]
  congr 1
  funext s
  rw [List.map_filterMap]
  congr 1
  funext a
  split_ifs <;> rfl

def cwStrict (m : Fin r × Fin n →₀ ℕ) : Fin r × Fin n →₀ ℕ := m.filter fun v => v.2.val < v.1.val

def cwPt : Fin r × Fin n → MvPolynomial (Fin r × Fin n) R := fun v =>
  idFrame (MvPolynomial (Fin r × Fin n) R) r n v + if v.2.val < v.1.val then X v else 0

open Classical in
theorem cw_prod_pt (m : Fin r × Fin n →₀ ℕ) :
    (∏ v, (cwPt (R := R) v) ^ m v) = if LowerTri m then monomial (cwStrict m) 1 else 0 := by
  classical
  split_ifs with h
  · rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (by simp)]
    apply Finset.prod_congr rfl
    rintro ⟨a, s⟩ _
    rcases lt_trichotomy a.val s.val with c | c | c
    · have h0 := h a s c
      simp [cwStrict, h0, not_lt.mpr (le_of_lt c)]
    · simp [cwPt, idFrame, c, cwStrict]
    · simp [cwPt, idFrame, c, ne_of_gt c, cwStrict]
  · unfold LowerTri at h
    push Not at h
    obtain ⟨a, s, c, hne⟩ := h
    apply Finset.prod_eq_zero (Finset.mem_univ (a, s))
    have h0 : cwPt (R := R) (a, s) = 0 := by simp [cwPt, idFrame, ne_of_lt c, not_lt.mpr (le_of_lt c)]
    rw [h0, zero_pow hne]

theorem cw_ext (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e) (hs : cwStrict m = cwStrict e)
    (hc : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s)) : m = e := by
  classical
  have off : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = e (a, s) := by
    intro a s hne
    rcases lt_or_gt_of_ne hne with c | c
    · rw [hm a s c, he a s c]
    · have h0 := DFunLike.congr_fun hs (a, s)
      simpa [cwStrict, Finsupp.filter_apply, c] using h0
  ext ⟨a, s⟩
  by_cases h : a.val = s.val
  · have h0 := hc s
    rw [← Finset.add_sum_erase _ (fun x => m (x, s)) (Finset.mem_univ a),
      ← Finset.add_sum_erase _ (fun x => e (x, s)) (Finset.mem_univ a)] at h0
    have h2 : ∑ x ∈ Finset.univ.erase a, m (x, s) = ∑ x ∈ Finset.univ.erase a, e (x, s) := by
      apply Finset.sum_congr rfl
      intro x hx
      apply off
      intro hxs
      exact (Finset.mem_erase.mp hx).1 (Fin.ext (by omega))
    omega
  · exact off a s h

end

theorem coeffWord' : CoeffWord := by
  classical
  intro R _ r n ν F e hF he hsum
  have hw : wordOf e = (cwLetters r n).map fun l => (l.1, l.2.1, cwStrict e l.2.2) := by
    rw [cw_wordOf]
    apply List.map_congr_left
    intro l hl
    have h0 := (cw_mem_letters l).mp hl
    have hlt : l.2.2.2.val < l.2.2.1.val := by rw [h0.1, h0.2.1]; exact h0.2.2
    simp [cwStrict, hlt]
  have hnd : ((cwLetters r n).map (·.2.2)).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact cw_letters_pairwise.imp fun h => h.2
  have hmem : ∀ v : Fin r × Fin n, v ∈ (cwLetters r n).map (·.2.2) ↔ v.2.val < v.1.val := by
    intro v
    rw [List.mem_map]
    constructor
    · rintro ⟨l, hl, rfl⟩
      have h0 := (cw_mem_letters l).mp hl
      rw [h0.1, h0.2.1]; exact h0.2.2
    · intro hv
      exact ⟨(⟨v.2.val, by omega⟩, v.1, v), (cw_mem_letters _).mpr ⟨rfl, rfl, hv⟩, rfl⟩
  have hcond : ∀ u, u ∉ (cwLetters r n).map (·.2.2) → cwStrict e u = 0 := by
    intro u hu
    rw [hmem] at hu
    simp [cwStrict, hu]
  have key := cwl_coeffT_Phi (cwLetters r n) hnd F (cwStrict e)
  rw [if_pos hcond, ← hw] at key
  rw [← key, cw_eval_coeffT]
  have hid : (fun v => (C (idFrame R r n v) : MvPolynomial (Fin r × Fin n) R)) =
      idFrame (MvPolynomial (Fin r × Fin n) R) r n := by
    funext v
    simp only [idFrame]
    split_ifs <;> simp
  rw [hid, cw_eval_Phi, cw_foldl_point _ (fun l hl => (cw_mem_letters l).mp hl) cw_letters_pairwise]
  have hpt : (fun v => idFrame (MvPolynomial (Fin r × Fin n) R) r n v +
      if v ∈ (cwLetters r n).map (·.2.2) then X v else 0) = cwPt := by
    funext v
    simp only [hmem]
    rfl
  rw [hpt, cwl_iota, eval_map, eval₂_eq', coeff_sum]
  simp only [coeff_C_mul, cw_prod_pt]
  rw [Finset.sum_eq_single e]
  · rw [if_pos he, coeff_monomial, if_pos rfl, mul_one]
  · intro m hm hne
    split_ifs with hL
    · rw [coeff_monomial, if_neg, mul_zero]
      intro hs
      apply hne
      refine cw_ext m e hL he hs fun s => ?_
      rw [hsum s, ← lccomp_weight_colW_apply, hF (mem_support_iff.mp hm)]
    · simp
  · intro h
    rw [notMem_support_iff.mp h, zero_mul]

end Formalism.L2.G.Model.TS
