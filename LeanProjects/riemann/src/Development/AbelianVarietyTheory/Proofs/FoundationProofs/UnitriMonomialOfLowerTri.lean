import Mathlib
import Formalism.GradedWeylDivisibility.StatementE

open MvPolynomial Formalism.GradedWeylDivisibility

noncomputable section

namespace GlobalTheory.CoeffWord

variable {R : Type} [CommRing R] {r n : ℕ}

def unitri (R : Type) [CommRing R] (L : List (Fin r × Fin n)) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] MvPolynomial (Fin r × Fin n) R :=
  aeval fun v => if v.1.val = v.2.val then 1 else if v ∈ L then X v else 0

def single (R : Type) [CommRing R] (p : Fin r × Fin n) :
    MvPolynomial (Fin r × Fin n) R →ₐ[R] Polynomial (MvPolynomial (Fin r × Fin n) R) :=
  aeval fun v => if v = p then Polynomial.X else Polynomial.C (X v)

theorem single_monomial (p : Fin r × Fin n) (m : Fin r × Fin n →₀ ℕ) (c : R) :
    single R p (monomial m c) = Polynomial.monomial (m p) (monomial (m.erase p) c) := by
  classical
  have h1 : (monomial m c : MvPolynomial (Fin r × Fin n) R) = monomial (m.erase p) c * X p ^ (m p) := by
    rw [X_pow_eq_monomial, monomial_mul, mul_one, Finsupp.erase_add_single]
  have h2 : single R p (monomial (m.erase p) c) = Polynomial.C (monomial (m.erase p) c) := by
    rw [single, aeval_monomial, monomial_eq, map_mul, map_finsuppProd]
    congr 1
    refine Finsupp.prod_congr fun v hv => ?_
    have : v ≠ p := by
      rintro rfl
      simp at hv
    simp [this]
  have h3 : single R p (X p) = Polynomial.X := by simp [single]
  rw [h1, map_mul, map_pow, h2, h3, Polynomial.C_mul_X_pow_eq_monomial]

theorem coeff_single (p : Fin r × Fin n) (e : Fin r × Fin n →₀ ℕ) (he : e p = 0) (k : ℕ)
    (G : MvPolynomial (Fin r × Fin n) R) :
    coeff e ((single R p G).coeff k) = coeff (e + Finsupp.single p k) G := by
  classical
  induction G using MvPolynomial.induction_on' with
  | add G H hG hH => simp [hG, hH]
  | monomial m c =>
    rw [single_monomial, Polynomial.coeff_monomial, coeff_monomial]
    by_cases h : m = e + Finsupp.single p k
    · have h1 : m p = k := by simp [h, he]
      have h2 : m.erase p = e := by
        ext v
        by_cases hv : v = p
        · simp [hv, he]
        · simp [h, Finsupp.erase_ne hv, Finsupp.single_apply, Ne.symm hv]
      simp [h1, h2, ← h]
    · rw [if_neg h]
      split_ifs with h1
      · rw [coeff_monomial, if_neg]
        intro h2
        apply h
        rw [← h2, ← h1, Finsupp.erase_add_single]
      · simp

theorem map_rowGen (L : List (Fin r × Fin n)) (p : Fin r × Fin n) (s : Fin r) (hs : s.val = p.2.val)
    (hp : p.2.val < p.1.val) (hpL : p ∉ L) (hL : ∀ q ∈ L, q.2.val < q.1.val ∧ p.2.val ≤ q.2.val)
    (F : MvPolynomial (Fin r × Fin n) R) :
    (rowGen R s p.1 F).map (unitri R L).toRingHom = single R p (unitri R (L ++ [p]) F) := by
  have : (Polynomial.mapRingHom (unitri R L).toRingHom).comp (rowGen R s p.1).toRingHom =
      (single R p).toRingHom.comp (unitri R (L ++ [p])).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
    · simp [rowGen, single, unitri]
    · by_cases hv : v = p
      · subst hv
        simp [rowGen, single, unitri, hs, hp.ne', hpL]
      · have h0 : v.1 = p.1 → unitri R L (X (s, v.2)) = 0 := by
          intro h1
          have h2 : v.2.val ≠ p.2.val := fun h => hv (Prod.ext h1 (Fin.ext h))
          have h3 : (s, v.2) ∉ L := fun h => by
            have := hL _ h
            simp only at this
            omega
          have h4 : s.val ≠ v.2.val := by omega
          simp [unitri, h3, h4]
        have h5 : single R p (unitri R (L ++ [p]) (X v)) = Polynomial.C (unitri R L (X v)) := by
          simp only [unitri, aeval_X, List.mem_append, List.mem_singleton, hv, or_false]
          split_ifs <;> simp [single, hv]
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h5, rowGen, aeval_X,
          Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_C]
        split_ifs with h1
        · simp [h0 h1]
        · simp
  exact RingHom.congr_fun this F

def letter (e : Fin r × Fin n →₀ ℕ) (p : Fin r × Fin n) : Fin r × Fin r × ℕ :=
  (if h : p.2.val < r then ⟨p.2.val, h⟩ else p.1, p.1, e p)

theorem eval_applyWord (e : Fin r × Fin n →₀ ℕ) (L : List (Fin r × Fin n))
    (h1 : ∀ q ∈ L, q.2.val < q.1.val) (h2 : L.Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val)
    (F : MvPolynomial (Fin r × Fin n) R) :
    eval (idFrame R r n) (applyWord R (L.map (letter e)) F) =
      coeff (e.filter (· ∈ L)) (unitri R L F) := by
  induction L using List.reverseRecOn generalizing F with
  | nil =>
    have h : (eval (idFrame R r n)) = constantCoeff.comp (unitri R ([] : List (Fin r × Fin n))).toRingHom := by
      refine MvPolynomial.ringHom_ext (fun c => ?_) (fun v => ?_)
      · simp [unitri]
      · simp only [unitri, idFrame, eval_X, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X]
        split_ifs <;> simp_all
    have h' : e.filter (· ∈ ([] : List (Fin r × Fin n))) = 0 := by
      ext v; simp
    rw [h', h]
    rfl
  | append_singleton L p ih =>
    rw [List.pairwise_append] at h2
    obtain ⟨h2, -, h3⟩ := h2
    have hp := h1 p (by simp)
    have hpr : p.2.val < r := lt_trans hp p.1.2
    have hL1 : ∀ q ∈ L, q.2.val < q.1.val := fun q hq => h1 q (by simp [hq])
    have hpL : p ∉ L := fun h => (h3 p h p (by simp)).1 rfl
    have hw : applyWord R ((L ++ [p]).map (letter e)) F =
        applyWord R (L.map (letter e)) (rowDiv R ⟨p.2.val, hpr⟩ p.1 (e p) F) := by
      simp [applyWord, letter, hpr]
    rw [hw, ih hL1 h2]
    have hm := map_rowGen (R := R) L p ⟨p.2.val, hpr⟩ rfl hp hpL
      (fun q hq => ⟨hL1 q hq, (h3 q hq p (by simp)).2⟩) F
    have hc := congrArg (fun P => Polynomial.coeff P (e p)) hm
    simp only [Polynomial.coeff_map] at hc
    have hc' : unitri R L (rowDiv R ⟨p.2.val, hpr⟩ p.1 (e p) F) =
        (single R p (unitri R (L ++ [p]) F)).coeff (e p) := hc
    rw [hc', coeff_single _ _ (by simp [Finsupp.filter_apply, hpL])]
    congr 1
    ext v
    by_cases hv : v = p
    · subst hv; simp [Finsupp.filter_apply, hpL]
    · simp [Finsupp.filter_apply, hv, Finsupp.single_apply, Ne.symm hv]

def positions (r n : ℕ) : List (Fin r × Fin n) :=
  (List.finRange n).reverse.flatMap fun s =>
    ((List.finRange r).filter fun a => s.val < a.val).map fun a => (a, s)

theorem mem_positions (v : Fin r × Fin n) : v ∈ positions r n ↔ v.2.val < v.1.val := by
  obtain ⟨a, s⟩ := v
  simp [positions]

theorem wordOf_eq (e : Fin r × Fin n →₀ ℕ) : wordOf e = (positions r n).map (letter e) := by
  rw [wordOf, positions, List.map_flatMap]
  congr 1
  funext s
  rw [List.map_map]
  generalize List.finRange r = l
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : s.val < a.val
    · have hr : s.val < r := lt_trans h a.2
      rw [List.filterMap_cons, dif_pos ⟨h, hr⟩, List.filter_cons_of_pos (by simpa using h)]
      simp only [List.map_cons, ih]
      simp [letter, hr]
    · rw [List.filterMap_cons, dif_neg (fun h' => h h'.1), List.filter_cons_of_neg (by simpa using h)]
      exact ih

theorem pairwise_positions :
    (positions r n).Pairwise fun q p => q ≠ p ∧ p.2.val ≤ q.2.val := by
  rw [positions, List.pairwise_flatMap]
  constructor
  · intro s _
    rw [List.pairwise_map]
    refine List.Pairwise.imp ?_ ((List.nodup_finRange r).filter _)
    intro a b hab
    exact ⟨fun h => hab (congrArg Prod.fst h), le_rfl⟩
  · rw [List.pairwise_reverse]
    refine List.Pairwise.imp ?_ (List.pairwise_lt_finRange n)
    intro s t hst x hx y hy
    simp only [List.mem_map] at hx hy
    obtain ⟨a, -, rfl⟩ := hx
    obtain ⟨b, -, rfl⟩ := hy
    exact ⟨fun h => hst.ne' (congrArg Prod.snd h), hst.le⟩

theorem eq_of_filter_eq (m e : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (he : LowerTri e)
    (hs : ∀ s : Fin n, ∑ a : Fin r, m (a, s) = ∑ a : Fin r, e (a, s))
    (h : ∀ v : Fin r × Fin n, v.2.val < v.1.val → m v = e v) : m = e := by
  have key : ∀ (a : Fin r) (s : Fin n), a.val ≠ s.val → m (a, s) = e (a, s) := by
    intro a s hne
    rcases lt_or_gt_of_ne hne with h1 | h1
    · rw [hm a s h1, he a s h1]
    · exact h (a, s) h1
  ext ⟨a, s⟩
  by_cases ha : a.val = s.val
  · have h1 := hs s
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a), ← Finset.add_sum_erase _ _ (Finset.mem_univ a),
      Finset.sum_congr rfl (fun b hb => key b s (fun hb' =>
        (Finset.ne_of_mem_erase hb) (Fin.ext (hb'.trans ha.symm))))] at h1
    exact Nat.add_right_cancel h1
  · exact key a s ha

theorem unitri_monomial_of_lowerTri (m : Fin r × Fin n →₀ ℕ) (hm : LowerTri m) (c : R) :
    unitri R (positions r n) (monomial m c) = monomial (m.filter (· ∈ positions r n)) c := by
  classical
  rw [unitri, aeval_monomial, monomial_eq, Finsupp.prod_filter_index, Finsupp.support_filter,
    Finset.prod_filter]
  congr 1
  refine Finset.prod_congr rfl fun v hv => ?_
  have hv' : m v ≠ 0 := Finsupp.mem_support_iff.1 hv
  have h1 : ¬ v.1.val < v.2.val := fun h => hv' (hm v.1 v.2 h)
  by_cases h2 : v.1.val = v.2.val
  · simp [mem_positions, h2]
  · have h3 : v.2.val < v.1.val := by omega
    simp [mem_positions, h2, h3]

theorem unitri_monomial_of_not (m : Fin r × Fin n →₀ ℕ) (hm : ¬ LowerTri m) (c : R) :
    unitri R (positions r n) (monomial m c) = 0 := by
  simp only [LowerTri, not_forall] at hm
  obtain ⟨a, s, h, h0⟩ := hm
  rw [unitri, aeval_monomial, Finsupp.prod,
    Finset.prod_eq_zero (i := (a, s)) (Finsupp.mem_support_iff.2 h0), mul_zero]
  have h1 : ¬ s.val < a.val := by omega
  simp [mem_positions, h.ne, h1, h0]

theorem weight_colW (m : Fin r × Fin n →₀ ℕ) (s : Fin n) :
    Finsupp.weight (colW r n) m s = ∑ a : Fin r, m (a, s) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Finset.sum_apply, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [colW, Pi.single_apply]

theorem coeffWord : Formalism.GradedWeylDivisibility.CoeffWord := by
  classical
  intro R _ r n ν F e hF he hν
  rw [wordOf_eq, eval_applyWord e _ (fun q hq => (mem_positions q).1 hq) pairwise_positions]
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, coeff_sum, coeff_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hw : Finsupp.weight (colW r n) m = ν := hF (mem_support_iff.1 hm)
  by_cases hl : LowerTri m
  · rw [unitri_monomial_of_lowerTri m hl, coeff_monomial, coeff_monomial]
    refine if_congr ⟨fun h => by rw [h], fun h => ?_⟩ rfl rfl
    refine eq_of_filter_eq m e hl he (fun s => by rw [← weight_colW, hw, hν]) fun v hv => ?_
    have := DFunLike.congr_fun h v
    simpa [Finsupp.filter_apply, mem_positions, hv] using this
  · rw [unitri_monomial_of_not m hl, coeff_monomial, if_neg (fun h : m = e => hl (h ▸ he)), coeff_zero]

end GlobalTheory.CoeffWord
