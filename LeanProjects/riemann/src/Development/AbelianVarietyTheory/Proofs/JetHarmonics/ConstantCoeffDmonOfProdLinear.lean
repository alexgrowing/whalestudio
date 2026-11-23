import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofDApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeBilinearTermEqNegDoubleSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivationMemPowOfMemPowSucc

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.SymbolOne

section Abstract

variable {k A : Type} [CommRing k] [CommRing A] [Algebra k A]

theorem deriv_mem_pow (D : Derivation k A A) (I : Ideal A) (n : ℕ) (x : A) (hx : x ∈ I ^ (n + 1)) :
    D x ∈ I ^ n := by
  first
  | exact @_root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ
  | exact _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ
  | (apply _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DerivationMemPow.derivation_mem_pow_of_mem_pow_succ ..)

variable {ι : Type}

theorem word_mem (D : ι → Derivation k A A) (I : Ideal A) (w : List ι) (x : A)
    (hx : x ∈ I ^ (w.length + 1)) : w.foldl (fun g l => D l g) x ∈ I := by
  induction w generalizing x with
  | nil => simpa using hx
  | cons l w ih => exact ih _ (deriv_mem_pow _ _ _ _ hx)

theorem word_add (D : ι → Derivation k A A) (w : List ι) (x y : A) :
    w.foldl (fun g l => D l g) (x + y) = w.foldl (fun g l => D l g) x + w.foldl (fun g l => D l g) y := by
  induction w generalizing x y with
  | nil => rfl
  | cons l w ih => simp only [List.foldl_cons, map_add, ih]

theorem word_smul (D : ι → Derivation k A A) (w : List ι) (r : k) (x : A) :
    w.foldl (fun g l => D l g) (r • x) = r • w.foldl (fun g l => D l g) x := by
  induction w generalizing x with
  | nil => rfl
  | cons l w ih => simp only [List.foldl_cons, Derivation.map_smul, ih]

variable [Fintype ι] [DecidableEq ι]

theorem prod_pow_mem (I : Ideal A) (lam : ι → A) (hlam : ∀ l, lam l ∈ I) (a : ι → ℕ) :
    ∏ l, lam l ^ a l ∈ I ^ (∑ l, a l) := by
  rw [← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun l _ => Ideal.pow_mem_pow (hlam l) _

theorem sum_update_pred (a : ι → ℕ) (j : ι) (h : a j ≠ 0) :
    ∑ l, Function.update a j (a j - 1) l + 1 = ∑ l, a l := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j), ← Finset.add_sum_erase _ a (Finset.mem_univ j),
    Finset.sdiff_singleton_eq_erase]
  omega

omit [Fintype ι] in
theorem deriv_prod (D : Derivation k A A) (f : ι → A) (s : Finset ι) :
    D (∏ l ∈ s, f l) = ∑ j ∈ s, (∏ l ∈ s.erase j, f l) * D (f j) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Derivation.leibniz, ih, Finset.erase_insert hi,
      smul_eq_mul, smul_eq_mul, add_comm, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    rw [Finset.erase_insert_of_ne hij, Finset.prod_insert (fun h => hi (Finset.mem_of_mem_erase h)),
      mul_assoc]

theorem deriv_prod_pow (D : Derivation k A A) (lam : ι → A) (a : ι → ℕ) :
    D (∏ l, lam l ^ a l) =
      ∑ j, (a j : A) * (∏ l, lam l ^ Function.update a j (a j - 1) l) * D (lam j) := by
  rw [deriv_prod]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Derivation.leibniz_pow, ← Finset.mul_prod_erase _ _ (Finset.mem_univ j), Function.update_self]
  have : ∏ l ∈ Finset.univ.erase j, lam l ^ Function.update a j (a j - 1) l =
      ∏ l ∈ Finset.univ.erase j, lam l ^ a l :=
    Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [this]
  simp only [smul_eq_mul, nsmul_eq_mul]
  ring

theorem deriv_prod_pow_mul (D : Derivation k A A) (I : Ideal A) (lam : ι → A) (hlam : ∀ l, lam l ∈ I)
    (a : ι → ℕ) (l₀ : ι) (r : k)
    (hD : ∀ l, a l ≠ 0 → D (lam l) - algebraMap k A (if l = l₀ then r else 0) ∈ I) (E : A) :
    D ((∏ l, lam l ^ a l) * E) -
      ((a l₀ : k) * r) • ((∏ l, lam l ^ Function.update a l₀ (a l₀ - 1) l) * E) ∈ I ^ (∑ l, a l) := by
  have h1 : ∑ j, (a j : A) * (∏ l, lam l ^ Function.update a j (a j - 1) l) *
      (D (lam j) - algebraMap k A (if j = l₀ then r else 0)) ∈ I ^ (∑ l, a l) := by
    refine Ideal.sum_mem _ fun j _ => ?_
    by_cases hj : a j = 0
    · simp [hj]
    · rw [← sum_update_pred a j hj, pow_succ, mul_assoc]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_mul (prod_pow_mem I lam hlam _) (hD j hj))
  have h2 : ∑ j, (a j : A) * (∏ l, lam l ^ Function.update a j (a j - 1) l) *
      algebraMap k A (if j = l₀ then r else 0) =
      (a l₀ : A) * (∏ l, lam l ^ Function.update a l₀ (a l₀ - 1) l) * algebraMap k A r := by
    rw [Finset.sum_eq_single l₀]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  simp only [mul_sub, Finset.sum_sub_distrib] at h1
  rw [h2, ← deriv_prod_pow] at h1
  have h3 := add_mem (Ideal.mul_mem_right (D E) _ (prod_pow_mem I lam hlam a))
    (Ideal.mul_mem_right E _ h1)
  convert h3 using 1
  rw [Derivation.leibniz, Algebra.smul_def (_ * r)]
  simp only [smul_eq_mul, map_mul, map_natCast]
  ring

theorem word_value (π : A →ₐ[k] k) (D : ι → Derivation k A A) (lam : ι → A)
    (hlam : ∀ l, π (lam l) = 0) (α : ι → k) (w : List ι) (a : ι → ℕ) (E : A)
    (hD : ∀ l l', a l ≠ 0 → l' ∈ w → π (D l' (lam l)) = if l = l' then α l else 0)
    (hw : w.length ≤ ∑ l, a l) :
    π (w.foldl (fun g l => D l g) ((∏ l, lam l ^ a l) * E)) =
      if (∀ l, w.count l = a l) then (∏ l, ((a l).factorial : k) * α l ^ a l) * π E else 0 := by
  induction w generalizing a with
  | nil =>
    simp only [List.foldl_nil, map_mul, map_prod, map_pow, hlam]
    by_cases h : ∀ l, ([] : List ι).count l = a l
    · rw [if_pos h]
      simp [← h]
    · rw [if_neg h]
      simp only [List.count_nil] at h
      push Not at h
      obtain ⟨l, hl⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ l) (zero_pow hl.symm), zero_mul]
  | cons l₀ w ih =>
    set I : Ideal A := RingHom.ker π
    have key := deriv_prod_pow_mul (D l₀) I lam hlam a l₀ (α l₀) (fun l hl => by
      rw [RingHom.mem_ker, map_sub, hD l l₀ hl List.mem_cons_self, AlgHom.commutes]
      split_ifs with h
      · simp [h]
      · simp) E
    have key2 := word_mem D I w _ (Ideal.pow_le_pow_right (by simpa using hw) key)
    rw [RingHom.mem_ker] at key2
    rw [List.foldl_cons, ← sub_add_cancel (D l₀ _) (((a l₀ : k) * α l₀) •
      ((∏ l, lam l ^ Function.update a l₀ (a l₀ - 1) l) * E)), word_add, map_add, key2, zero_add,
      word_smul, map_smul]
    by_cases h0 : a l₀ = 0
    · rw [if_neg]
      · simp [h0]
      · intro h
        have := h l₀
        simp [h0] at this
    · have hs := sum_update_pred a l₀ h0
      rw [ih (Function.update a l₀ (a l₀ - 1))]
      · have hiff : (∀ l, w.count l = Function.update a l₀ (a l₀ - 1) l) ↔
            ∀ l, (l₀ :: w).count l = a l := by
          refine forall_congr' fun l => ?_
          by_cases hl : l = l₀
          · subst hl
            simp only [Function.update_self, List.count_cons_self]
            omega
          · rw [Function.update_of_ne hl, List.count_cons_of_ne (Ne.symm hl)]
        simp only [hiff]
        split_ifs with h
        · rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l₀),
            ← Finset.mul_prod_erase _ (fun l => ((a l).factorial : k) * α l ^ a l) (Finset.mem_univ l₀),
            Function.update_self]
          have : ∏ l ∈ Finset.univ.erase l₀, (((Function.update a l₀ (a l₀ - 1) l).factorial : k) *
              α l ^ Function.update a l₀ (a l₀ - 1) l) =
              ∏ l ∈ Finset.univ.erase l₀, (((a l).factorial : k) * α l ^ a l) :=
            Finset.prod_congr rfl fun l hl => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
          rw [this]
          obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
          rw [hn, smul_eq_mul]
          simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.factorial_succ]
          push_cast
          ring
        · simp
      · intro l l' hl hl'
        refine hD l l' ?_ (List.mem_cons_of_mem _ hl')
        by_cases h : l = l₀
        · rw [h]; exact h0
        · rwa [Function.update_of_ne h] at hl
      · simp only [List.length_cons] at hw
        omega

end Abstract

theorem exists_word {ι A : Type} [DecidableEq ι] (D : ι → A → A) (m : ι → ℕ) (L : List ι) :
    ∃ w : List ι, (∀ l, w.count l = L.count l * m l) ∧
      ∀ f, L.foldr (fun l g => (D l)^[m l] g) f = w.foldl (fun g l => D l g) f := by
  induction L with
  | nil => exact ⟨[], by simp, fun _ => rfl⟩
  | cons j L ih =>
    obtain ⟨w, h1, h2⟩ := ih
    refine ⟨w ++ List.replicate (m j) j, fun l => ?_, fun f => ?_⟩
    · rw [List.count_append, h1, List.count_replicate, List.count_cons]
      by_cases h : j = l
      · subst h; simp [add_mul]
      · simp [h]
    · rw [List.foldr_cons, List.foldl_append, h2]
      generalize w.foldl (fun g l => D l g) f = x
      generalize m j = n
      induction n generalizing x with
      | zero => rfl
      | succ n ih => rw [List.replicate_succ, List.foldl_cons, Function.iterate_succ_apply, ih]

theorem coeff_law {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (i j : Fin d) :
    coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F j) = if j = i then 1 else 0 := by
  have h := WickVanishing.coeff_ev_zero_left (G.F j) (Finsupp.single ((0 : Fin 1), i) 1)
  rw [G.unit, Finsupp.embDomain_single, coeff_X] at h
  change _ = coeff (Finsupp.single ((1 : Fin 2), i) 1) (G.F j) at h
  rw [← h]
  by_cases hij : j = i
  · simp [hij]
  · rw [if_neg hij, if_neg]
    intro h'
    rw [Finsupp.single_left_inj one_ne_zero] at h'
    exact hij (congrArg Prod.snd h').symm

theorem constantCoeff_dof_X {R k : Type} [CommRing R] [CommRing k] (φ : R →+* k) {d : ℕ}
    (G : FGLaw R d) (v : Fin d → k) (j : Fin d) :
    constantCoeff (Dof (G.mapF φ) v (X ((0 : Fin 1), j))) = v j := by
  have h : ∀ i j : Fin d, constantCoeff (ev (n := 1) ![pt k d 0, 0]
      (pderiv k ((1 : Fin 2), i) (G.mapF φ j))) = if j = i then 1 else 0 := by
    intro i j
    rw [← coeff_zero_eq_constantCoeff_apply, WickVanishing.coeff_ev_zero_right, Finsupp.embDomain_zero,
      coeff_pderiv, FGLaw.mapF, coeff_map, zero_add, coeff_law]
    split_ifs <;> simp
  unfold Dof
  simp only [map_sum, map_mul, h, constantCoeff_C]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj
    rw [pderiv_X_of_ne, map_zero, mul_zero]
    intro h'
    exact hj (by simpa using h'.symm)
  · simp

end GlobalTheory.SymbolOne

namespace GlobalTheory

open SymbolOne in

theorem constantCoeff_dmonOf_prod_linear :
    ∀ (R k : Type) [CommRing R] [CommRing k] (φ : R →+* k) (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι] [DecidableEq ι] (u lam : ι → Fin d → k) (α : ι → k) (al m : ι →₀ ℕ) (E : PS k 1 d), (∀ l l', al l ≠ 0 → m l' ≠ 0 → ∑ i, lam l i * u l' i = if l = l' then α l else 0) → m.degree ≤ al.degree → constantCoeff (DmonOf (G.mapF φ) u m ((∏ l, (∑ i, C (lam l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al l) * E)) = if m = al then (∏ l, ((al l).factorial : k) * α l ^ al l) * constantCoeff E else 0 := by
  intro R k _ _ φ d G ι _ _ u lam α al m E hpair hdeg
  obtain ⟨w, hw1, hw2⟩ := exists_word (fun l => Dof (G.mapF φ) (u l)) m (Finset.univ : Finset ι).toList
  have hc : ∀ l, w.count l = m l := fun l => by
    rw [hw1, List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp), one_mul]
  let π : PS k 1 d →ₐ[k] k :=
    { (constantCoeff : PS k 1 d →+* k) with commutes' := fun r => constantCoeff_C r }
  have hπ : ∀ f, π f = constantCoeff f := fun _ => rfl
  have hlen : w.length = ∑ l, m l := by
    rw [← Finset.sum_congr rfl fun l _ => hc l]
    have := Multiset.sum_count_eq_card (s := Finset.univ) (m := (w : Multiset ι)) (by simp)
    simpa using this.symm
  have key := word_value π (fun l => GE.dofD (G.mapF φ) (u l))
    (fun l => ∑ i, C (lam l i) * (X ((0 : Fin 1), i) : PS k 1 d)) (fun l => by simp [hπ]) α w al E
    (fun l l' hl hl' => by
      rw [hπ, GE.dofD_apply, GE.dof_sum, map_sum]
      simp only [GE.dof_C_mul, map_mul, constantCoeff_C, constantCoeff_dof_X]
      exact hpair l l' hl (by rw [← hc]; exact (List.count_pos_iff.2 hl').ne'))
    (by rw [hlen]; simpa [Finsupp.degree_eq_sum] using hdeg)
  simp only [GE.dofD_apply, hπ, hc] at key
  unfold DmonOf
  rw [hw2, key]
  simp only [Finsupp.ext_iff]

end GlobalTheory
