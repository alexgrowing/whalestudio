import Formalism.LocalToGlobal.ProjectiveLattices.CrudeBase

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {k : Type} [CommRing k] {d n : ℕ}

theorem div_Lin_add (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f + g) = Lin b v f + Lin b v g := by
  simp only [Lin, map_add, mul_add, Finset.sum_add_distrib]

theorem div_Lin_mul (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f * g) = Lin b v f * g + f * Lin b v g := by
  simp only [Lin, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring

theorem div_Lin_C (b : Fin n) (v : Fin d → k) (c : k) : Lin b v (C c : PS k n d) = 0 := by
  simp [Lin, MvPowerSeries.pderiv_C]

theorem Lin_linForm (b b' : Fin n) (v w : Fin d → k) :
    Lin b v (∑ j : Fin d, C (w j) * (X (b', j) : PS k n d)) =
      C (if b = b' then ∑ j : Fin d, v j * w j else 0) := by
  unfold Lin
  by_cases h : b = b'
  · subst h
    simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Finset.mul_sum,
      map_sum, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Pi.single_apply,
      Prod.ext_iff, h]

theorem div_ordGe_mul {a b : ℕ} {f g : PS k n d} (hf : OrdGe a f) (hg : OrdGe b g) : OrdGe (a + b) (f * g) := by
  intro m hm
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = m := Finset.HasAntidiagonal.mem_antidiagonal.mp hpq
  have hdeg : pq.1.degree + pq.2.degree = m.degree := by
    rw [← hpq']
    first
      | exact (map_add Finsupp.degree pq.1 pq.2).symm
      | exact (Finsupp.degree_add pq.1 pq.2).symm
  by_cases h1 : pq.1.degree < a
  · rw [hf _ h1, zero_mul]
  · rw [hg _ (by omega), mul_zero]

theorem div_ordGe_one : OrdGe 0 (1 : PS k n d) := fun _ hm => absurd hm (Nat.not_lt_zero _)

theorem div_ordGe_pow {a : ℕ} {f : PS k n d} (hf : OrdGe a f) (e : ℕ) : OrdGe (a * e) (f ^ e) := by
  induction e with
  | zero => simpa using div_ordGe_one
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact div_ordGe_mul ih hf

theorem ordGe_aeval_monomial {ι : Type} (φ : ι → PS k n d) (hφ : ∀ i, OrdGe 1 (φ i)) (α : ι →₀ ℕ) :
    OrdGe α.degree (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k))) := by
  classical
  have key : ∀ s : Finset ι, OrdGe (∑ i ∈ s, α i) (∏ i ∈ s, φ i ^ α i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using div_ordGe_one
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi]
      have h := div_ordGe_pow (hφ i) (α i)
      rw [one_mul] at h
      exact div_ordGe_mul h ih
  rw [MvPolynomial.aeval_monomial, map_one, one_mul]
  exact key α.support

theorem div_Lin_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (Q : MvPolynomial ι k) :
    Lin (cp l) (u l) (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ (MvPolynomial.pderiv l Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, MvPowerSeries.algebraMap_apply]
    simpa using div_Lin_C (cp l) (u l) a
  | add p q hp hq => rw [map_add, div_Lin_add, hp, hq, map_add, map_add]
  | mul_X p i hp =>
    rw [map_mul, div_Lin_mul, hp, MvPolynomial.aeval_X, hl, Derivation.leibniz, MvPolynomial.pderiv_X]
    by_cases h : l = i
    · subst h
      simp
      ring
    · simp [h, Pi.single_apply]
      ring

theorem div_Lin_iter_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (t : ℕ) (Q : MvPolynomial ι k) :
    (Lin (cp l) (u l))^[t] (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ ((MvPolynomial.pderiv l)^[t] Q) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, div_Lin_aeval cp u φ l hl]

theorem div_LinMon_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) (Q : MvPolynomial ι k) :
    LinMon cp u a (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ
      ((Finset.univ : Finset ι).toList.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) Q) := by
  unfold LinMon
  generalize (Finset.univ : Finset ι).toList = L
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [ih]
    by_cases h0 : a l = 0
    · rw [h0]
      rfl
    · exact div_Lin_iter_aeval cp u φ l (hdual l (ha l h0)) (a l) _

theorem div_constCoeff_aeval {ι : Type} (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (Q : MvPolynomial ι k) : constantCoeff (MvPolynomial.aeval φ Q) = MvPolynomial.constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPowerSeries.algebraMap_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp, hφ0]

theorem div_iter_pderiv_monomial {ι : Type} [DecidableEq ι] (i : ι) (t : ℕ) (s : ι →₀ ℕ) (c : k) :
    (MvPolynomial.pderiv i)^[t] (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - Finsupp.single i t) (c * ((s i).descFactorial t : k)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : s - Finsupp.single i t - Finsupp.single i 1 = s - Finsupp.single i (t + 1) := by
      ext j
      first
        | (simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp [Finsupp.single_apply]; split_ifs <;> omega)
    have h2 : (s - Finsupp.single i t) i = s i - t := by
      first
        | simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
        | simp
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial, h1, h2,
      Nat.descFactorial_succ]
    congr 1
    push_cast
    ring

theorem div_listSum_apply_of_notMem {ι : Type} (a : ι →₀ ℕ) (L : List ι) (l : ι) (hl : l ∉ L) :
    (L.map fun l' => Finsupp.single l' (a l')).sum l = 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.mem_cons, not_or] at hl
    simp [Finsupp.single_apply, Ne.symm hl.1, ih hl.2]

theorem div_fold_monomial {ι : Type} [DecidableEq ι] (a : ι →₀ ℕ) (L : List ι) (hL : L.Nodup) (s : ι →₀ ℕ)
    (c : k) :
    L.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - (L.map fun l => Finsupp.single l (a l)).sum)
        (c * (L.map fun l => ((s l).descFactorial (a l) : k)).prod) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.foldr_cons, ih hL.2, div_iter_pderiv_monomial]
    have hx : (s - (L.map fun l => Finsupp.single l (a l)).sum) x = s x := by
      rw [Finsupp.tsub_apply, div_listSum_apply_of_notMem a L x hL.1, Nat.sub_zero]
    simp only [List.map_cons, List.sum_cons, List.prod_cons, hx]
    congr 1
    · rw [tsub_tsub, add_comm]
    · ring

theorem linMon_aeval_monomial {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a α : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) :
    constantCoeff (LinMon cp u a (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k)))) =
      if a = α then ((α.prod fun _ e => e.factorial : ℕ) : k) else 0 := by
  classical
  rw [div_LinMon_aeval cp u φ Good hdual a ha, div_fold_monomial a _ (Finset.nodup_toList _),
    div_constCoeff_aeval φ hφ0, MvPolynomial.constantCoeff_monomial]
  have hLs : ∀ (M : Type) [AddCommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).sum = ∑ l, f l := fun M _ f => by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hLp : ∀ (M : Type) [CommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).prod = ∏ l, f l := fun M _ f => by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hS : ((Finset.univ : Finset ι).toList.map fun l => Finsupp.single l (a l)).sum = a := by
    rw [hLs]
    ext j
    simp [Finsupp.finset_sum_apply, Finsupp.single_apply]
  have hP : ((Finset.univ : Finset ι).toList.map fun l => ((α l).descFactorial (a l) : k)).prod =
      ∏ l, ((α l).descFactorial (a l) : k) := hLp k _
  rw [hS, hP, one_mul]
  by_cases hEq : a = α
  · subst hEq
    rw [tsub_self, if_pos rfl, if_pos rfl, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
    push_cast
    exact Finset.prod_congr rfl fun l _ => by rw [Nat.descFactorial_self]
  · rw [if_neg hEq]
    split_ifs with h0
    · have hle : α ≤ a := tsub_eq_zero_iff_le.mp h0
      obtain ⟨l, hl⟩ : ∃ l, α l < a l := by
        by_contra hcon
        push_neg at hcon
        exact hEq (le_antisymm (Finsupp.le_def.mpr hcon) hle)
      exact Finset.prod_eq_zero (Finset.mem_univ l)
        (by rw [Nat.descFactorial_eq_zero_iff_lt.mpr hl, Nat.cast_zero])
    · rfl

end Formalism.L2.Pj.Crude
