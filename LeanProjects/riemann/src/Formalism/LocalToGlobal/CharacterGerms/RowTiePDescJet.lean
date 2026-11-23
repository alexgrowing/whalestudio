import Formalism.LocalToGlobal.CharacterGerms.RowTieDesc

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.DescP

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

section Jet

variable {k : Type} [CommRing k] {n d : ℕ}

def HiOrd (K : ℕ) (g : PS k n d) : Prop :=
  ∀ μ : Fin n × Fin d →₀ ℕ, μ.degree < K → coeff μ g = 0

theorem HiOrd.mono {K K' : ℕ} {g : PS k n d} (h : HiOrd K' g) (hK : K ≤ K') : HiOrd K g := fun μ hμ => h μ (lt_of_lt_of_le hμ hK)

theorem HiOrd.mul_left {K : ℕ} {g : PS k n d} (h : HiOrd K g) (a : PS k n d) : HiOrd K (a * g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun pq hpq => ?_
  have hpq' : pq.1 + pq.2 = μ := Finset.HasAntidiagonal.mem_antidiagonal.1 hpq
  have h2 : Finsupp.degree pq.2 < K :=
    lt_of_le_of_lt (by rw [← hpq', map_add]; exact Nat.le_add_left _ _) hμ
  rw [h _ h2, mul_zero]

theorem HiOrd.sum {K : ℕ} {α : Type} (s : Finset α) (g : α → PS k n d) (h : ∀ i ∈ s, HiOrd K (g i)) :
    HiOrd K (∑ i ∈ s, g i) := by
  intro μ hμ
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => h i hi μ hμ

theorem HiOrd.deriv {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (i : Fin n × Fin d) :
    HiOrd K (MvPowerSeries.pderiv k i g) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_pderiv, h _ (by rw [map_add, Finsupp.degree_single]; omega), zero_mul]

theorem HiOrd.dofN {K : ℕ} {g : PS k n d} (h : HiOrd (K + 1) g) (F : Fin d → PS k 2 d) (b : Fin n)
    (u : Fin d → k) : HiOrd K (DofN F b u g) := by
  unfold DofN
  exact HiOrd.sum _ _ fun j _ => (h.deriv _).mul_left _

theorem HiOrd.iter (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) :
    ∀ (j K : ℕ) (g : PS k n d), HiOrd (K + j) g → HiOrd K ((DofN F b u)^[j] g)
  | 0, K, g, h => h
  | j + 1, K, g, h => by
    rw [Function.iterate_succ_apply]
    exact HiOrd.iter F b u j K _ (HiOrd.dofN (K := K + j) (by rw [add_assoc]; exact h) F b u)

theorem HiOrd.foldr (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (K : ℕ) (g : PS k n d), HiOrd (K + (L.map m).sum) g →
      HiOrd K (L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g)
  | [], K, g, h => by simpa using h
  | l :: L, K, g, h => by
    rw [List.foldr_cons]
    refine HiOrd.iter F (cp l) (u l) (m l) K _ (HiOrd.foldr F cp u m L (K + m l) g ?_)
    rw [List.map_cons, List.sum_cons] at h
    rw [add_assoc]
    exact h

theorem HiOrd.dmonN (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (m : ι →₀ ℕ) {K : ℕ} {g : PS k n d} (h : HiOrd (K + m.degree) g) : HiOrd K (DmonN F cp u m g) := by
  unfold DmonN
  refine HiOrd.foldr F cp u m _ K g ?_
  rw [Finset.sum_map_toList, ← Finsupp.degree_eq_sum]
  exact h

theorem const_dpolyN_eq_zero (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) {g : PS k n d} (h : HiOrd (P.totalDegree + 1) g) :
    constantCoeff (DpolyN F cp u P g) = 0 := by
  unfold DpolyN
  rw [map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hd : Finsupp.degree m ≤ P.totalDegree := by
    have h1 := MvPolynomial.le_totalDegree hm
    rw [Finsupp.degree_apply]
    exact h1
  have h1 : HiOrd 1 (DmonN F cp u m g) := HiOrd.dmonN F cp u m (h.mono (by omega))
  rw [map_mul, ← coeff_zero_eq_constantCoeff_apply (DmonN F cp u m g), h1 0 (by simp), mul_zero]

theorem dofN_add (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (f g : PS k n d) :
    DofN F b u (f + g) = DofN F b u f + DofN F b u g := by
  simp only [DofN, map_add, mul_add, Finset.sum_add_distrib]

theorem dofN_smul (F : Fin d → PS k 2 d) (b : Fin n) (u : Fin d → k) (c : k) (f : PS k n d) :
    DofN F b u (c • f) = c • DofN F b u f := by
  simp only [DofN, Derivation.map_smul, Finset.smul_sum, mul_smul_comm]

theorem iter_add (A : PS k n d → PS k n d) (hA : ∀ f g, A (f + g) = A f + A g) :
    ∀ (j : ℕ) (f g : PS k n d), A^[j] (f + g) = A^[j] f + A^[j] g
  | 0, f, g => rfl
  | j + 1, f, g => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, hA,
      iter_add A hA j]

theorem iter_smul (A : PS k n d → PS k n d) (hA : ∀ (c : k) f, A (c • f) = c • A f) :
    ∀ (j : ℕ) (c : k) (f : PS k n d), A^[j] (c • f) = c • A^[j] f
  | 0, c, f => rfl
  | j + 1, c, f => by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hA, iter_smul A hA j]

theorem foldr_add (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (f g : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (f + g) =
        L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f + L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) g
  | [], f, g => rfl
  | l :: L, f, g => by
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, foldr_add F cp u m L f g,
      iter_add _ (dofN_add F (cp l) (u l))]

theorem foldr_smul (F : Fin d → PS k 2 d) {ι : Type} (cp : ι → Fin n) (u : ι → Fin d → k) (m : ι →₀ ℕ) :
    ∀ (L : List ι) (c : k) (f : PS k n d),
      L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) (c • f) =
        c • L.foldr (fun l g => (DofN F (cp l) (u l))^[m l] g) f
  | [], c, f => rfl
  | l :: L, c, f => by
    rw [List.foldr_cons, List.foldr_cons, foldr_smul F cp u m L c f,
      iter_smul _ (dofN_smul F (cp l) (u l))]

theorem dpolyN_add (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (f g : PS k n d) :
    DpolyN F cp u P (f + g) = DpolyN F cp u P f + DpolyN F cp u P g := by
  simp only [DpolyN, DmonN, foldr_add, mul_add, Finset.sum_add_distrib]

theorem dpolyN_smul (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (c : k) (f : PS k n d) :
    DpolyN F cp u P (c • f) = c • DpolyN F cp u P f := by
  simp only [DpolyN, DmonN, foldr_smul, mul_smul_comm, Finset.smul_sum]

def nabL (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) : PS k n d →ₗ[k] k where
  toFun f := constantCoeff (DpolyN F cp u P (f * G))
  map_add' f g := by
    rw [add_mul, dpolyN_add, map_add]
  map_smul' c f := by
    rw [smul_mul_assoc, dpolyN_smul, ← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
      map_smul]
    rfl

def cst (D : ℕ) : Fin n × Fin d →₀ ℕ := Finsupp.equivFunOnFinite.symm fun _ => D

theorem hiOrd_sub_trunc (f : PS k n d) (D : ℕ) :
    HiOrd (D + 1) (f - ((trunc' k (cst D) f : MvPolynomial _ k) : PS k n d)) := by
  intro μ hμ
  rw [map_sub, MvPolynomial.coeff_coe, MvPowerSeries.coeff_trunc', if_pos, sub_self]
  intro i
  have h1 : μ i ≤ Finsupp.degree μ := Finsupp.le_degree i μ
  simp [cst]
  omega

theorem coe_eq_sum (p : MvPolynomial (Fin n × Fin d) k) :
    (p : PS k n d) = ∑ μ ∈ p.support, MvPolynomial.coeff μ p • monomial μ (1 : k) := by
  ext ν
  rw [MvPolynomial.coeff_coe, map_sum]
  simp only [map_smul, MvPowerSeries.coeff_monomial, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · simpa using h

theorem nabL_trunc (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (G : PS k n d) (f : PS k n d) :
    nabL F cp u P G f = ∑ μ ∈ (trunc' k (cst P.totalDegree) f).support,
      MvPolynomial.coeff μ (trunc' k (cst P.totalDegree) f) * nabL F cp u P G (monomial μ (1 : k)) := by
  set T : PS k n d := ((trunc' k (cst P.totalDegree) f : MvPolynomial _ k) : PS k n d) with hTdef
  have h0 : nabL F cp u P G (f - T) = 0 := by
    show constantCoeff (DpolyN F cp u P ((f - T) * G)) = 0
    rw [mul_comm]
    exact const_dpolyN_eq_zero F cp u P ((hiOrd_sub_trunc f P.totalDegree).mul_left G)
  have hsplit : nabL F cp u P G f = nabL F cp u P G (f - T) + nabL F cp u P G T := by
    rw [← map_add, sub_add_cancel]
  rw [hsplit, h0, zero_add, hTdef, coe_eq_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

theorem dpolyN_sub (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (P : MvPolynomial ι k) (g : PS k n d) (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    DpolyN F cp u P g = ∑ m ∈ S, MvPowerSeries.C (P.coeff m) * DmonN F cp u m g := by
  unfold DpolyN
  refine Finset.sum_subset hS fun m _ hm => ?_
  rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, zero_mul]

theorem const_dpolyN_lin (F : Fin d → PS k 2 d) {ι : Type} [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    {α : Type} (s : Finset α) (c : α → k) (Q : α → MvPolynomial ι k) (g : PS k n d) :
    constantCoeff (DpolyN F cp u (∑ i ∈ s, c i • Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) := by
  set S := (∑ i ∈ s, c i • Q i).support ∪ s.biUnion (fun i => (Q i).support) with hS
  rw [dpolyN_sub F cp u _ g S Finset.subset_union_left]
  have hQ : ∀ i ∈ s, DpolyN F cp u (Q i) g = ∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g :=
    fun i hi => dpolyN_sub F cp u _ g S
      (fun m hm => Finset.mem_union_right _ (Finset.mem_biUnion.2 ⟨i, hi, hm⟩))
  have hR : ∑ i ∈ s, c i * constantCoeff (DpolyN F cp u (Q i) g) =
      ∑ i ∈ s, c i * constantCoeff (∑ m ∈ S, MvPowerSeries.C ((Q i).coeff m) * DmonN F cp u m g) :=
    Finset.sum_congr rfl fun i hi => by rw [hQ i hi]
  rw [hR]
  simp only [map_sum, map_mul, MvPowerSeries.constantCoeff_C, MvPolynomial.coeff_sum,
    MvPolynomial.coeff_smul, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun m _ => by ring

end Jet

theorem exists_fin_sum {α M : Type} [AddCommMonoid M] (s : Finset α) (g : α → M) :
    ∃ (N : ℕ) (e : Fin N → α), (∀ j, e j ∈ s) ∧ ∑ x ∈ s, g x = ∑ j, g (e j) := ⟨s.card, fun j => (s.equivFin.symm j : α), fun j => (s.equivFin.symm j).2, by
    rw [← Finset.sum_coe_sort s, ← Equiv.sum_comp s.equivFin.symm]⟩

end Formalism.L2.FormalSeriesBounds.DescP
