import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SquarefreeRootShift.CountB

open Polynomial

noncomputable section

namespace PI.SqfRootShift.W

open PI.SqfLab

variable {g : ℕ} [Fact g.Prime]

open Classical in

theorem count_good (c : (ZMod g)ˣ) (hg : 3 ≤ g) (k : ℕ) (hk : 1 ≤ k)
    (Q : Finset (ZMod g)[X]) (hQ : ∀ P ∈ Q, Good c P ∧ P.natDegree = k) :
    k * Q.card ≤ ppSum (g ^ k - 1) := by
  set alg := algebraMap (ZMod g) (Fbar g) with halg
  set c' := alg (c : ZMod g) with hc'
  have hc0 : c' ≠ 0 := (_root_.map_ne_zero _).2 c.ne_zero
  set R : (ZMod g)[X] → Finset (Fbar g) := fun P => (P.map alg).roots.toFinset with hRdef
  have hR : ∀ P ∈ Q, (R P).card = k := by
    intro P hP
    obtain ⟨⟨hmon, hirr, -⟩, hdeg⟩ := hQ P hP
    have hsep : (P.map alg).Separable := (PerfectField.separable_of_irreducible hirr).map
    rw [hRdef, Multiset.toFinset_card_of_nodup (nodup_roots hsep),
      IsAlgClosed.card_roots_eq_natDegree, natDegree_map, hdeg]
  have hdisj : (Q : Set (ZMod g)[X]).PairwiseDisjoint R := by
    intro P hP P' hP' hne
    refine Finset.disjoint_left.2 (fun z hz hz' => hne ?_)
    obtain ⟨⟨hmon, hirr, -⟩, -⟩ := hQ P hP
    obtain ⟨⟨hmon', hirr', -⟩, -⟩ := hQ P' hP'
    rw [hRdef, Multiset.mem_toFinset, mem_roots_map hmon.ne_zero] at hz
    rw [hRdef, Multiset.mem_toFinset, mem_roots_map hmon'.ne_zero] at hz'
    rw [minpoly.eq_of_irreducible_of_monic (A := ZMod g) (x := z) hirr
        (by rw [aeval_def]; exact hz) hmon,
      minpoly.eq_of_irreducible_of_monic (A := ZMod g) (x := z) hirr'
        (by rw [aeval_def]; exact hz') hmon']
  have hcard : (Q.biUnion R).card = k * Q.card := by
    rw [Finset.card_biUnion hdisj, Finset.sum_congr rfl hR, Finset.sum_const, smul_eq_mul,
      mul_comm]
  have hgk : g ≤ g ^ k := Nat.le_self_pow (by omega) g
  have hN : 2 ≤ g ^ k - 1 := by omega
  rw [← hcard]
  refine le_trans ?_ (card_ppRoots_le (K := Fbar g) (g ^ k - 1) hN)
  refine Finset.card_le_card_of_injOn (fun z => z * c'⁻¹) ?_ ?_
  · intro z hz
    rw [Finset.mem_coe, Finset.mem_biUnion] at hz
    obtain ⟨P, hP, hzP⟩ := hz
    obtain ⟨hgood, hdeg⟩ := hQ P hP
    rw [hRdef, Multiset.mem_toFinset] at hzP
    have h := good_root c P hgood z hzP
    rw [hdeg] at h
    rw [Finset.mem_coe, Finset.mem_filter, Polynomial.mem_nthRootsFinset (by omega)]
    exact h
  · intro z1 _ z2 _ h
    exact mul_right_cancel₀ (inv_ne_zero hc0) h

theorem monic_ext {h1 h2 : (ZMod g)[X]} {m : ℕ} (hm1 : h1.Monic) (hm2 : h2.Monic)
    (hd1 : h1.natDegree = m) (hd2 : h2.natDegree = m)
    (hc : ∀ i < m, h1.coeff i = h2.coeff i) : h1 = h2 := by
  ext n
  rcases lt_trichotomy n m with hlt | heq | hgt
  · exact hc n hlt
  · have e1 : h1.coeff m = 1 := by rw [← hd1]; exact hm1.coeff_natDegree
    have e2 : h2.coeff m = 1 := by rw [← hd2]; exact hm2.coeff_natDegree
    rw [heq, e1, e2]
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_eq_zero_of_natDegree_lt (by omega)]

theorem divByMonic_facts {r : ℕ} {f P : (ZMod g)[X]} (hf : IsLab g r f) (hP : P.Monic)
    (hdvd : P ∣ f) :
    f = P * (f /ₘ P) ∧ (f /ₘ P).Monic ∧ (f /ₘ P).natDegree = r - P.natDegree := by
  have hmod : f %ₘ P = 0 := (modByMonic_eq_zero_iff_dvd hP).2 hdvd
  have heq : f = P * (f /ₘ P) := by
    have := modByMonic_add_div f P
    rw [hmod, zero_add] at this
    exact this.symm
  refine ⟨heq, ?_, ?_⟩
  · apply hP.of_mul_monic_left
    rw [← heq]; exact hf.1
  · rw [natDegree_divByMonic f hP, hf.2.1]

open Classical in

theorem count_mult (r : ℕ) (T : Finset (ZMod g)[X]) (hT : ∀ f ∈ T, IsLab g r f)
    (P : (ZMod g)[X]) (hP : P.Monic) :
    (T.filter (fun f => P ∣ f)).card ≤ g ^ (r - P.natDegree) := by
  have hu : (Finset.univ : Finset (Fin (r - P.natDegree) → ZMod g)).card =
      g ^ (r - P.natDegree) := by
    simp [ZMod.card]
  rw [← hu]
  refine Finset.card_le_card_of_injOn (fun f (i : Fin (r - P.natDegree)) => (f /ₘ P).coeff i)
    ?_ ?_
  · intro f _; exact Finset.mem_coe.2 (Finset.mem_univ _)
  · intro f1 hf1 f2 hf2 h
    rw [Finset.mem_coe, Finset.mem_filter] at hf1 hf2
    obtain ⟨e1, m1, d1⟩ := divByMonic_facts (hT f1 hf1.1) hP hf1.2
    obtain ⟨e2, m2, d2⟩ := divByMonic_facts (hT f2 hf2.1) hP hf2.2
    have hq : f1 /ₘ P = f2 /ₘ P := monic_ext m1 m2 d1 d2 (fun i hi => congrFun h ⟨i, hi⟩)
    rw [e1, e2, hq]

end PI.SqfRootShift.W
