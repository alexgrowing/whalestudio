import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MonicFactorCoeffNatDegreeLe

open Polynomial

namespace GlobalTheory.FactorCertificate

noncomputable def monicOf {R : Type} [CommRing R] {d m : ℕ} (v : Fin d × Fin (m + 1) → R) :
    R[X][X] :=
  X ^ d + ∑ i : Fin d, C (∑ j : Fin (m + 1), C (v (i, j)) * X ^ (j : ℕ)) * X ^ (i : ℕ)

theorem map_monicOf {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d m : ℕ}
    (v : Fin d × Fin (m + 1) → R) :
    (monicOf v).map (mapRingHom f) = monicOf (fun x => f (v x)) := by
  simp [monicOf, Polynomial.map_sum]

theorem coeff_monicOf {R : Type} [CommRing R] {d m : ℕ} (v : Fin d × Fin (m + 1) → R) :
    (monicOf v).coeff d = 1 := by
  rw [monicOf, coeff_add, coeff_X_pow_self, finsetSum_coeff, Finset.sum_eq_zero, add_zero]
  intro i _
  rw [coeff_C_mul_X_pow, if_neg i.2.ne']

theorem monicOf_coeff {R : Type} [CommRing R] (A : R[X][X]) (hA : A.Monic) {d m : ℕ}
    (hd : A.natDegree = d) (hm : ∀ i, (A.coeff i).natDegree ≤ m) :
    monicOf (fun x : Fin d × Fin (m + 1) => (A.coeff x.1).coeff x.2) = A := by
  subst hd
  conv_rhs => rw [hA.as_sum]
  rw [monicOf, ← Fin.sum_univ_eq_sum_range (fun i => C (A.coeff i) * X ^ i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [Fin.sum_univ_eq_sum_range (fun j => C ((A.coeff i).coeff j) * X ^ j)]
  exact ((A.coeff i).as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le (hm i))).symm

abbrev Unk (a b m : ℕ) : Type := (Fin a × Fin (m + 1)) ⊕ (Fin b × Fin (m + 1))

noncomputable def eqn {R : Type} [CommRing R] (Ψ : R[X][X]) (a b m : ℕ) (p : ℕ × ℕ) :
    MvPolynomial (Unk a b m) R :=
  ((monicOf (fun x => (MvPolynomial.X (Sum.inl x) : MvPolynomial (Unk a b m) R)) *
    monicOf (fun x => (MvPolynomial.X (Sum.inr x) : MvPolynomial (Unk a b m) R)) -
    Ψ.map (mapRingHom MvPolynomial.C)).coeff p.1).coeff p.2

theorem ringHom_eqn {R S : Type} [CommRing R] [CommRing S] (Ψ : R[X][X]) (a b m : ℕ)
    (g : MvPolynomial (Unk a b m) R →+* S) (p : ℕ × ℕ) :
    g (eqn Ψ a b m p) =
      ((monicOf (fun x => g (MvPolynomial.X (Sum.inl x))) *
        monicOf (fun x => g (MvPolynomial.X (Sum.inr x))) -
        Ψ.map (mapRingHom (g.comp MvPolynomial.C))).coeff p.1).coeff p.2 := by
  rw [eqn, ← coeff_map g, ← coe_mapRingHom, ← coeff_map (mapRingHom g), Polynomial.map_sub,
    Polynomial.map_mul, map_monicOf, map_monicOf, Polynomial.map_map, mapRingHom_comp]

theorem map_eqn {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Ψ : R[X][X]) (a b m : ℕ)
    (p : ℕ × ℕ) :
    MvPolynomial.map f (eqn Ψ a b m p) = eqn (Ψ.map (mapRingHom f)) a b m p := by
  rw [ringHom_eqn, eqn, Polynomial.map_map, mapRingHom_comp]
  have : (MvPolynomial.map f : MvPolynomial (Unk a b m) R →+* _).comp MvPolynomial.C =
      MvPolynomial.C.comp f := by
    ext; simp
  simp only [MvPolynomial.map_X, this]

theorem one_mem_span {F : Type} [Field F] [IsAlgClosed F] (Φ : F[X][X]) (hΦ : Irreducible Φ)
    (a b m : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (1 : MvPolynomial (Unk a b m) F) ∈ Ideal.span (Set.range (eqn Φ a b m)) := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ ((Ideal.ne_top_iff_one _).2 h)
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  have h0 : ∀ p, MvPolynomial.eval x (eqn Φ a b m p) = 0 := fun p => by
    have := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).1
      (hle (Ideal.subset_span ⟨p, rfl⟩))
    simpa [MvPolynomial.aeval_eq_eval] using this
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id F := by
    ext; simp
  have hAB : Φ = monicOf (fun y => x (Sum.inl y)) * monicOf (fun y => x (Sum.inr y)) := by
    symm
    rw [← sub_eq_zero]
    ext i j
    have := h0 (i, j)
    rw [ringHom_eqn, hc] at this
    simpa using this
  have key : ∀ {d : ℕ} (v : Fin d × Fin (m + 1) → F), d ≠ 0 → ¬ IsUnit (monicOf v) := by
    intro d v hd hu
    have h1 := natDegree_eq_zero_of_isUnit hu
    have h2 : d ≤ (monicOf v).natDegree :=
      le_natDegree_of_ne_zero (by rw [coeff_monicOf]; exact one_ne_zero)
    omega
  rcases hΦ.isUnit_or_isUnit hAB with hu | hu
  · exact key _ ha hu
  · exact key _ hb hu

theorem descend {F : Type} [CommRing F] (Φ : F[X][X]) (a b m : ℕ)
    (h : (1 : MvPolynomial (Unk a b m) F) ∈ Ideal.span (Set.range (eqn Φ a b m))) :
    ∃ s : Finset F, ∀ R : Subring F, (s : Set F) ⊆ R → ∀ Ψ : R[X][X],
      Ψ.map (mapRingHom R.subtype) = Φ →
      (1 : MvPolynomial (Unk a b m) R) ∈ Ideal.span (Set.range (eqn Ψ a b m)) := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h
  refine ⟨c.support.biUnion fun e => (c e).coeffs, fun R hR Ψ hΨ => ?_⟩
  have hl : ∀ e, ∃ q : MvPolynomial (Unk a b m) R,
      e ∈ c.support → MvPolynomial.map R.subtype q = c e := by
    intro e
    by_cases he : e ∈ c.support
    · have : c e ∈ Set.range (MvPolynomial.map (σ := Unk a b m) R.subtype) := by
        rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
        intro y hy
        exact ⟨⟨y, hR (by
          simp only [Finset.coe_biUnion, Set.mem_iUnion]
          exact ⟨e, he, hy⟩)⟩, rfl⟩
      obtain ⟨q, hq⟩ := this
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose q hq using hl
  have h1 : ∑ e ∈ c.support, q e * eqn Ψ a b m e = 1 := by
    apply MvPolynomial.map_injective R.subtype Subtype.val_injective
    rw [map_sum, map_one, ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [map_mul, hq e he, map_eqn, hΨ, smul_eq_mul]
  rw [← h1]
  exact Ideal.sum_mem _ fun e _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e, rfl⟩)

theorem false_of_one_mem {R k : Type} [CommRing R] [CommRing k] [Nontrivial k] (Ψ : R[X][X])
    (a b m : ℕ)
    (h : (1 : MvPolynomial (Unk a b m) R) ∈ Ideal.span (Set.range (eqn Ψ a b m)))
    (φ : R →+* k) (A B : k[X][X]) (hA : A.Monic) (hB : B.Monic) (ha : A.natDegree = a)
    (hb : B.natDegree = b) (hAm : ∀ i, (A.coeff i).natDegree ≤ m)
    (hBm : ∀ i, (B.coeff i).natDegree ≤ m) (hAB : A * B = Ψ.map (mapRingHom φ)) : False := by
  let x : Unk a b m → k :=
    Sum.elim (fun y => (A.coeff y.1).coeff y.2) (fun y => (B.coeff y.1).coeff y.2)
  let g : MvPolynomial (Unk a b m) R →+* k := MvPolynomial.eval₂Hom φ x
  have hc : g.comp MvPolynomial.C = φ := by
    ext; simp [g]
  have hle : Ideal.span (Set.range (eqn Ψ a b m)) ≤ RingHom.ker g := by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    have e1 : (fun y => g (MvPolynomial.X (Sum.inl y))) =
        fun y : Fin a × Fin (m + 1) => (A.coeff y.1).coeff y.2 := by
      funext y; simp [g, x]
    have e2 : (fun y => g (MvPolynomial.X (Sum.inr y))) =
        fun y : Fin b × Fin (m + 1) => (B.coeff y.1).coeff y.2 := by
      funext y; simp [g, x]
    change g _ = 0
    rw [ringHom_eqn, hc, e1, e2, monicOf_coeff A hA ha hAm, monicOf_coeff B hB hb hBm, hAB,
      sub_self, coeff_zero, coeff_zero]
  have := hle h
  rw [RingHom.mem_ker, map_one] at this
  exact one_ne_zero this

theorem exists_subring_no_monic_factorisation {F : Type} [Field F] [IsAlgClosed F]
    (Φ : Polynomial (Polynomial F)) (hm : Φ.Monic) (hΦ : Irreducible Φ) :
    ∃ s : Finset F, ∃ Ψ : Polynomial (Polynomial (Subring.closure (s : Set F))),
      Ψ.map (Polynomial.mapRingHom (Subring.closure (s : Set F)).subtype) = Φ ∧
      ∀ (k : Type) [Field k] (φ : Subring.closure (s : Set F) →+* k)
        (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
        A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
  classical
  set d := Φ.natDegree with hd
  set D := Φ.support.sup fun i => (Φ.coeff i).natDegree with hD
  have hDle : ∀ i, (Φ.coeff i).natDegree ≤ D := fun i => by
    by_cases hi : i ∈ Φ.support
    · exact Finset.le_sup (f := fun i => (Φ.coeff i).natDegree) hi
    · rw [notMem_support_iff.1 hi]; simp
  have hex : ∀ p : ℕ × ℕ, ∃ s : Finset F, p.1 ≠ 0 → p.2 ≠ 0 → ∀ R : Subring F, (s : Set F) ⊆ R →
      ∀ Ψ : R[X][X], Ψ.map (mapRingHom R.subtype) = Φ →
      (1 : MvPolynomial (Unk p.1 p.2 (d * D)) R) ∈
        Ideal.span (Set.range (eqn Ψ p.1 p.2 (d * D))) := by
    intro p
    by_cases h : p.1 ≠ 0 ∧ p.2 ≠ 0
    · obtain ⟨s, hs⟩ := descend Φ _ _ _ (one_mem_span Φ hΦ p.1 p.2 (d * D) h.1 h.2)
      exact ⟨s, fun _ _ => hs⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose s₀ hs₀ using hex
  let s : Finset F := (Φ.support.biUnion fun i => (Φ.coeff i).coeffs) ∪
    (Finset.range (d + 1) ×ˢ Finset.range (d + 1)).biUnion s₀
  set R := Subring.closure (s : Set F) with hR
  have hinj : Function.Injective (mapRingHom R.subtype) :=
    Polynomial.map_injective _ Subtype.val_injective
  have hlift : Φ ∈ lifts (mapRingHom R.subtype) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have : Φ.coeff i ∈ lifts R.subtype := by
      rw [lifts_iff_coeff_lifts]
      intro j
      by_cases h0 : (Φ.coeff i).coeff j = 0
      · exact ⟨0, by simp [h0]⟩
      · refine ⟨⟨_, Subring.subset_closure ?_⟩, rfl⟩
        have hi : i ∈ Φ.support := mem_support_iff.2 fun h => h0 (by rw [h, coeff_zero])
        exact Finset.mem_coe.2 (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨i, hi, coeff_mem_coeffs h0⟩))
    exact this
  obtain ⟨Ψ, hΨ⟩ := hlift
  replace hΨ : Ψ.map (mapRingHom R.subtype) = Φ := hΨ
  refine ⟨s, Ψ, hΨ, fun k _ φ A B hA hB hAB => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  have hΨm : Ψ.Monic := monic_of_injective hinj (hΨ ▸ hm)
  have hΨd : Ψ.natDegree = d := by
    rw [hd, ← hΨ, natDegree_map_eq_of_injective hinj]
  have hφd : (Ψ.map (mapRingHom φ)).natDegree = d := by
    rw [hΨm.natDegree_map, hΨd]
  have hφD : ∀ i, ((Ψ.map (mapRingHom φ)).coeff i).natDegree ≤ D := fun i => by
    rw [coeff_map, coe_mapRingHom]
    refine natDegree_map_le.trans (le_trans (le_of_eq ?_) (hDle i))
    rw [← hΨ, coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective Subtype.val_injective]
  have hsum : A.natDegree + B.natDegree = d := by
    rw [← hA.natDegree_mul hB, hAB, hφd]
  have hsub : (s₀ (A.natDegree, B.natDegree) : Set F) ⊆ R := fun y hy =>
    Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨_, Finset.mem_product.2
        ⟨Finset.mem_range.2 (by simp only; omega), Finset.mem_range.2 (by simp only; omega)⟩, hy⟩)))
  refine false_of_one_mem Ψ _ _ _ (hs₀ (A.natDegree, B.natDegree) hcon.1 hcon.2 R hsub Ψ hΨ)
    φ A B hA hB rfl rfl ?_ ?_ hAB
  · rw [← hφd]
    exact GlobalTheory.MonicFactorDegree.monic_factor_coeff_natDegree_le _ A B D (hΨm.map _) hA hB
      hAB.symm hφD
  · rw [← hφd]
    exact GlobalTheory.MonicFactorDegree.monic_factor_coeff_natDegree_le _ B A D (hΨm.map _) hB hA
      (by rw [mul_comm, hAB]) hφD

end GlobalTheory.FactorCertificate
