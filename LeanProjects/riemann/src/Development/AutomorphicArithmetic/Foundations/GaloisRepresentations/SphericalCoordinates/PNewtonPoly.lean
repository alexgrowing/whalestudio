import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.RootSumWOff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.PELU Filter Topology
open scoped Matrix
open GlobalTheory.HodgeCoh GlobalTheory.CechDR Polynomial UpperTheory.Gal.W2

private lemma exists_fin_map (n : ℕ) (s : Multiset ℂ) (h : Multiset.card s = n) :
    ∃ r : Fin n → ℂ, (Finset.univ : Finset (Fin n)).val.map r = s := by
  induction n generalizing s with
  | zero =>
    refine ⟨Fin.elim0, ?_⟩
    rw [Multiset.card_eq_zero] at h
    simp [h]
  | succ n ih =>
    obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.1 (by omega : 0 < Multiset.card s)
    obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem ha
    obtain ⟨r, hr⟩ := ih t (by simpa using h)
    refine ⟨Fin.cons a r, ?_⟩
    rw [Fin.univ_val_map, List.ofFn_succ, ← Multiset.cons_coe]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [← Fin.univ_val_map, hr]

private lemma newton_step (n k : ℕ) (r : Fin n → ℂ) :
    (k : ℂ) * ((Finset.univ : Finset (Fin n)).val.map r).esymm k =
      (-1) ^ (k + 1) * ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * ((Finset.univ : Finset (Fin n)).val.map r).esymm a.1 *
          (((Finset.univ : Finset (Fin n)).val.map r).map fun x => x ^ a.2).sum := by
  have h := congrArg (MvPolynomial.aeval (R := ℂ) r) (MvPolynomial.mul_esymm_eq_sum (Fin n) ℂ k)
  simp only [map_mul, map_sum, map_pow, map_neg, map_one, map_natCast,
    MvPolynomial.aeval_esymm_eq_multiset_esymm] at h
  rw [h]
  congr 1
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  simp only [MvPolynomial.psum, map_sum, map_pow, MvPolynomial.aeval_X, Multiset.map_map,
    Function.comp_def]
  rfl

private lemma esymm_descends (F : Type) [Field F] [NumberField F] (n : ℕ)
    (m : (F →+* ℂ) → Multiset ℂ) (hc : ∀ τ, Multiset.card (m τ) = n)
    (hpow : ∀ j : ℕ, ∃ b : F, ∀ τ, ((m τ).map fun r => r ^ j).sum = τ b) (k : ℕ) :
    ∃ b : F, ∀ τ, (m τ).esymm k = τ b := by
  choose p hp using hpow
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact ⟨1, fun τ => by simp [Multiset.esymm]⟩
    choose! e he using ih
    refine ⟨(k : F)⁻¹ * ((-1) ^ (k + 1) *
      ∑ a ∈ (Finset.HasAntidiagonal.antidiagonal k).filter (fun a => a.1 < k),
        (-1) ^ a.1 * e a.1 * p a.2), fun τ => ?_⟩
    obtain ⟨r, hr⟩ := exists_fin_map n (m τ) (hc τ)
    have hs := newton_step n k r
    rw [hr] at hs
    have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [map_mul, map_inv₀, map_natCast, map_pow, map_neg, map_one, map_sum]
    rw [eq_inv_mul_iff_mul_eq₀ hk', hs]
    congr 1
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [he a.1 (Finset.mem_filter.1 ha).2 τ, hp]

theorem UpperTheory.Gal.W2.newtonPoly_of :
    UpperTheory.Gal.W2.NewtonPoly := by
  intro F _ _ n m hc hpow
  choose b hb using esymm_descends F n m hc hpow
  refine ⟨∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j)), ?_⟩
  have hmap : ∀ τ : F →+* ℂ, Polynomial.map τ
      (∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j))) =
      ((m τ).map fun r => X - C r).prod := by
    intro τ
    rw [Multiset.prod_X_sub_X_eq_sum_esymm, hc τ, Polynomial.map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [hb j τ]
  obtain ⟨τ⟩ : Nonempty (F →+* ℂ) := inferInstance
  have hmon : ((m τ).map fun r => X - C r).prod.Monic :=
    Polynomial.monic_multiset_prod_of_monic _ _ fun r _ => Polynomial.monic_X_sub_C r
  refine ⟨?_, ?_, hmap⟩
  · have h1 := Polynomial.leadingCoeff_map_of_injective τ.injective
      (∑ j ∈ Finset.range (n + 1), (-1) ^ j * (C (b j) * X ^ (n - j)))
    rw [hmap τ, hmon.leadingCoeff] at h1
    exact τ.injective (by rw [← h1, map_one])
  · rw [← Polynomial.natDegree_map_eq_of_injective τ.injective, hmap τ,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card, hc τ]
