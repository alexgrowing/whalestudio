import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TchPoly
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem hos_expand {O S σ : Type} [CommRing O] [CommRing S] [Algebra O S] [Finite σ]
    (N : ℕ) (D : Finset (σ →₀ ℕ)) (hD : ∀ d, d ∈ D ↔ d.degree < N)
    (g : MvPowerSeries σ O →ₐ[O] S) (J : Ideal S) (hg : ∀ s, g (MvPowerSeries.X s) ∈ J) (hJ : J ^ N = ⊥)
    (y : MvPowerSeries σ O) :
    g y = ∑ d ∈ D, algebraMap O S (coeff d y) * d.prod fun s k => g (MvPowerSeries.X s) ^ k := by
  classical
  have h1 := GlobalTheory.algHom_sub_aeval_truncTotal_mem g hg N y
  rw [hJ, Ideal.mem_bot, sub_eq_zero] at h1
  rw [h1]
  have ht : truncTotal N y = ∑ d ∈ D, MvPolynomial.monomial d (coeff d y) := by
    ext d
    rw [MvPolynomial.coeff_sum, coeff_truncTotal_eq_ite]
    simp only [MvPolynomial.coeff_monomial, Finset.sum_ite_eq', hD]
  rw [ht, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [MvPolynomial.aeval_monomial]

private theorem hos_prod {S σ X : Type} [CommRing S] [AddCommGroup X] (wt : σ → X)
    (t : Multiplicative X →* Sˣ) (a : σ → S) (d : σ →₀ ℕ) :
    (d.prod fun s k => ((t (Multiplicative.ofAdd (wt s)) : S) * a s) ^ k) =
      t (Multiplicative.ofAdd (Finsupp.weight wt d)) * d.prod fun s k => a s ^ k := by
  classical
  unfold Finsupp.prod
  simp only [mul_pow, Finset.prod_mul_distrib]
  congr 1
  rw [Finsupp.weight_apply, Finsupp.sum, ofAdd_sum, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun s _ => ?_
  rw [ofAdd_nsmul, map_pow, Units.val_pow_eq_pow_val]

private theorem hos_art {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {S : Type} [CommRing S] [Algebra O S] [IsCO O S] {σ : Type} [Finite σ] (wt : σ → X)
    (p : MvPowerSeries σ O →ₐ[O] S) (N : ℕ) (hJ : maximalIdeal S ^ N = ⊥)
    (hp : ∀ s, p (MvPowerSeries.X s) ∈ maximalIdeal S) (x : MvPowerSeries σ O)
    (H : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (i : S →ₐ[O] R')
      (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) →
      ∀ f' : MvPowerSeries σ O →ₐ[O] R',
        (∀ s, f' (MvPowerSeries.X s) = t (Multiplicative.ofAdd (wt s)) * i (p (MvPowerSeries.X s))) → f' x = 0)
    (j : X) : p (wcomp O wt j x) = 0 := by
  classical
  obtain ⟨n, t, ht1, ht2⟩ := tchar O X
  haveI : IsCO O (MvPowerSeries (Fin n) S) := co_mvps O S (Fin n)
  let i : S →ₐ[O] MvPowerSeries (Fin n) S := IsScalarTower.toAlgHom O S (MvPowerSeries (Fin n) S)
  have hi : ∀ a, i a = MvPowerSeries.C a := fun a => rfl
  let t' : Multiplicative X →* (MvPowerSeries (Fin n) S)ˣ :=
    (Units.map (MvPowerSeries.map (algebraMap O S)).toMonoidHom).comp t
  have ht' : ∀ k, res O (MvPowerSeries (Fin n) S) (t' k) = 1 := by
    intro k
    rw [← sub_eq_zero, ← map_one (res O (MvPowerSeries (Fin n) S)), ← map_sub, res_eq_zero_iff,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    have hc : constantCoeff ((t' k : MvPowerSeries (Fin n) S) - 1) = 0 := by
      show constantCoeff (MvPowerSeries.map (algebraMap O S) (t k : MvPowerSeries (Fin n) O) - 1) = 0
      rw [map_sub, MvPowerSeries.constantCoeff_map, ht1, map_one, map_one, sub_self]
    rw [hc]
    exact not_isUnit_zero
  have hJm : Ideal.map i (maximalIdeal S) ≤ maximalIdeal (MvPowerSeries (Fin n) S) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    show i a ∈ maximalIdeal _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff, hi,
      MvPowerSeries.constantCoeff_C]
    exact (IsLocalRing.mem_maximalIdeal _).1 ha
  let e : σ → MvPowerSeries (Fin n) S := fun s =>
    (t' (Multiplicative.ofAdd (wt s)) : MvPowerSeries (Fin n) S) * i (p (MvPowerSeries.X s))
  have he : ∀ s, e s ∈ Ideal.map i (maximalIdeal S) := fun s =>
    Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hp s))
  haveI : IsAdicComplete (maximalIdeal (MvPowerSeries (Fin n) S)) (MvPowerSeries (Fin n) S) :=
    IsCO.complete (O := O)
  let f' := GlobalTheory.mvEvalAdic O (maximalIdeal (MvPowerSeries (Fin n) S)) e (fun s => hJm (he s))
  have hf'X : ∀ s, f' (MvPowerSeries.X s) =
      t' (Multiplicative.ofAdd (wt s)) * i (p (MvPowerSeries.X s)) := fun s =>
    GlobalTheory.mvEvalAdic_X _ _ _ s
  have h0 : f' x = 0 := H _ i t' ht' f' hf'X
  have hJN : Ideal.map i (maximalIdeal S) ^ N = ⊥ := by
    rw [← Ideal.map_pow, hJ, Ideal.map_bot]
  have hf'J : ∀ s, f' (MvPowerSeries.X s) ∈ Ideal.map i (maximalIdeal S) := fun s => by
    rw [hf'X]
    exact he s
  let D : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_lt N).toFinset
  have hD : ∀ d, d ∈ D ↔ d.degree < N := fun d => by simp [D]
  have E1 := hos_expand N D hD f' (Ideal.map i (maximalIdeal S)) hf'J hJN x
  let T : (σ →₀ ℕ) → S := fun d =>
    algebraMap O S (coeff d x) * d.prod fun s k => p (MvPowerSeries.X s) ^ k
  have hT : ∀ k, p (wcomp O wt k x) = ∑ d ∈ D, if Finsupp.weight wt d = k then T d else 0 := by
    intro k
    rw [hos_expand N D hD p (maximalIdeal S) hp hJ]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [coeff_wcomp]
    split_ifs <;> simp [T]
  have hE : f' x = ∑ d ∈ D,
      (t' (Multiplicative.ofAdd (Finsupp.weight wt d)) : MvPowerSeries (Fin n) S) * i (T d) := by
    rw [E1]
    refine Finset.sum_congr rfl fun d _ => ?_
    simp only [hf'X]
    have hp' := hos_prod wt t' (fun s => i (p (MvPowerSeries.X s))) d
    beta_reduce at hp'
    rw [hp']
    simp only [T, map_mul, AlgHom.commutes, Finsupp.prod, map_prod, map_pow]
    ring
  let s : Finset X := D.image (Finsupp.weight wt)
  have hz : ∀ k ∈ s, p (wcomp O wt k x) = 0 := by
    refine ht2 S s (fun k => p (wcomp O wt k x)) ?_
    calc _ = ∑ k ∈ s, (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) *
          i (p (wcomp O wt k x)) := Finset.sum_congr rfl fun k _ => by rw [hi]; rfl
      _ = ∑ k ∈ s, ∑ d ∈ D, if Finsupp.weight wt d = k then
          (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) * i (T d) else 0 := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hT, map_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun d _ => ?_
          split_ifs <;> simp
      _ = ∑ d ∈ D, ∑ k ∈ s, if Finsupp.weight wt d = k then
          (t' (Multiplicative.ofAdd k) : MvPowerSeries (Fin n) S) * i (T d) else 0 :=
          Finset.sum_comm
      _ = f' x := by
          rw [hE]
          refine Finset.sum_congr rfl fun d hd => ?_
          rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ hd)]
      _ = 0 := h0
  by_cases hj : j ∈ s
  · exact hz j hj
  · rw [hT]
    apply Finset.sum_eq_zero
    intro d hd
    rw [if_neg]
    intro h
    exact hj (h ▸ Finset.mem_image_of_mem _ hd)

theorem UpperTheory.V.Alg.homog_of_stable :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (σ : Type) [Finite σ] (wt : σ → X) (π : MvPowerSeries σ O →ₐ[O] R), (∀ s, π (MvPowerSeries.X s) ∈ maximalIdeal R) →
      (∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : MvPowerSeries σ O →ₐ[O] R') (t : Multiplicative X →* R'ˣ), (∀ j, res O R' (t j) = 1) → (∀ x, π x = 0 → f x = 0) →
        ∀ f' : MvPowerSeries σ O →ₐ[O] R', (∀ s, f' (MvPowerSeries.X s) = t (Multiplicative.ofAdd (wt s)) * f (MvPowerSeries.X s)) → ∀ x, π x = 0 → f' x = 0) →
      IsHomog O wt (RingHom.ker π) := by
  intro O _ _ _ _ X _ _ _ R _ _ _ σ _ wt π hπ hstab
  intro x hx j
  have hx' : π x = 0 := hx
  show π (wcomp O wt j x) = 0
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  apply GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal R)
  intro N
  rw [sub_zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ N) ?_
  obtain ⟨I, hI⟩ : ∃ I : Ideal R, I = maximalIdeal R ^ (N + 1) := ⟨_, rfl⟩
  rw [← hI]
  have hIm : I ≤ maximalIdeal R := hI ▸ Ideal.pow_le_self (Nat.succ_ne_zero N)
  have hItop : I ≠ ⊤ := fun h =>
    (maximalIdeal.isMaximal R).ne_top (top_le_iff.1 (h ▸ hIm))
  haveI : Nontrivial (R ⧸ I) := by
    refine ⟨⟨0, 1, fun h => hItop ((Ideal.eq_top_iff_one _).2 ?_)⟩⟩
    rw [← map_one (Ideal.Quotient.mk I)] at h
    exact Ideal.Quotient.eq_zero_iff_mem.1 h.symm
  let q : R →ₐ[O] R ⧸ I := Ideal.Quotient.mkₐ O I
  haveI : IsCO O (R ⧸ I) := co_quot O R (R ⧸ I) q (Ideal.Quotient.mkₐ_surjective O I)
  have hmap : ∀ r ∈ maximalIdeal R, q r ∈ maximalIdeal (R ⧸ I) := by
    intro r hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rintro ⟨u, hu⟩
    obtain ⟨v, hv⟩ := Ideal.Quotient.mk_surjective ((u⁻¹ : (R ⧸ I)ˣ) : R ⧸ I)
    have hrv : r * v - 1 ∈ I := by
      rw [← Ideal.Quotient.eq, map_mul, hv, map_one]
      show q r * _ = 1
      rw [← hu, Units.mul_inv]
    apply (maximalIdeal.isMaximal R).ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 := Ideal.sub_mem _ (Ideal.mul_mem_right v _ hr) (hIm hrv)
    simpa using h1
  have hle : maximalIdeal (R ⧸ I) ≤ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) := by
    intro y hy
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.mem_map_of_mem
    by_contra hr
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at hr
    exact (IsLocalRing.mem_maximalIdeal _).1 hy (hr.map _)
  have hJ : maximalIdeal (R ⧸ I) ^ (N + 1) = ⊥ := by
    rw [eq_bot_iff]
    calc maximalIdeal (R ⧸ I) ^ (N + 1)
        ≤ Ideal.map (Ideal.Quotient.mk I) (maximalIdeal R) ^ (N + 1) := Ideal.pow_right_mono hle _
      _ = Ideal.map (Ideal.Quotient.mk I) I := by rw [← Ideal.map_pow, hI]
      _ = ⊥ := Ideal.map_quotient_self I
      _ ≤ ⊥ := le_rfl
  have hp : ∀ s, (q.comp π) (MvPowerSeries.X s) ∈ maximalIdeal (R ⧸ I) := fun s =>
    hmap _ (hπ s)
  have key := hos_art wt (q.comp π) (N + 1) hJ hp x
    (fun R' _ _ _ i t ht f' hf' =>
      hstab R' ((i.comp q).comp π) t ht (fun y hy => by simp [hy]) f' (fun s => (hf' s).trans rfl) x hx') j
  rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem] at key
  exact key
