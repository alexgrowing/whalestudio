import Mathlib

open NumberField

namespace GlobalTheory.ModNBasis

variable {O : Type*} [CommRing O] [IsDedekindDomain O]

def primeToSub (n : O) : Submonoid O where
  carrier := {s | IsCoprime s n}
  one_mem' := isCoprime_one_left
  mul_mem' := fun ha hb => IsCoprime.mul_left ha hb

theorem primeToSub_le {n : O} (hn : ¬ IsUnit n) : primeToSub n ≤ nonZeroDivisors O := by
  intro s hs
  apply mem_nonZeroDivisors_of_ne_zero
  rintro rfl
  exact hn (isCoprime_zero_left.mp hs)

theorem primes_finite {n : O} (hn0 : n ≠ 0) :
    {P : Ideal (Localization (primeToSub n)) | P.IsPrime}.Finite := by
  have hfin : {P : Ideal O | P.IsMaximal ∧ n ∈ P}.Finite := by
    have h0 : Ideal.span {n} ≠ 0 := by
      simpa [Ideal.span_singleton_eq_bot] using hn0
    refine ((Ideal.finite_factors h0).image (fun v => v.asIdeal)).subset ?_
    rintro P ⟨hP, hnP⟩
    have hb : P ≠ ⊥ := by
      rintro rfl
      exact hn0 (by simpa using hnP)
    exact ⟨⟨P, hP.isPrime, hb⟩, Ideal.dvd_span_singleton.2 hnP, rfl⟩
  apply ((hfin.insert ⊥).image (Ideal.map (algebraMap O (Localization (primeToSub n))))).subset
  intro P hP
  have hP' : P.IsPrime := hP
  obtain ⟨hQ, hdisj⟩ :=
    (IsLocalization.isPrime_iff_isPrime_disjoint (primeToSub n) _ P).mp hP'
  refine ⟨P.comap (algebraMap O _), ?_, IsLocalization.map_comap (primeToSub n) _ P⟩
  set Q := P.comap (algebraMap O (Localization (primeToSub n)))
  by_cases hb : Q = ⊥
  · exact Or.inl hb
  have hmax : Q.IsMaximal := hQ.isMaximal hb
  right
  refine ⟨hmax, ?_⟩
  by_contra hnQ
  obtain ⟨y, i, hi, hyi⟩ := hmax.exists_inv hnQ
  have hc : i ∈ primeToSub n := show IsCoprime i n from ⟨1, y, by linear_combination hyi⟩
  exact Set.disjoint_left.mp hdisj hc hi

theorem exists_basis_modN {M : Type*} [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {n : O} (hn0 : n ≠ 0) :
    ∃ e : Fin (Module.finrank O M) → M,
      (∀ a : M, ∃ c : Fin (Module.finrank O M) → O, ∃ w : M, a - ∑ i, c i • e i = n • w) ∧
      ∀ c : Fin (Module.finrank O M) → O, (∃ w : M, ∑ i, c i • e i = n • w) → ∀ i, n ∣ c i := by
  classical
  by_cases hu : IsUnit n
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨0, fun a => ⟨0, (↑u⁻¹ : O) • a, ?_⟩, fun c _ i => ⟨↑u⁻¹ * c i, by simp⟩⟩
    simp [smul_smul]
  have hS := primeToSub_le hu
  let Loc := Localization (primeToSub n)
  haveI : IsDomain Loc := IsLocalization.isDomain_localization hS
  haveI : IsDedekindDomain Loc := IsLocalization.isDedekindDomain O hS Loc
  haveI : IsPrincipalIdealRing Loc := IsPrincipalIdealRing.of_finite_primes (primes_finite hn0)
  let f := LocalizedModule.mkLinearMap (primeToSub n) M
  haveI : Module.Finite Loc (LocalizedModule (primeToSub n) M) := inferInstance
  haveI : Module.Free Loc (LocalizedModule (primeToSub n) M) := inferInstance
  let b0 := Module.Free.chooseBasis Loc (LocalizedModule (primeToSub n) M)
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex Loc (LocalizedModule (primeToSub n) M)) =
      Module.finrank O M := by
    rw [← Module.finrank_eq_card_basis b0, IsLocalization.finrank_eq Loc (primeToSub n) hS,
      IsLocalizedModule.finrank_eq (primeToSub n) f hS]

  set ι := Module.Free.ChooseBasisIndex Loc (LocalizedModule (primeToSub n) M)
  have hsurj : ∀ i : ι, ∃ x : M × primeToSub n, x.2 • b0 i = f x.1 :=
    fun i => IsLocalizedModule.surj (primeToSub n) f (b0 i)
  choose x hx using hsurj
  let m : ι → M := fun i => (x i).1
  have hunit : ∀ i, IsUnit (algebraMap O Loc ((x i).2 : O)) :=
    fun i => IsLocalization.map_units Loc (x i).2
  let b := b0.isUnitSMul hunit
  have hb : ∀ i, b i = f (m i) := by
    intro i
    rw [Module.Basis.isUnitSMul_apply, algebraMap_smul, ← hx i, Submonoid.smul_def]

  have hA : ∀ a : M, ∃ c : ι → O, ∃ w : M, a - ∑ i, c i • m i = n • w := by
    intro a
    obtain ⟨T, hT⟩ := IsLocalization.exist_integer_multiples (primeToSub n) (Finset.univ : Finset ι)
      (fun i => b.repr (f a) i)
    choose y hy using fun i => hT i (Finset.mem_univ i)
    have h1 : f ((T : O) • a) = f (∑ i, y i • m i) := by
      rw [map_smul, map_sum, ← b.sum_repr (f a), Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, ← hb i, ← smul_assoc, ← hy i, algebraMap_smul]
    obtain ⟨u, hu⟩ := (IsLocalizedModule.eq_iff_exists (primeToSub n) f).mp h1
    have hcop : IsCoprime ((u : O) * T) n := (u * T).2
    obtain ⟨α, β, hαβ⟩ := hcop
    refine ⟨fun i => α * (u : O) * y i, β • a, ?_⟩
    have h2 : ((u : O) * T) • a = ∑ i, ((u : O) * y i) • m i := by
      rw [mul_smul, ← Submonoid.smul_def, hu, Submonoid.smul_def, Finset.smul_sum]
      simp only [smul_smul]
    calc a - ∑ i, (α * (u : O) * y i) • m i
        = (α * ((u : O) * T) + β * n) • a - α • ∑ i, ((u : O) * y i) • m i := by
          rw [hαβ, one_smul, Finset.smul_sum]; simp only [smul_smul, mul_assoc]
      _ = n • (β • a) := by
          rw [← h2, add_smul, smul_smul, smul_smul, mul_comm β n]; abel

  have hB : ∀ c : ι → O, (∃ w : M, ∑ i, c i • m i = n • w) → ∀ i, n ∣ c i := by
    rintro c ⟨w, hw⟩ i
    have h1 : ∑ j, (algebraMap O Loc (c j) - algebraMap O Loc n * b.repr (f w) j) • b j = 0 := by
      simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, b.sum_repr]
      simp only [algebraMap_smul, hb, ← map_smul, ← map_sum, hw, sub_self]
    have h2 := (Fintype.linearIndependent_iff.mp b.linearIndependent) _ h1 i
    obtain ⟨⟨yy, t⟩, ht⟩ := IsLocalization.surj (primeToSub n) (b.repr (f w) i)
    have h3 : c i * t = n * yy := by
      apply IsLocalization.injective Loc hS
      rw [map_mul, map_mul, ← ht, sub_eq_zero.mp h2, mul_assoc]
    exact (IsCoprime.symm t.2).dvd_of_dvd_mul_right ⟨yy, h3⟩
  let eqv := Fintype.equivFinOfCardEq hcard
  refine ⟨fun j => m (eqv.symm j), fun a => ?_, fun c hc j => ?_⟩
  · obtain ⟨c, w, hw⟩ := hA a
    refine ⟨fun j => c (eqv.symm j), w, ?_⟩
    rw [← hw, Equiv.sum_comp eqv.symm (fun i => c i • m i)]
  · have := hB (fun i => c (eqv i)) ?_ (eqv.symm j)
    · simpa using this
    obtain ⟨w, hw⟩ := hc
    refine ⟨w, ?_⟩
    rw [← hw]
    exact Fintype.sum_equiv eqv _ _ (fun i => by simp)

end GlobalTheory.ModNBasis
