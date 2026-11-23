import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.WitSys
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.FiniteFreeOfBoundedDenominatorsLattice
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.LatticeSaturatedAtPAndPrimeToP
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDualVectorOfIntegralFunctional
import Development.AutomorphicArithmetic.PAdicLatticeApproximation.ExistsDenominatorOfLattice
open NumberField
open GlobalTheory GlobalTheory.PELU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo UpperTheory.Gal.W2.Wit
open scoped TensorProduct

theorem UpperTheory.exists_prime_to_p_multiple_in_range_of_bilinForm :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (X : UpperTheory.Gal.W2.Wit.Sys D) (E : LinearMap.BilinForm ℤ X.lat), (∀ u w : X.lat, ((E u w : ℤ) : ℚ) = X.s * X.B (u : VQ D) (w : VQ D)) → ∃ e : ℕ, e.Coprime p ∧ ∀ f : X.lat →ₗ[ℤ] ℤ, ∃ x, E x = e • f := by
  classical
  intro p hp D X E hE
  obtain ⟨hfin, hfree⟩ := UpperTheory.finite_free_of_bounded_denominators_lattice p D X (UpperTheory.exists_denominator_of_lattice p D X)
  haveI := hfin
  haveI := hfree
  let b := Module.Free.chooseBasis ℤ X.lat
  have hli : LinearIndependent ℚ (fun i => ((b i : X.lat) : VQ D)) := by
    have h0 : LinearIndependent ℤ (fun i => ((b i : X.lat) : VQ D)) :=
      b.linearIndependent.map' X.lat.toIntSubmodule.subtype (Submodule.ker_subtype _)
    exact (LinearIndependent.iff_fractionRing ℤ ℚ).1 h0
  have hcoe : ∀ u : X.lat, (u : VQ D) = ∑ i, ((b.repr u i : ℤ) : ℚ) • ((b i : X.lat) : VQ D) := by
    intro u
    have h := congrArg X.lat.subtype (b.sum_repr u)
    rw [map_sum] at h
    rw [← show _ = (u : VQ D) from h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, Int.cast_smul_eq_zsmul]
    rfl
  have hsp : ⊤ ≤ Submodule.span ℚ (Set.range (fun i => ((b i : X.lat) : VQ D))) := by
    intro w _
    obtain ⟨m, hm, hmw⟩ := (UpperTheory.lattice_saturated_at_p_and_prime_to_p p D X).2.2 w
    have hmem : ((m : ℚ) • w) ∈ Submodule.span ℚ (Set.range (fun i => ((b i : X.lat) : VQ D))) := by
      have h1 : (m : ℚ) • w = m • w := Nat.cast_smul_eq_nsmul ℚ m w
      rw [h1, show m • w = ((⟨m • w, hmw⟩ : X.lat) : VQ D) from rfl, hcoe ⟨m • w, hmw⟩]
      exact Submodule.sum_mem _ fun i _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
    exact (Submodule.smul_mem_iff _ hm').1 hmem
  let Bq := Module.Basis.mk hli hsp
  have hd : ∀ i j, Bq.coord i ((b j : X.lat) : VQ D) = if j = i then 1 else 0 := by
    intro i j
    have h : ((b j : X.lat) : VQ D) = Bq j := (Module.Basis.mk_apply hli hsp j).symm
    rw [h, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  have hint : ∀ i, ∀ u ∈ X.lat, ∃ z : ℤ, Bq.coord i u = z := by
    intro i u hu
    refine ⟨b.repr ⟨u, hu⟩ i, ?_⟩
    have h := hcoe ⟨u, hu⟩
    change u = _ at h
    calc Bq.coord i u = Bq.coord i (∑ j, ((b.repr ⟨u, hu⟩ j : ℤ) : ℚ) • ((b j : X.lat) : VQ D)) :=
          congrArg _ h
      _ = _ := by
          rw [map_sum]
          simp [hd]
  choose w hwM hw using fun i => UpperTheory.exists_dual_vector_of_integral_functional p D X (Bq.coord i) (hint i)
  choose m hm0 hmc hml using fun i => (UpperTheory.lattice_saturated_at_p_and_prime_to_p p D X).2.1 (w i) (hwM i)
  refine ⟨∏ i, m i, Nat.Coprime.prod_left fun i _ => hmc i, ?_⟩
  intro f
  have ht : ∀ i, ∃ t : X.lat, ∀ j, E t (b j) = if j = i then ((∏ k, m k : ℕ) : ℤ) else 0 := by
    intro i
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m (Finset.mem_univ i)
    have hmem : (∏ k, m k) • w i ∈ X.lat := by
      rw [hc, mul_comm, mul_smul]
      exact nsmul_mem (hml i) c
    refine ⟨⟨_, hmem⟩, fun j => ?_⟩
    have h := hE ⟨_, hmem⟩ (b j)
    have h2 : X.s * X.B ((∏ k, m k) • w i) ((b j : X.lat) : VQ D)
        = ((∏ k, m k : ℕ) : ℚ) * (X.s * X.B (w i) ((b j : X.lat) : VQ D)) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, map_smul, LinearMap.smul_apply, smul_eq_mul]
      ring
    rw [show (((⟨_, hmem⟩ : X.lat)) : VQ D) = (∏ k, m k) • w i from rfl, h2, hw i, hd] at h
    have h3 : ((E ⟨_, hmem⟩ (b j) : ℤ) : ℚ) = (((if j = i then ((∏ k, m k : ℕ) : ℤ) else 0) : ℤ) : ℚ) := by
      rw [h]
      split_ifs <;> simp
    exact_mod_cast h3
  choose t ht using ht
  refine ⟨∑ i, f (b i) • t i, b.ext fun j => ?_⟩
  simp [map_sum, LinearMap.sum_apply, ht, mul_comm]
