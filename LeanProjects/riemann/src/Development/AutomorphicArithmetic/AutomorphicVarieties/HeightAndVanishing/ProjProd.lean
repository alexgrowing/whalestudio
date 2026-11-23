import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ProjFacts

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

private theorem UpperTheory.V.HV.projProd_ext (N : ℕ) [NeZero N] (a b : (ZMod N)ˣ)
    (h : ∀ r ∈ N.primeFactors, ZMod.unitsMap (Nat.ordProj_dvd N r) a = ZMod.unitsMap (Nat.ordProj_dvd N r) b) :
    a = b := by
  have key : ∀ r ∈ N.primeFactors, (((r ^ N.factorization r : ℕ)) : ℤ) ∣ ((b : ZMod N).val : ℤ) - ((a : ZMod N).val : ℤ) := by
    intro r hr
    have e := congrArg (fun u : (ZMod (r ^ N.factorization r))ˣ => (u : ZMod (r ^ N.factorization r))) (h r hr)
    simp only [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe] at e
    rw [← ZMod.natCast_zmod_val (a : ZMod N), ← ZMod.natCast_zmod_val (b : ZMod N), map_natCast, map_natCast,
      ZMod.natCast_eq_natCast_iff] at e
    exact Nat.modEq_iff_dvd.mp e
  have hcop : (N.primeFactors : Set ℕ).Pairwise (Function.onFun IsCoprime fun r => (((r ^ N.factorization r : ℕ)) : ℤ)) := by
    intro p hp q hq hpq
    simp only [Function.onFun]
    rw [Nat.isCoprime_iff_coprime]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq)
  have hd := Finset.prod_dvd_of_coprime hcop key
  have hN : ∏ r ∈ N.primeFactors, r ^ N.factorization r = N := by
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self (NeZero.ne N)]
    rw [Finsupp.prod, Nat.support_factorization]
  rw [← Nat.cast_prod, hN] at hd
  have e2 : ((a : ZMod N).val : ZMod N) = ((b : ZMod N).val : ZMod N) :=
    (ZMod.natCast_eq_natCast_iff _ _ _).mpr (Nat.modEq_iff_dvd.mpr hd)
  rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at e2
  exact Units.ext e2

theorem UpperTheory.V.HV.projProd :
    ∀ (N : ℕ) [NeZero N] (u : (ZMod N)ˣ), ∏ r ∈ N.primeFactors, proj r N u = u := by
  intro N _ u
  apply projProd_ext
  intro r hr
  have hp := Nat.prime_of_mem_primeFactors hr
  rw [map_prod, Finset.prod_eq_single_of_mem r hr]
  · exact (projFacts N r hp).1 u
  · intro s hs hsr
    have hs' := Nat.prime_of_mem_primeFactors hs
    refine (projFacts N s hs').2.2.2.2.2.2.2.1 _ _ ?_ u
    intro hd
    exact hsr ((Nat.prime_dvd_prime_iff_eq hs' hp).1 (hs'.dvd_of_dvd_pow hd))
