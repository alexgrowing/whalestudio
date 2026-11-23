import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Cohen
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CompDim

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

private theorem dim_le_nil {R : Type} [CommRing R] :
    ringKrullDim R ≤ ringKrullDim (R ⧸ nilradical R) := by
  rw [ringKrullDim_quotient]
  have h : PrimeSpectrum.zeroLocus (nilradical R : Set R) = Set.univ := by
    ext p
    simp only [Set.mem_univ, iff_true, PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact nilradical_le_prime p.asIdeal
  rw [h]
  exact le_of_eq (Order.krullDim_eq_of_orderIso OrderIso.Set.univ).symm

theorem UpperTheory.V.AlgebraTools.Conn.clComp :
    ∀ {O R : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
      [CommRing R] [IsLocalRing R] [Algebra O R] [IrreducibleSpace (PrimeSpectrum R)], UpperTheory.V.CA.IsCL O R → ∀ (a q : Ideal R) (h : ℕ),
      ReciprocityTheory.CA.AraLE a h → q ∈ a.minimalPrimes → ringKrullDim R ≤ ringKrullDim (R ⧸ q) + h := by
  intro O R _ _ _ _ _ _ _ _ hR a q h ha hq
  haveI := hR.noeth
  obtain ⟨s, hs, hrad⟩ := ha
  have hnil : (nilradical R).IsPrime := by
    have hirr : IsIrreducible (PrimeSpectrum.zeroLocus ((⊥ : Ideal R) : Set R)) := by
      rw [Submodule.bot_coe, PrimeSpectrum.zeroLocus_singleton_zero]
      exact IrreducibleSpace.isIrreducible_univ _
    exact (PrimeSpectrum.isIrreducible_zeroLocus_iff ⊥).mp hirr
  have hsup : (nilradical R ⊔ Ideal.span (s : Set R)).radical = a.radical := by
    rw [Ideal.radical_sup, nilradical, Ideal.radical_idem, ← Ideal.radical_sup, Submodule.zero_eq_bot,
      bot_sup_eq, hrad]
  have hq' : q ∈ (nilradical R ⊔ Ideal.span (s : Set R)).minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hsup, Ideal.radical_minimalPrimes]
    exact hq
  calc ringKrullDim R ≤ ringKrullDim (R ⧸ nilradical R) := dim_le_nil
    _ ≤ ringKrullDim (R ⧸ q) + s.card := compDim (cohen hR) _ q s hnil hq'
    _ ≤ ringKrullDim (R ⧸ q) + h := by
      gcongr
