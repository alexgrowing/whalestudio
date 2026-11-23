import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.DimFormula

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.compDim :
    ∀ {R : Type} [CommRing R] [IsNoetherianRing R], CohenType R → ∀ (p q : Ideal R) (s : Finset R), p.IsPrime →
      q ∈ (p ⊔ Ideal.span (s : Set R)).minimalPrimes → ringKrullDim (R ⧸ p) ≤ ringKrullDim (R ⧸ q) + s.card := by
  classical
  intro R _ _ hC p q s hp hq
  have hpq : p ≤ q := le_sup_left.trans hq.1.2
  haveI := hp
  haveI := hq.1.1
  obtain ⟨-, hDF⟩ := dimFormula (hC p hp)
  set f := Ideal.Quotient.mk p
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f ≤ q := by rw [Ideal.mk_ker]; exact hpq
  haveI hQ : (q.map f).IsPrime := Ideal.map_isPrime_of_surjective hf hker
  have hmin : q.map f ∈ (Ideal.span ((s.image f : Finset (R ⧸ p)) : Set (R ⧸ p))).minimalPrimes := by
    rw [Finset.coe_image, ← Ideal.map_span, Ideal.minimalPrimes_map_of_surjective hf]
    refine ⟨q, ?_, rfl⟩
    rw [Ideal.mk_ker, sup_comm]
    exact hq
  have hh : (q.map f).height ≤ s.card :=
    (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin).trans
      (by exact_mod_cast Finset.card_image_le)
  have e := hDF (q.map f)
  rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hpq)] at e
  rw [← e, add_comm]
  gcongr
  exact_mod_cast hh
