import Mathlib

namespace KStar.Binom

open IsLocalRing Polynomial

universe u

variable {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}

theorem adjoinRoot_unramified (hϖ : Irreducible ϖ) {f : O[X]} (hf : f.Monic)
    (hirr : Irreducible (f.map (residue O))) :
    ∃ (_ : IsDomain (AdjoinRoot f)) (_ : IsDiscreteValuationRing (AdjoinRoot f)),
      Irreducible (algebraMap O (AdjoinRoot f) ϖ) ∧
        Nat.card (ResidueField (AdjoinRoot f)) = Nat.card (ResidueField O) ^ f.natDegree := by
  classical
  have : Fact (Irreducible (f.map (residue O))) := ⟨hirr⟩
  have hfirr : Irreducible f := Monic.irreducible_of_irreducible_map (residue O) f hf hirr
  have hdom : IsDomain (AdjoinRoot f) := AdjoinRoot.isDomain_of_prime hfirr.prime
  have hfin : Module.Finite O (AdjoinRoot f) := hf.finite_adjoinRoot
  have hfree : Module.Free O (AdjoinRoot f) := hf.free_adjoinRoot
  have : IsNoetherianRing (AdjoinRoot f) := IsNoetherianRing.of_finite O _
  let J : Ideal (AdjoinRoot f) := Ideal.map (AdjoinRoot.of f) (maximalIdeal O)
  let e : (AdjoinRoot f ⧸ J) ≃+* AdjoinRoot (f.map (residue O)) :=
    AdjoinRoot.quotAdjoinRootEquivQuotPolynomialQuot (maximalIdeal O) f
  have hJ : J.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (e.toMulEquiv.isField (Field.toIsField _))
  have huniq : ∀ M : Ideal (AdjoinRoot f), M.IsMaximal → M = J := by
    intro M hM
    have h1 := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := O) M
    have h2 : J ≤ M := by
      rw [Ideal.map_le_iff_le_comap, ← AdjoinRoot.algebraMap_eq, eq_maximalIdeal h1]
    exact (hJ.eq_of_le hM.ne_top h2).symm
  have : IsLocalRing (AdjoinRoot f) := IsLocalRing.of_unique_max_ideal ⟨J, hJ, huniq⟩
  have hmJ : maximalIdeal (AdjoinRoot f) = J := (eq_maximalIdeal hJ).symm
  have hm : maximalIdeal (AdjoinRoot f) = Ideal.span {algebraMap O (AdjoinRoot f) ϖ} := by
    rw [hmJ]
    simp only [J, hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton,
      AdjoinRoot.algebraMap_eq]
  have hne : algebraMap O (AdjoinRoot f) ϖ ≠ 0 := by
    intro h
    exact hϖ.ne_zero (FaithfulSMul.algebraMap_injective O (AdjoinRoot f) (by simpa using h))
  have hnf : ¬ IsField (AdjoinRoot f) := by
    rw [isField_iff_maximalIdeal_eq, hm, Ideal.span_singleton_eq_bot]
    exact hne
  have hdvr : IsDiscreteValuationRing (AdjoinRoot f) :=
    ((IsDiscreteValuationRing.TFAE (AdjoinRoot f) hnf).out 0 4).mpr
      (show (maximalIdeal (AdjoinRoot f)).IsPrincipal from ⟨_, hm⟩)
  refine ⟨hdom, hdvr, IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal _ hne hm, ?_⟩
  have e2 : ResidueField (AdjoinRoot f) ≃+* AdjoinRoot (f.map (residue O)) :=
    (Ideal.quotEquivOfEq hmJ).trans e
  have : Module.Finite (ResidueField O) (AdjoinRoot (f.map (residue O))) :=
    (hf.map _).finite_adjoinRoot
  rw [Nat.card_congr e2.toEquiv, Module.natCard_eq_pow_finrank (K := ResidueField O),
    (AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hf.natDegree_map]

end KStar.Binom
