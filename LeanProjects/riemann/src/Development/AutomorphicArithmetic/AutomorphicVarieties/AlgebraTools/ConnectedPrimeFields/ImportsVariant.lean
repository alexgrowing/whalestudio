import Mathlib
import ReciprocityTheory.CommutativeAlgebra.ChainConnInDim
import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.IsWeaklyRegularPairModOneLeft
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CutDimCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.Adjoin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ConnectedPrimeFields.CplFinite

open IsLocalRing UpperTheory.V.AlgebraTools.Conn

theorem UpperTheory.V.AlgebraTools.Conn.one :
    ∀ {R : Type} [CommRing R] [IsLocalRing R] [IsDomain R], HasBase R → ∀ (f : R) (b c : Ideal R), f ∈ maximalIdeal R →
      (b ⊓ c).radical = (Ideal.span {f}).radical → b ≠ ⊤ → c ≠ ⊤ →
      ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ b) → ringKrullDim (R ⧸ (b ⊔ c)) < ringKrullDim (R ⧸ c) →
      ringKrullDim R ≤ ringKrullDim (R ⧸ (b ⊔ c)) + 2 := by
  intro R _ _ _ hB f b c hf hrad hb hc hdb hdc
  obtain ⟨A, _, _, i, hA, hinj, hfin⟩ := hB
  letI : Algebra A R := i.toAlgebra
  haveI : Module.Finite A R := hfin
  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective A R).mpr hinj
  haveI : IsDomain A := hA.dom
  haveI : IsNoetherianRing A := hA.cm.1
  haveI : IsAdicComplete (maximalIdeal A) A := hA.complete
  by_cases hf0 : f = 0
  · exfalso
    subst hf0
    have hbc : b ⊓ c ≤ ⊥ := by
      intro x hx
      have : x ∈ (b ⊓ c).radical := Ideal.le_radical hx
      rw [hrad, Ideal.span_singleton_eq_bot.mpr rfl, Ideal.radical_eq_iff.mpr (Ideal.isPrime_bot).isRadical] at this
      exact this
    have hprod : b * c = ⊥ := le_bot_iff.mp (le_trans Ideal.mul_le_inf hbc)
    rcases Ideal.mul_eq_bot.mp hprod with h | h
    · subst h
      rw [bot_sup_eq] at hdc
      exact lt_irrefl _ hdc
    · subst h
      rw [sup_bot_eq] at hdb
      exact lt_irrefl _ hdb
  obtain ⟨hloc, hcm⟩ := adjoin hA f
  haveI : IsNoetherianRing (Algebra.adjoin A {f}) := hcm.1
  haveI : Module.Finite A (Algebra.adjoin A {f}) :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom A (Algebra.adjoin A {f}) R).toLinearMap Subtype.val_injective
  haveI : IsAdicComplete (maximalIdeal (Algebra.adjoin A {f})) (Algebra.adjoin A {f}) :=
    cplFinite (A := A) (maximalIdeal _) (maximalIdeal.isMaximal _).ne_top
  haveI : Module.Finite (Algebra.adjoin A {f}) R := Module.Finite.of_restrictScalars_finite A _ R
  let x : Algebra.adjoin A {f} := ⟨f, Algebra.self_mem_adjoin_singleton A f⟩
  have hx0 : x ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
  have hxm : x ∈ maximalIdeal (Algebra.adjoin A {f}) := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have : IsUnit f := hu.map (Algebra.adjoin A {f}).val
    exact ((mem_maximalIdeal f).mp hf) this
  have hdim : ringKrullDim (Algebra.adjoin A {f} ⧸ Ideal.ofList [x]) + ↑([x].length) =
      ringKrullDim (Algebra.adjoin A {f}) := by
    have hsp : Ideal.ofList [x] = Ideal.span {x} := by simp [Ideal.ofList]
    rw [hsp]
    apply ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_jacobson
    · exact IsSMulRegular.of_ne_zero hx0
    · rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
      exact hxm
  have hmap : Ideal.map (algebraMap (Algebra.adjoin A {f}) R) (Ideal.ofList [x]) = Ideal.span {f} := by
    simp [Ideal.ofList, Ideal.map_span]
    rfl
  have key := cut (A := Algebra.adjoin A {f}) (R := R) hcm [x] b c (by simpa using hxm) hdim (hmap ▸ hrad) hb hc hdb hdc
  simp only [List.length_singleton, Nat.cast_one] at key
  rw [add_assoc] at key
  exact key
