import Mathlib
import GroundTheory.ArithmeticGeometry.SchemeCohomology.CurveBase
import GroundTheory.FunctionField.PlaceDefs
set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

section Algebra

theorem ringKrullDim_le_of_isIntegral {A R : Type*} [CommRing A] [CommRing R] [Algebra A R]
    [Algebra.IsIntegral A R] (h : Function.Injective (algebraMap A R)) :
    ringKrullDim A ≤ ringKrullDim R := by
  rcases isEmpty_or_nonempty (PrimeSpectrum A) with hA | hA
  · rw [ringKrullDim, Order.krullDim_eq_bot]
    exact bot_le
  rw [ringKrullDim, Order.krullDim_eq_iSup_length]
  rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
  refine iSup_le fun l => ?_
  obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal (⊥ : Ideal R)
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 h]; exact bot_le)
  have : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
  rw [← hL]
  exact LTSeries.length_le_krullDim L

variable (k R K : Type u) [Field k] [CommRing R] [IsDomain R] [Algebra k R]
  [Algebra.FiniteType k R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra k K]
  [IsScalarTower k R K]

theorem trdeg_eq_one_of_ringKrullDim_eq_one (hR : ringKrullDim R = 1) : Algebra.trdeg k K = 1 := by
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k R
  let : Algebra (MvPolynomial (Fin s) k) R := g.toRingHom.toAlgebra
  have : IsScalarTower k (MvPolynomial (Fin s) k) R :=
    IsScalarTower.of_algebraMap_eq fun c => (g.commutes c).symm
  have : Module.Finite (MvPolynomial (Fin s) k) R := hfin
  have hdim : ringKrullDim (MvPolynomial (Fin s) k) = s := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hle := ringKrullDim_le_of_isIntegral (A := MvPolynomial (Fin s) k) (R := R) hg
  rw [hdim, hR] at hle
  have hs1 : s ≤ 1 := by exact_mod_cast hle
  have : FaithfulSMul (MvPolynomial (Fin s) k) R :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  have : FaithfulSMul R K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective R K)
  have h1 : Algebra.trdeg k R = s := by
    rw [← trdeg_add_eq k (MvPolynomial (Fin s) k) (A := R), MvPolynomial.trdeg_of_isDomain,
      trdeg_eq_zero (R := MvPolynomial (Fin s) k) (A := R)]
    simp
  have h2 : Algebra.trdeg k K = s := by
    have : Algebra.IsAlgebraic R K := IsLocalization.isAlgebraic K (nonZeroDivisors R)
    rw [← trdeg_add_eq k R (A := K), h1, trdeg_eq_zero (R := R) (A := K), add_zero]
  rcases Nat.lt_or_ge s 1 with h0 | h1'
  · exfalso
    have hs0 : s = 0 := by omega
    subst hs0
    have : Algebra.IsIntegral k (MvPolynomial (Fin 0) k) :=
      Algebra.IsIntegral.of_surjective (Algebra.ofId k (MvPolynomial (Fin 0) k))
        (MvPolynomial.C_surjective (Fin 0))
    have : Algebra.IsIntegral k R := Algebra.IsIntegral.trans (MvPolynomial (Fin 0) k)
    have hfield : IsField R :=
      (Algebra.IsIntegral.isField_iff_isField (algebraMap k R).injective).1 (Field.toIsField k)
    rw [ringKrullDim_eq_zero_of_isField hfield] at hR
    exact zero_ne_one hR
  · rw [h2, le_antisymm hs1 h1']
    simp

theorem isFunctionField_of_ringKrullDim_eq_one (hR : ringKrullDim R = 1) :
    GroundTheory.FunctionField.IsFunctionField k K := by
  have htr := trdeg_eq_one_of_ringKrullDim_eq_one k R K hR
  have : Algebra.Transcendental k K := by
    rw [← trdeg_ne_zero_iff, htr]
    exact one_ne_zero
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := K)
  refine ⟨x, hx, ?_⟩
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set K) → K) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set K))).2 hx)
      (by rw [htr, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType R K :=
    Algebra.EssFiniteType.of_isLocalization K (nonZeroDivisors R)
  have : Algebra.EssFiniteType k K := Algebra.EssFiniteType.comp k R K
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) K :=
    Algebra.EssFiniteType.of_comp k _ K
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end Algebra

section Scheme

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))] [IsIntegral X]

lemma exists_ne_genericPoint (hX : topologicalKrullDim X = 1) : ∃ x : X, x ≠ genericPoint X := by
  by_contra! h
  have : Subsingleton X := ⟨fun a b => (h a).trans (h b).symm⟩
  let := specializationOrder X
  have h0 : topologicalKrullDim X ≤ 0 := by
    unfold topologicalKrullDim
    rw [Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints]
    exact Order.krullDim_nonpos_of_subsingleton
  rw [hX] at h0
  exact absurd h0 (by decide)

theorem isFunctionField [LocallyOfFiniteType (X ↘ Spec (.of k))]
    (hX : topologicalKrullDim X = 1) :
    GroundTheory.FunctionField.IsFunctionField k X.functionField := by
  obtain ⟨x, hx⟩ := exists_ne_genericPoint X hX
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : Nonempty U := ⟨⟨x, hxU⟩⟩
  let : Algebra k Γ(X, U) :=
    ((X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op).hom.comp (scalarRingHom X)).toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := by
    have h := (X ↘ Spec (.of k)).finiteType_appLE (isAffineOpen_top (Spec (.of k))) hU le_top
    have e : algebraMap k Γ(X, U) = ((X ↘ Spec (.of k)).appLE ⊤ U le_top).hom.comp
        (Scheme.ΓSpecIso (.of k)).inv.hom := rfl
    rw [← RingHom.finiteType_algebraMap, e]
    refine h.comp (RingHom.FiniteType.of_surjective _ fun y => ⟨(Scheme.ΓSpecIso (.of k)).hom y, ?_⟩)
    simp
  have : IsFractionRing Γ(X, U) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X U hU
  have : IsScalarTower k Γ(X, U) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun c => ?_
    rw [algebraMap_functionField]
    change X.germToFunctionField ⊤ (scalarRingHom X c) = X.germToFunctionField U
      (X.presheaf.map (homOfLE le_top : U ⟶ ⊤).op (scalarRingHom X c))
    simp only [Scheme.germToFunctionField, TopCat.Presheaf.germ_res_apply]
  have hdim : ringKrullDim Γ(X, U) = 1 := by
    have hle : ringKrullDim Γ(X, U) ≤ 1 := by
      rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
      change topologicalKrullDim (Spec Γ(X, U)) ≤ 1
      rw [← IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
      exact (topologicalKrullDim_subspace_le X U).trans hX.le
    have hηU : genericPoint X ∈ U :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
    have hnf : ¬ IsField Γ(X, U) := by
      intro hF
      let := hF.toField
      have h2 := hU.isoSpec.hom.homeomorph.injective
        (Subsingleton.elim (α := PrimeSpectrum Γ(X, U)) (hU.isoSpec.hom.homeomorph ⟨x, hxU⟩)
          (hU.isoSpec.hom.homeomorph ⟨genericPoint X, hηU⟩))
      exact hx (congrArg Subtype.val h2)
    have h0 : ringKrullDim Γ(X, U) ≠ 0 := fun h => hnf (by
      have : Ring.KrullDimLE 0 Γ(X, U) := by
        rw [Ring.krullDimLE_iff, h]
        rfl
      exact Ring.KrullDimLE.isField_of_isDomain)
    have hnn : 0 ≤ ringKrullDim Γ(X, U) := ringKrullDim_nonneg_of_nontrivial
    generalize ringKrullDim Γ(X, U) = d at hle h0 hnn ⊢
    induction d using WithBot.recBotCoe with
    | bot => exact absurd hnn (by simp)
    | coe n =>
      have h1 : n ≤ 1 := by exact_mod_cast hle
      have h2 : n ≠ 0 := by exact_mod_cast h0
      rw [le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h2)]
      rfl
  exact isFunctionField_of_ringKrullDim_eq_one k Γ(X, U) X.functionField hdim

end Scheme

end GroundTheory.Arith.SchemeCoh
