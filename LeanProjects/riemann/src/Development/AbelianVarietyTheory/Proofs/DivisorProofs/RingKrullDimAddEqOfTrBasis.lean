import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.AdjKltOfLtDisc
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RingKrullDimQuotientAddOneOfMemMinimalPrimesSup

set_option autoImplicit false

noncomputable section

open Algebra

namespace GlobalTheory.LocModelDim

theorem isAlgebraic_of_forall_mul {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ s : S, ∃ a b : R, algebraMap R S b ≠ 0 ∧ s * algebraMap R S b = algebraMap R S a) :
    Algebra.IsAlgebraic R S := by
  refine ⟨fun s => ?_⟩
  obtain ⟨a, b, hb, e⟩ := h s
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => Polynomial.coeff p 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ,
      sub_zero, Polynomial.coeff_zero, if_true] at h1
    rw [h1, map_zero]
  · rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C, mul_comm, e,
      sub_self]

theorem ringKrullDim_add_trdeg {k R Ω : Type} [Field k] [CommRing R] [IsDomain R]
    [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] [Field Ω] [Algebra R Ω]
    [Algebra k Ω] [IsScalarTower k R Ω] (hχ : Function.Surjective (algebraMap R Ω)) {n m : ℕ}
    (hn : trdeg k Ω = n) (hm : trdeg k R = m) : ringKrullDim R + n = m := by
  set A := EssFiniteType.subalgebra k R
  set ι := algebraMap A R
  set f : A →+* Ω := (algebraMap R Ω).comp ι with hf
  set P := RingHom.ker f with hP
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hmax : RingHom.ker (algebraMap R Ω) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hχ)
  have hunit : ∀ r : R, IsUnit r ↔ algebraMap R Ω r ≠ 0 := by
    intro r
    have := congrArg (r ∈ ·) hmax
    simp only [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
    rw [Ne, this, not_not]
  have hM : EssFiniteType.submonoid k R = P.primeCompl := by
    ext x
    simp only [EssFiniteType.submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
      Ideal.mem_primeCompl_iff, hP, RingHom.mem_ker, hf, RingHom.comp_apply, hunit]
    rfl
  haveI : IsLocalization.AtPrime R P := by
    unfold IsLocalization.AtPrime
    rw [← hM]
    infer_instance

  have hdimR : ringKrullDim R = P.height := IsLocalization.AtPrime.ringKrullDim_eq_height P R
  have hform := GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType k P
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  obtain ⟨s', hs1', hs2'⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A ⧸ P)

  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (EssFiniteType.submonoid k R)
  have hAR := trdeg_add_eq k A (A := R)
  rw [trdeg_eq_zero (R := A) (A := R), add_zero, hs2, hm] at hAR

  letI : Algebra (A ⧸ P) Ω := (RingHom.kerLift f).toAlgebra
  haveI : IsScalarTower k (A ⧸ P) Ω := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap k Ω x = f (algebraMap k A x)
    rw [hf, RingHom.comp_apply, IsScalarTower.algebraMap_apply k R Ω]
    rfl
  haveI : FaithfulSMul (A ⧸ P) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective f)
  haveI : Algebra.IsAlgebraic (A ⧸ P) Ω := by
    apply isAlgebraic_of_forall_mul
    intro ω
    obtain ⟨r, rfl⟩ := hχ ω
    obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (EssFiniteType.submonoid k R) r
    refine ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P t, ?_, ?_⟩
    · change f t ≠ 0
      exact (hunit _).1 t.2
    · change algebraMap R Ω r * f t = f a
      rw [hf, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      exact congrArg (algebraMap R Ω) e
  haveI hdom : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  haveI : Nontrivial (A ⧸ P) := hdom.toNontrivial
  haveI : FaithfulSMul k (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k (A ⧸ P)).injective
  have hPΩ := trdeg_add_eq k (A ⧸ P) (A := Ω)
  rw [trdeg_eq_zero (R := A ⧸ P) (A := Ω), add_zero, hs2', hn] at hPΩ
  have hss : s' = n := by exact_mod_cast hPΩ
  have hsm : s = m := by exact_mod_cast hAR
  rw [hdimR, ← hss, ← hsm, ← hs1', ← hs1]
  exact hform

end GlobalTheory.LocModelDim

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
