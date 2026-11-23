import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyValExtOfOverLa
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FactorDepth

namespace GlobalTheory.GenericCentre

theorem trdegGe_of_le_trdeg {k L M : Type} [Field k] [Field L] [Field M] [Algebra k L] (g : L →+* M) {d : ℕ}
    (hd : (d : Cardinal) ≤ Algebra.trdeg k L) : TrdegGe M d := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k L
  have hc : Cardinal.mk (Fin d) ≤ Cardinal.mk s := by
    rw [hs.cardinalMk_eq_trdeg]; simpa using hd
  obtain ⟨e⟩ := hc
  have h1 : AlgebraicIndependent k (((↑) : s → L) ∘ e) := hs.1.comp e e.injective
  let _ : Algebra k M := (g.comp (algebraMap k L)).toAlgebra
  have h2 : AlgebraicIndependent k (g ∘ (((↑) : s → L) ∘ e)) :=
    h1.ringHom_of_comp_eq (RingHom.id k) g Function.surjective_id g.injective rfl
  let e' := (algebraMap k M).rangeRestrictFieldEquiv
  let j : (⊥ : Subfield M) →+* k := e'.symm.toRingHom.comp (Subfield.inclusion bot_le)
  refine ⟨_, AlgebraicIndependent.of_ringHom_of_comp_eq j (RingHom.id M) h2 j.injective ?_⟩
  ext z
  exact congrArg Subtype.val (e'.apply_symm_apply (Subfield.inclusion bot_le z))

theorem exists_cdvr_centred_generic (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (A : Type) [CommRing A] [Algebra O A] [Algebra.FiniteType O A] (K : Type) [Field K] [Algebra A K] [Algebra O K]
    [IsScalarTower O A K] (hinj : Function.Injective (algebraMap O K))
    (hfrac : ∀ x : K, ∃ a b : A, algebraMap A K b ≠ 0 ∧ x * algebraMap A K b = algebraMap A K a)
    (p : Ideal A) (hp : p.IsPrime) (hker : RingHom.ker (algebraMap A K) ≤ p)
    (hm : (maximalIdeal O).map (algebraMap O A) ≤ p) (d : ℕ) (hd : (d : Cardinal) ≤ Algebra.trdeg O K) :
    ∃ (T : CDVR) (f : A →+* T.V) (ψ : K →+* T.Fr),
      (algebraMap T.V T.Fr).comp f = ψ.comp (algebraMap A K) ∧ IsLocalHom (f.comp (algebraMap O A)) ∧
      TrdegGe ((maximalIdeal T.V).comap f).ResidueField d := by
  let P := RingHom.ker (algebraMap A K)
  have hP : P.IsPrime := RingHom.ker_isPrime _
  let B := A ⧸ P
  let _ : Algebra B K := (RingHom.kerLift (algebraMap A K)).toAlgebra
  have hBK : Function.Injective (algebraMap B K) := RingHom.kerLift_injective _
  have hmk : ∀ a : A, algebraMap B K (Ideal.Quotient.mk P a) = algebraMap A K a := fun _ => rfl
  have : IsScalarTower O B K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsScalarTower.algebraMap_apply O A K x).trans (hmk _).symm
  have : FaithfulSMul B K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hBK
  have hOB : Function.Injective (algebraMap O B) := by
    refine Function.Injective.of_comp (f := algebraMap B K) ?_
    rw [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
    exact hinj
  have : FaithfulSMul O B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hOB
  have : IsFractionRing B K := by
    refine IsFractionRing.of_field B K fun x => ?_
    obtain ⟨a, b, hb, h⟩ := hfrac x
    exact ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P b, by rw [hmk, hmk, ← h, mul_div_cancel_right₀ _ hb]⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  have hp' : (p.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hker)
  have hle : (maximalIdeal O).map (algebraMap O B) ≤ p.map (Ideal.Quotient.mk P) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact Ideal.mem_map_of_mem (Ideal.Quotient.mk P) (hm (Ideal.mem_map_of_mem _ hx))
  obtain ⟨q, hq, -⟩ := Ideal.exists_minimalPrimes_le hle
  have hqp : q.IsPrime := hq.1.1
  have hlo := GlobalTheory.liesOver_maximalIdeal_of_mem_minimalPrimes O hq
  have hq0 : (⊥ : Ideal B) < q := by
    rw [bot_lt_iff_ne_bot]
    rintro rfl
    apply IsDiscreteValuationRing.not_a_field O
    rw [hlo.over]
    exact Ideal.comap_bot_of_injective _ hOB
  obtain ⟨V, _, _, _, hc, φ, hφ0, hφ⟩ := GlobalTheory.exists_complete_discreteValuationRing_of_prime_lt (⊥ : Ideal B) q hq0
  have hφi : Function.Injective φ := (RingHom.injective_iff_ker_eq_bot φ).mpr hφ0
  have h0 : CharZero V := charZero_of_injective_ringHom (f := φ.comp (algebraMap O B)) (hφi.comp hOB)
  let T : CDVR := @CDVR.mk V _ _ _ hc h0
  let f : A →+* V := φ.comp (Ideal.Quotient.mk P)
  have hg : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V _).comp hφi
  refine ⟨T, f, IsFractionRing.lift (A := B) (K := K) hg, ?_, ?_, ?_⟩
  · ext a
    exact (IsFractionRing.lift_algebraMap (K := K) hg (Ideal.Quotient.mk P a)).symm
  · refine ⟨fun x hx => ?_⟩
    by_contra hn
    have h1 : algebraMap O B x ∈ q := hq.1.2 (Ideal.mem_map_of_mem _ hn)
    rw [← hφ] at h1
    exact h1 hx
  · have := GlobalTheory.isLocalHom_algebraMap_localization_of_liesOver O q
    have h1 := GlobalTheory.trdeg_residueField_eq_of_mem_minimalPrimes O (ResidueField O) residue_surjective q hq
    have : Algebra.IsAlgebraic B K := IsLocalization.isAlgebraic _ (nonZeroDivisors B)
    rw [GlobalTheory.trdeg_eq_of_isAlgebraic_top O B K, ← h1] at hd
    let Q : Ideal A := (maximalIdeal V).comap f
    have hQ : ∀ a, a ∈ Q ↔ Ideal.Quotient.mk P a ∈ q := fun a => by rw [← hφ]; rfl
    let g : B →+* Q.ResidueField := Ideal.Quotient.lift P (algebraMap A _) fun a ha => by
      rw [Ideal.algebraMap_residueField_eq_zero, hQ, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      exact q.zero_mem
    have hgq : ∀ b, g b = 0 ↔ b ∈ q := fun b => by
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [← hQ]
      exact Ideal.algebraMap_residueField_eq_zero
    exact trdegGe_of_le_trdeg (Ideal.ResidueField.lift q g (fun b hb => (hgq b).mpr hb)
      fun b hb => Ne.isUnit fun h => hb ((hgq b).mp h)) hd

end GlobalTheory.GenericCentre
