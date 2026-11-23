import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.GlobalEulerFormulaInf
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Devissage
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section General

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem card_cohomology_eq_of_iso {A B : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B]
    (e : A ≅ B) (q : ℕ) : Nat.card (cohomology A q) = Nat.card (cohomology B q) := by
  let i : cohomology A q ≅ cohomology B q :=
    { hom := cohomologyMap e.hom q
      inv := cohomologyMap e.inv q
      hom_inv_id := by rw [← cohomologyMap_comp, e.hom_inv_id, cohomologyMap_id]
      inv_hom_id := by rw [← cohomologyMap_comp, e.inv_hom_id, cohomologyMap_id] }
  exact Nat.card_congr i.toLinearEquiv.toEquiv

omit [TopologicalSpace G] [IsTopologicalGroup G] in

theorem card_eq_of_iso {A B : Rep.{u} k G} (e : A ≅ B) : Nat.card A = Nat.card B :=
  Nat.card_congr ((forget (Rep.{u} k G)).mapIso e).toEquiv

theorem card_cohomology_zero_of_subsingleton (A : Rep.{u} k G) [IsDiscreteRep A] [Subsingleton A] :
    Nat.card (cohomology A 0) = 1 := by
  rw [Nat.card_congr (H0Iso A).toLinearEquiv.toEquiv]
  exact Nat.card_unique

theorem card_cohomology_zero_of_forall_eq_one (A : Rep.{u} k G) [IsDiscreteRep A]
    (h : ∀ g, A.ρ g = 1) : Nat.card (cohomology A 0) = Nat.card A := by
  rw [Nat.card_congr (H0Iso A).toLinearEquiv.toEquiv]
  have hmem : ∀ x : A, x ∈ A.ρ.invariants := fun x g => by rw [h g]; rfl
  exact Nat.card_congr (Equiv.subtypeUnivEquiv hmem)

end General

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]

section Real

open scoped Classical

variable (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)

theorem gsRealH0Card_pos [Finite M] (v : {v : InfinitePlace K.1 // v.IsReal}) :
    0 < gsRealH0Card S M ιr v := by
  have : Finite (Rep.res (gsRealFamily S ιr v).toMonoidHom M) := inferInstanceAs (Finite M)
  have := finite_cohomology_zero (Rep.res (gsRealFamily S ιr v).toMonoidHom M)
  exact Nat.card_pos

theorem gsEulerRatio_eq_of_iso {N : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)}
    [IsDiscreteRep N] (e : M ≅ N) : gsEulerRatio S M ιr = gsEulerRatio S N ιr := by
  have hv : ∀ v, gsRealH0Card S M ιr v = gsRealH0Card S N ιr v := fun v =>
    card_cohomology_eq_of_iso ((Rep.resFunctor (gsRealFamily S ιr v).toMonoidHom).mapIso e) 0
  simp only [gsEulerRatio, eulerChar_eq_of_iso e, card_eq_of_iso e, hv]

theorem gsEulerRatio_eq_one_of_subsingleton [Subsingleton M] : gsEulerRatio S M ιr = 1 := by
  have hv : ∀ v, gsRealH0Card S M ιr v = 1 := fun v => by
    have : Subsingleton (Rep.res (gsRealFamily S ιr v).toMonoidHom M) :=
      inferInstanceAs (Subsingleton M)
    exact card_cohomology_zero_of_subsingleton _
  have hM : Nat.card M = 1 := Nat.card_unique
  simp [gsEulerRatio, eulerChar_eq_one_of_subsingleton, hv]

theorem eulerChar_gs_pos [Finite S] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    0 < eulerChar M := by
  refine Finset.prod_pos fun q hq => ?_
  have : Finite (cohomology M q) :=
    finite_cohomology_gs K S M hS q (Nat.lt_succ_iff.1 (Finset.mem_range.1 hq))
  have : (0 : ℚ) < Nat.card (cohomology M q) := by exact_mod_cast Nat.card_pos
  exact zpow_pos this _

theorem gsEulerRatio_pos [Finite S] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    0 < gsEulerRatio S M ιr := by
  have h1 := eulerChar_gs_pos S M hS
  have h2 : (0 : ℚ) < Nat.card M := by exact_mod_cast Nat.card_pos
  have h3 : (0 : ℚ) < ∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S M ιr v : ℚ) :=
    Finset.prod_pos fun v _ => by exact_mod_cast gsRealH0Card_pos S M ιr v
  unfold gsEulerRatio
  convert div_pos (mul_pos h1 (pow_pos h2 (Fintype.card (InfinitePlace K.1)))) h3

theorem gsEulerRatio_eq_one_iff [Finite M] :
    gsEulerRatio S M ιr = 1 ↔
      eulerChar M = (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S M ιr v : ℚ)) /
        (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K.1) := by
  have h2 : (0 : ℚ) < Nat.card M := by exact_mod_cast Nat.card_pos
  have hn : (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K.1) ≠ 0 := (pow_pos h2 _).ne'
  have h3 : (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S M ιr v : ℚ)) ≠ 0 :=
    (Finset.prod_pos fun v _ => by exact_mod_cast gsRealH0Card_pos S M ιr v).ne'
  unfold gsEulerRatio
  convert (div_eq_one_iff_eq h3).trans (eq_div_iff hn).symm

theorem globalEulerFormula_iff :
    GlobalEulerFormula S ιr ↔
      ∀ (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M],
        (∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) →
          gsEulerRatio S M ιr = 1 := by
  refine forall_congr' fun M => ?_
  refine ⟨fun h _ _ hS => ?_, fun h _ _ hS => ?_⟩
  · exact (gsEulerRatio_eq_one_iff S M ιr).2 (by convert h hS)
  · convert (gsEulerRatio_eq_one_iff S M ιr).1 (h hS)

end Real

section Infinite

open scoped Classical

variable (ι : ∀ v : InfinitePlace K.1, ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

theorem card_gsInfH0_of_isComplex {v : InfinitePlace K.1} (hv : v.IsComplex) :
    gsInfH0Card S M ι v = Nat.card M := by
  unfold gsInfH0Card
  refine (card_cohomology_zero_of_forall_eq_one _ fun g => ?_).trans rfl
  rw [eq_one_of_isComplex hv g, map_one]

theorem gsInfH0Card_real (v : {v : InfinitePlace K.1 // v.IsReal}) :
    gsInfH0Card S M ι v.1 = gsRealH0Card S M (fun w => ι w.1) v :=
  rfl

theorem gsEulerInfFactor_eq [Finite M] :
    gsEulerInfFactor S M ι =
      (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S M (fun w => ι w.1) v : ℚ)) /
        (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K.1) := by
  classical
  have h2 : (0 : ℚ) < Nat.card M := by exact_mod_cast Nat.card_pos
  set n : ℚ := (Nat.card M : ℚ) with hn
  have hcard : n ^ Fintype.card (InfinitePlace K.1) =
      n ^ Fintype.card {v : InfinitePlace K.1 // v.IsReal} *
        n ^ Fintype.card {v : InfinitePlace K.1 // v.IsComplex} := by
    have := InfinitePlace.prod_eq_prod_mul_prod (K := K.1) (fun _ => n)
    simpa [Finset.prod_const, Finset.card_univ] using this
  unfold gsEulerInfFactor
  rw [InfinitePlace.prod_eq_prod_mul_prod, hcard]
  have hr : ∀ v : {v : InfinitePlace K.1 // v.IsReal},
      (gsInfH0Card S M ι v.1 : ℚ) / n ^ v.1.mult = (gsRealH0Card S M (fun w => ι w.1) v : ℚ) / n := by
    intro v
    rw [InfinitePlace.mult_isReal v, gsInfH0Card_real, pow_one]
  have hc : ∀ v : {v : InfinitePlace K.1 // v.IsComplex},
      (gsInfH0Card S M ι v.1 : ℚ) / n ^ v.1.mult = n⁻¹ := by
    intro v
    rw [InfinitePlace.mult_isComplex v, card_gsInfH0_of_isComplex S M ι v.2, ← hn]
    field_simp
  rw [Fintype.prod_congr _ _ hr, Fintype.prod_congr _ _ hc, Finset.prod_const, Finset.card_univ,
    Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, inv_pow]
  field_simp

theorem eulerChar_eq_gsEulerInfFactor_iff [Finite M] :
    eulerChar M = gsEulerInfFactor S M ι ↔ gsEulerRatio S M (fun w => ι w.1) = 1 := by
  rw [gsEulerRatio_eq_one_iff, gsEulerInfFactor_eq]

theorem globalEulerFormulaInf_iff :
    GlobalEulerFormulaInf S ι ↔ GlobalEulerFormula S (fun w => ι w.1) := by
  rw [globalEulerFormula_iff]
  refine forall_congr' fun M => ⟨fun h _ _ hS => ?_, fun h _ _ hS => ?_⟩
  · exact (eulerChar_eq_gsEulerInfFactor_iff S M ι).1 (h hS)
  · exact (eulerChar_eq_gsEulerInfFactor_iff S M ι).2 (h hS)

end Infinite

end

end GroundTheory.ProfCoh
