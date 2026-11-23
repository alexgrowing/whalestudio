import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfIsDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreConnectedOfProper
import Formalism.LocalToGlobal.GlobalTheory.GL6.PSplitT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormalProjectiveModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdEqZeroOfUnderEqBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

set_option autoImplicit false

noncomputable section

open IsLocalRing CategoryTheory Limits

namespace GlobalTheory.SteinFibreConn

section Completion

variable {A : Type} [CommRing A] [IsDedekindDomain A] (v : HeightOneSpectrum A)

theorem mem_maximalIdeal_iff (a : A) :
    algebraMap A (v.adicCompletionIntegers (FractionRing A)) a ∈
      maximalIdeal (v.adicCompletionIntegers (FractionRing A)) ↔ a ∈ v.asIdeal := by
  rw [mem_maximalIdeal, mem_nonunits_iff, HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one,
    ← v.valuation_lt_one_iff_mem (K := FractionRing A)]
  have e : Valued.v ((algebraMap A (v.adicCompletionIntegers (FractionRing A)) a :
      v.adicCompletionIntegers (FractionRing A)) : v.adicCompletion (FractionRing A)) =
      v.valuation (FractionRing A) (algebraMap A (FractionRing A) a) := by
    first
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v _
      | exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation v _
      | simp
  rw [e]
  exact ⟨fun h => lt_of_le_of_ne (v.valuation_le_one a) h, ne_of_lt⟩

theorem flat : Module.Flat A (v.adicCompletionIntegers (FractionRing A)) := by
  rw [IsDedekindDomain.flat_iff_torsion_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := (Submodule.mem_torsion_iff x).1 hx
  have hc' : algebraMap A (v.adicCompletionIntegers (FractionRing A)) (c : A) * x = 0 := by
    rw [← Algebra.smul_def]; exact hc
  rcases mul_eq_zero.1 hc' with h | h
  · exfalso
    have h0 : (((algebraMap A (v.adicCompletionIntegers (FractionRing A)) (c : A)) :
        v.adicCompletionIntegers (FractionRing A)) : v.adicCompletion (FractionRing A)) = 0 := by
      rw [h]; rfl
    have h1 : algebraMap (FractionRing A) (v.adicCompletion (FractionRing A))
        (algebraMap A (FractionRing A) (c : A)) = 0 := h0
    rw [map_eq_zero, IsFractionRing.to_map_eq_zero_iff] at h1
    exact nonZeroDivisors.coe_ne_zero c h1
  · exact (Submodule.mem_bot _).2 h

theorem isAdicComplete :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers (FractionRing A)))
      (v.adicCompletionIntegers (FractionRing A)) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers (FractionRing A))
  have : IsPrecomplete (maximalIdeal (v.adicCompletionIntegers (FractionRing A)))
      (v.adicCompletionIntegers (FractionRing A)) := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.completion_integers_precomplete v hϖ
  exact {}

end Completion

theorem isPreconnected_of_complete (hM : GlobalTheory.Published.FormalAlgebraisation.Morphisms) (X : Scheme.{0})
    [IsProper X.toSpecΓ] (P : Ideal Γ(X, ⊤)) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [Algebra Γ(X, ⊤) O] [Module.Flat Γ(X, ⊤) O]
    (hO : ∀ a, algebraMap Γ(X, ⊤) O a ∈ maximalIdeal O ↔ a ∈ P) :
    _root_.IsPreconnected {z : X | GlobalTheory.SteinFibre.under z = P} := by
  let f : Spec (.of O) ⟶ Spec Γ(X, ⊤) := Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) O))
  haveI : IsIso X.toSpecΓ.appTop := by rw [Scheme.toSpecΓ_appTop]; infer_instance
  haveI : Flat f := by
    show Flat (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, ⊤) O)))
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have H := IsPullback.of_hasPullback X.toSpecΓ f
  haveI : IsIso (pullback.snd X.toSpecΓ f).appTop := GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback H
  haveI : IsDomain Γ(pullback X.toSpecΓ f, ⊤) :=
    (asIso (pullback.snd X.toSpecΓ f).appTop).symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  haveI hY := GlobalTheory.ConnDvr.connectedSpace_of_isDomain (pullback X.toSpecΓ f)
  haveI hsp := GlobalTheory.AlgConn.connectedSpace_specialFibre_of_morphisms hM O _ (pullback.snd X.toSpecΓ f)
    inferInstance hY
  have hT : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f)) =
      (pullback.snd X.toSpecΓ f) ⁻¹' {IsLocalRing.closedPoint O} := by
    have h := Scheme.Pullback.range_fst (pullback.snd X.toSpecΓ f)
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue O)))
    rw [GlobalTheory.SpecialConn.range_residue] at h
    exact h
  have hcl : (f (IsLocalRing.closedPoint O)).asIdeal = P := by
    ext a
    exact hO a
  have hw : ∀ y, X.toSpecΓ (pullback.fst X.toSpecΓ f y) = f (pullback.snd X.toSpecΓ f y) := fun y => by
    rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
  have hR : Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) ≫ pullback.fst X.toSpecΓ f) =
      {z : X | GlobalTheory.SteinFibre.under z = P} := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      have hy : GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) w ∈
          Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f)) := ⟨w, rfl⟩
      rw [hT] at hy
      have hy' : pullback.snd X.toSpecΓ f (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) w) =
          IsLocalRing.closedPoint O := hy
      show (X.toSpecΓ ((GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f) ≫ pullback.fst X.toSpecΓ f) w)).asIdeal = P
      rw [Scheme.Hom.comp_apply, hw, hy']
      exact hcl
    · intro hz
      have h1 : X.toSpecΓ z = f (IsLocalRing.closedPoint O) :=
        PrimeSpectrum.ext (show (X.toSpecΓ z).asIdeal = _ from (hz : GlobalTheory.SteinFibre.under z = P).trans hcl.symm)
      obtain ⟨y, hy1, hy2⟩ := Scheme.Pullback.exists_preimage_pullback z _ h1
      have hy : y ∈ Set.range (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.specialι (pullback.snd X.toSpecΓ f)) := by
        rw [hT]; exact hy2
      obtain ⟨w, hw'⟩ := hy
      exact ⟨w, by rw [Scheme.Hom.comp_apply, hw', hy1]⟩
  rw [← hR]
  exact isPreconnected_range (Scheme.Hom.continuous _)

theorem isPreconnected_setOf_under_eq : GlobalTheory.CovTop.Hypotheses2 → ∀ (F : Type) [Field F] [NumberField F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X]
    [IsDedekindDomain Γ(X, ⊤)] (p : X ⟶ Sp (𝓞 F)) (e : ℕ), IsArithVar p e → IsArithVar (spMap (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p ⊤)) 0 →
    ∀ P : Ideal Γ(X, ⊤), _root_.IsPreconnected {z : X | GlobalTheory.SteinFibre.under z = P} := by
  intro hP F _ _ X _ _ _ p e hX _ P
  by_cases hPp : P.IsPrime
  swap
  · have h : {z : X | GlobalTheory.SteinFibre.under z = P} = ∅ := by
      ext z
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hPp (h ▸ GlobalTheory.SteinFibre.under_isPrime z)
    rw [h]
    exact isPreconnected_empty
  by_cases hb : P = ⊥
  · subst hb
    have hη : GlobalTheory.SteinFibre.under (genericPoint X) = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      rw [GlobalTheory.SteinFibre.mem_under_iff] at ha
      rw [Ideal.mem_bot]
      have hu : ∀ y : X.functionField, y ≠ 0 → IsUnit y := fun y hy => IsUnit.mk0 y hy
      have h0 : X.presheaf.germ ⊤ (genericPoint X) trivial a = 0 := by
        by_contra h
        exact ha (hu _ h)
      exact germ_injective_of_isIntegral X (U := ⊤) (genericPoint X) trivial (h0.trans (map_zero _).symm)
    refine (isPreconnected_singleton (x := genericPoint X)).subset_closure (fun z hz => ?_) (fun z _ => ?_)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hη
    · exact specializes_iff_mem_closure.1 ((genericPoint_spec X).specializes (Set.mem_univ z))
  let v : HeightOneSpectrum Γ(X, ⊤) := ⟨P, hPp, hb⟩
  haveI hpr : IsProper p := GlobalTheory.CommonModel.isProper_of_isProjOver hX.isProjOver
  have e1 : p = X.toSpecΓ ≫ (Spec.map p.appTop ≫ inv (Sp (𝓞 F)).toSpecΓ) := by
    rw [← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have h2 := hpr
  rw [e1] at h2
  haveI : IsProper X.toSpecΓ := IsProper.of_comp X.toSpecΓ (Spec.map p.appTop ≫ inv (Sp (𝓞 F)).toSpecΓ)
  haveI := isAdicComplete v
  haveI := flat v
  exact isPreconnected_of_complete hP.q18.1 X P (v.adicCompletionIntegers (FractionRing Γ(X, ⊤)))
    (mem_maximalIdeal_iff v)

end GlobalTheory.SteinFibreConn
