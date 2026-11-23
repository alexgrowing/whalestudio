import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ValCount
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.JGenSpecializes
import Development.AutomorphicArithmetic.DivisorFrames.ValuationRingOfFiniteDominating
import Development.AutomorphicArithmetic.DivisorFrames.OrderEqValuationCodimOne
import Development.AutomorphicArithmetic.DivisorFrames.ResidueDegreeEqValuationDegree
open CategoryTheory AlgebraicGeometry IsLocalRing GlobalTheory GlobalTheory.ValCount GlobalTheory.TrueGeo
open scoped Classical

private theorem dom_eq {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
    {x : X} (hx : Order.coheight x = 1) {W W' : ValuationSubring X.functionField}
    (h : DominatesStalk W x) (h' : DominatesStalk W' x) : W = W' :=
  ValuationSubring.toSubring_injective ((h.range_eq hx).symm.trans (h'.range_eq hx))

private theorem coheight_above {X X' : Scheme.{0}} [IsIntegral X] [IsIntegral X']
    [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [GlobalTheory.IsNormalScheme X] [GlobalTheory.IsNormalScheme X']
    [CharZero X.functionField] (g : X' ⟶ X) [IsDominant g] (hf : (functionFieldMap g).Finite)
    (ζ : X') (h : Order.coheight (g ζ) = 1) : Order.coheight ζ = 1 := by
  haveI := IsNormalScheme.isDiscreteValuationRing_stalk h
  haveI : ValuationRing (X'.presheaf.stalk ζ) :=
    UpperTheory.valuationRing_of_finite_dominating (X.presheaf.stalk (g ζ)) X.functionField (X'.presheaf.stalk ζ) X'.functionField
      (functionFieldMap g) hf (g.stalkMap ζ).hom (fun r => (functionFieldMap_algebraMap g ζ r).symm)
  have hnf : ¬ IsField (X'.presheaf.stalk ζ) := by
    intro hF
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (X.presheaf.stalk (g ζ))
    have h1 : (g.stalkMap ζ).hom ϖ ∈ maximalIdeal (X'.presheaf.stalk ζ) :=
      map_nonunit (g.stalkMap ζ).hom ϖ hϖ.not_isUnit
    rw [IsLocalRing.isField_iff_maximalIdeal_eq.1 hF, Ideal.mem_bot] at h1
    have h2 := functionFieldMap_algebraMap g ζ ϖ
    rw [h1, map_zero, map_eq_zero,
      map_eq_zero_iff _ (IsFractionRing.injective _ X.functionField)] at h2
    exact hϖ.ne_zero h2
  exact IsNormalScheme.isDiscreteValuationRing_stalk_iff.1
    (((IsDiscreteValuationRing.TFAE (X'.presheaf.stalk ζ) hnf).out 1 0).mp this)

theorem UpperTheory.order_codim_one_finite_map :
    ∀ (X X' : Scheme.{0}) [IsIntegral X] [IsIntegral X'] [IsLocallyNoetherian X] [IsLocallyNoetherian X'] [GlobalTheory.IsNormalScheme X] [GlobalTheory.IsNormalScheme X'] [X.IsSeparated] [CharZero X.functionField] (O : Type) [CommRing O] (s : X' ⟶ Spec (.of O)) [IsProper s] (g : X' ⟶ X) (hg : g (genericPoint X') ⤳ genericPoint X), (SmallSec.fnMap g hg).Finite → ∀ (η : X) (W : ValuationSubring X.functionField), Order.coheight η = 1 → DominatesStalk W η → ∀ x : X'.functionField, (∑ᶠ ζ : X', if g ζ = η then Scheme.ord x ζ * (g.residueDegree ζ : ℤ) else 0) = ∑ᶠ V : ValuationSubring X'.functionField, if V.comap (SmallSec.fnMap g hg) = W ∧ ∀ o : O, toFunctionField s o ∈ V then vord V x * (vdeg (SmallSec.fnMap g hg) V : ℤ) else 0 := by
  intro X X' _ _ _ _ _ _ _ _ O _ s _ g hg hfin η W hη hW x
  haveI : IsDominant g := ⟨by
    rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
    intro x
    exact (hg.trans (genericPoint_specializes x)).mem_closed isClosed_closure
      (subset_closure ⟨_, rfl⟩)⟩
  have e : SmallSec.fnMap g hg = functionFieldMap g := rfl
  choose v hv using fun ζ : X' => exists_dominatesStalk ζ
  have hco : ∀ ζ : X', g ζ = η → Order.coheight ζ = 1 := fun ζ h =>
    coheight_above g hfin ζ (h ▸ hη)
  have hbij : Set.BijOn v {ζ | g ζ = η}
      {V | V.comap (SmallSec.fnMap g hg) = W ∧ ∀ o : O, toFunctionField s o ∈ V} := by
    refine ⟨fun ζ h => ⟨?_, (hv ζ).toFunctionField_mem s⟩, fun ζ _ ζ' _ h => ?_, fun V hV => ?_⟩
    · have h' : g ζ = η := h
      exact dom_eq hη (h' ▸ (hv ζ).comap g) hW
    · have h1 := (centre_eq_iff s (v ζ) ((hv ζ).toFunctionField_mem s) ζ).2 (hv ζ)
      have h2 := (centre_eq_iff s (v ζ) ((hv ζ).toFunctionField_mem s) ζ').2 (h ▸ hv ζ')
      exact h1.symm.trans h2
    · obtain ⟨hV1, hV2⟩ := hV
      have hd := dominatesStalk_centre s V hV2
      have h1 : g (centre s V hV2) = η := by
        have h2 := hd.comap g
        rw [← e, hV1] at h2
        exact h2.unique hW
      exact ⟨_, h1, dom_eq (hco _ h1) (hv _) hd⟩
  have key := finsum_mem_eq_of_bijOn (f := fun ζ : X' => Scheme.ord x ζ * (g.residueDegree ζ : ℤ))
    (g := fun V : ValuationSubring X'.functionField =>
      vord V x * (vdeg (SmallSec.fnMap g hg) V : ℤ)) v hbij (fun ζ h => by
      have h' : g ζ = η := h
      haveI := IsNormalScheme.isDiscreteValuationRing_stalk (hco ζ h')
      haveI := IsNormalScheme.isDiscreteValuationRing_stalk (x := g ζ) (h' ▸ hη)
      rw [UpperTheory.order_eq_valuation_codim_one X' ζ (v ζ) (hco ζ h') (hv ζ) x,
        UpperTheory.residueDegree_eq_valuation_degree X X' g hg ζ (v ζ) (hv ζ) inferInstance inferInstance])
  simp only [finsum_eq_if, Set.mem_setOf_eq] at key
  convert key
