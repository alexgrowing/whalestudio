import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MeanSquareAddFundamentalDomainOfCocompact
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCompactAdeleRingModNumberField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsNhdsZeroPrincipalEqZero
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep

namespace GlobalTheory.ConstNotCusp

variable (E : Type) [Field E] [NumberField E] (a r : ℕ)

theorem discreteTopology_ratN : DiscreteTopology (ratN E a r) := by
  obtain ⟨U, hU, h0⟩ := GlobalTheory.AdeleDiscrete.exists_nhds_zero_principal_eq_zero E
  obtain ⟨V, hVU, hVo, hV0⟩ := mem_nhds_iff.1 hU
  refine discreteTopology_of_isOpen_singleton_zero ?_
  have hW : IsOpen (Set.pi Set.univ fun _ : BlockIx a r => V) :=
    isOpen_set_pi Set.finite_univ fun _ _ => hVo
  convert hW.preimage (continuous_subtype_val (p := fun x => x ∈ ratN E a r)) using 1
  ext ⟨_, x, rfl⟩
  constructor
  · intro h p _
    have h1 := congrFun (congrArg Subtype.val (Set.mem_singleton_iff.1 h)) p
    exact h1.symm ▸ hV0
  · intro h
    have hx : x = 0 := funext fun p => h0 (x p) (hVU (h p trivial))
    subst hx
    exact Subtype.ext (map_zero _)

theorem exists_compact_ratN : ∃ K : Set (BlockIx a r → Ad E), IsCompact K ∧
    ∀ x, ∃ γ ∈ ratN E a r, γ + x ∈ K := by
  obtain ⟨K, hK, h⟩ := GlobalTheory.AdeleCocompact.exists_compact_adele E
  refine ⟨Set.pi Set.univ fun _ => K, isCompact_univ_pi fun _ => hK, fun x => ?_⟩
  choose y hy using fun p => h (x p)
  refine ⟨_, ⟨fun p => -y p, rfl⟩, fun p _ => ?_⟩
  change algebraMap E (Ad E) (-y p) + x p ∈ K
  rw [map_neg, neg_add_eq_sub]
  exact hy p

theorem not_isCuspidal_oneFn : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ),
    2 ≤ a → ¬ IsCuspidal (oneFn E a).1 := by
  intro E _ _ _ a ha h
  haveI : LocallyCompactSpace (Ad E) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele E
  haveI : SecondCountableTopology (Ad E) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : T2Space (Ad E) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField E
  letI : MeasurableSpace (BlockIx a 1 → Ad E) := borel _
  haveI : BorelSpace (BlockIx a 1 → Ad E) := ⟨rfl⟩
  haveI := discreteTopology_ratN E a 1
  obtain ⟨K, hK, hcov⟩ := exists_compact_ratN E a 1
  obtain ⟨⟨μ, F, hμ, hF, h1⟩, -⟩ :=
    GlobalTheory.meanSquare_addFundamentalDomain_of_cocompact _ (ratN E a 1) K hK hcov
  have h2 : ∫ _ in F, (1 : ℂ) ∂μ = 0 := h 1 one_pos (by omega) μ F hμ hF 1
  simp [Measure.real, h1] at h2

end GlobalTheory.ConstNotCusp
