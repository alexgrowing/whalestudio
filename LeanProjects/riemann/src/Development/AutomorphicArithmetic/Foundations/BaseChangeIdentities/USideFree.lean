import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLevelOfFixed
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLinks.UnitaryGeometricSideSeparableTest

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem _root_.UpperTheory.BaseChangeIdentities.uSide : USide := by
  intro E _ _ _ hU n hn S hS lam K' hK'
  have L3 := GlobalTheory.T.inf_fixedVectors_adelicLevel_ne_bot_of_localLevel
  have L4 := GlobalTheory.T.localComponent_levelFixedVectors_ne_bot
  have L5 := GlobalTheory.T.heckeOperator_testFamily_preserves_level_forms
  obtain ⟨hfd, ι, hι, π, hπ, hind, hsup, hcomp⟩ := GlobalTheory.T.unitaryAutForms_weight_level_finite_sum_fixed_vectors E hU n hn S hS lam K' hK'
  have hloc := fun i w => GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary E hU n hn (π i) (hπ i).1 w
  choose σ hσc hσf using fun i w => (hloc i w).1
  refine ⟨ι, hι, π, σ, fun i => ⟨(hπ i).1, (hπ i).2.1, hasLevel_of_fixed hS (hπ i).2.2, fun w hw =>
    ⟨hσc i w, L4 E hU n hn S hS lam K' hK' (π i) (hπ i).1 (hπ i).2.1 (hπ i).2.2 w hw (σ i w) (hσc i w), hσf i w⟩⟩,
    ?_, ?_⟩
  · intro π₀ h0 hw0 hl0
    obtain ⟨i, hi⟩ := hcomp π₀ h0 hw0 (L3 E n S hS K' hK' π₀ h0 hl0)
    refine ⟨i, fun w _ => ?_⟩
    obtain ⟨⟨σ₀, h₀, -⟩, -⟩ := GlobalTheory.T.exists_unique_admissible_localComponent_definiteUnitary E hU n hn π₀ h0 w
    obtain ⟨e⟩ := (hloc i w).2 σ₀ (σ i w) (hi w σ₀ h₀) (hσc i w)
    exact isCompU_of_equiv h₀ e
  · intro f hf hsep
    have hM : ∀ i, FiniteDimensional ℂ ↥(π i ⊓ fixed (RF E n) (globLev S K')) := fun i =>
      Submodule.finiteDimensional_of_le
        (hsup ▸ le_iSup (fun i => π i ⊓ fixed (RF E n) (globLev S K')) i)
    have h1 := GlobalTheory.T.traceOnInvariantSubmodule_iSup_eq_sum _ ι (fun i => π i ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) hind hM
      (fun i => L5 E n S hS K' hK' f hf (π i) (hπ i).1)
    rw [hsup] at h1
    have h2 := GlobalTheory.T.heckeTrace_weightForms_eq_dim_mul_rationalClasses E hU n hn S hS lam K' hK' f hf hsep
    have h3 := GlobalTheory.PreStabU.geomURat_eq_geomU E hU n hn S hS lam K' hK' f hf hsep
    have h4 : geomURat lam (fun γ => twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f)) =
        geomURat lam (fun γ => ∏ᶠ w ∈ S, twOrb (MonoidHom.id _) (KL n w) (locPt w γ) (f w)) := by
      unfold geomURat
      refine finsum_congr fun c => ?_
      split_ifs with hc
      · exact congrArg (_ * ·) (GlobalTheory.T.twistedOrbitalIntegral_product_eq_finprod E hU n hn S hS K' hK' f hf c.rep hc)
      · rfl
    have h5 : ∀ i, trOn (π i ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) =
        dimW lam * ∏ᶠ w ∈ S, twTr (σ i w).ρ (KL n w) (K' w) (f w) LinearMap.id := fun i =>
      GlobalTheory.T.trace_hecke_levelVectors_eq_dim_mul_local_traces E hU n hn (π i) (hπ i).1 S hS lam (hπ i).2.1 K' hK' (σ i) (hσc i) f hf
    have key : ∑ i, trOn (π i ⊓ fixed (RF E n) (globLev S K')) (hop S K' f) = dimW lam * geomU S lam f := by
      rw [← h1, h2, h4, h3]
    simp_rw [h5, ← Finset.mul_sum] at key
    exact mul_left_cancel₀ (dimW_ne_zero lam) key

end GlobalTheory.BCT
