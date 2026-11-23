import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFactorDualEmbeddingOfNeZeroTensor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinrankInvFunBranch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupRangeWeightMapsEqTopDefiniteUnitary
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.hasWeightAt_of_tensor_dual_intertwiner :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), 1 ≤ n → ∀ (I : Type) [Finite I] (φ : I → E →+* ℂ), (Function.Injective fun i => InfinitePlace.mk (φ i)) → ∀ (lam : I → DomWeight n) (σ : Submodule ℂ (UA E n → ℂ)) (Φ : Module.Dual ℂ (⨂[ℂ] i, nablaSq ℂ n (lam i)) →ₗ[ℂ] (UA E n → ℂ)), Φ ≠ 0 → (∀ ℓ, Φ ℓ ∈ σ) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x⁻¹))) → ∀ i, HasWeightAt σ (φ i) (lam i).dual := by
  intro E _ _ _ n hn I _ φ hφ lam σ Φ hΦ hσ heq y
  obtain ⟨F, hF0, hF⟩ := UpperTheory.exists_factor_dual_embedding_of_ne_zero_tensor I (fun i => nablaSq ℂ n (lam i)) _ Φ hΦ y
  obtain ⟨e, he⟩ := (GlobalTheory.T.unitaryIrrep_comp_conj_iso_dual n hn (lam y)).symm.trans (GlobalTheory.T.iso_unitaryIrrep_conj_dual n (lam y))
  obtain ⟨u, hu⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n (φ y)
  refine ⟨GlobalTheory.DefU.isIrreducible_sqRep n _, (Φ ∘ₗ F) ∘ₗ e.toLinearMap, fun h0 => hF0 ?_, fun v => hσ _, fun x v => ?_⟩
  · apply LinearMap.ext
    intro m
    obtain ⟨v, rfl⟩ := e.surjective m
    exact LinearMap.congr_fun h0 v
  · have hx : x.1 ∈ infU E n := GlobalTheory.DefU.embU_le_infU _ x.2
    have hT : ∀ i, i ≠ y → GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (φ i) x.1⁻¹) = LinearMap.id := by
      intro i hi
      have h1 := (Subgroup.mem_inf.1 x.2).2
      rw [Subgroup.mem_iInf] at h1
      have h2 := h1 (φ i)
      rw [Subgroup.mem_iInf] at h2
      have h3 : cEmb (φ i) x.1 = 1 := h2 fun h => hi (hφ h)
      rw [map_inv, h3, inv_one, map_one]
      rfl
    change Φ (F (e (GlobalTheory.Branching.sqRep ℂ n (lam y).dual (cEmb (φ y) x.1) v))) = RU E n x.1 (Φ (F (e v)))
    rw [heq _ _ hx, hF _ hT, map_inv, ← hu x]
    congr 2
    rw [← map_inv]
    exact he (u x) v
