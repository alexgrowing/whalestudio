import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IrreducibleRepIsotypicOfCentraliserFactor
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

theorem UpperTheory.isoSum_restriction_of_local_component_unitary :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (σ : Submodule ℂ (UA E n → ℂ)), IsAutRepU σ → ∀ (w : Plc E) (j : GLw n w →* UA E n), (∀ g, j g ∈ locU n w) → (∀ g, cLoc w (j g) = g) → (∀ x ∈ locU n w, x = j (cLoc w x)) → ∀ τ : SmIrr (GLw n w), IsCompAlong σ (locU n w) ((cLoc w).comp (locU n w).subtype) τ.ρ → IsoSum ((RU E n).comp j) σ τ := by
  intro E _ _ _ n π hπ w j hj1 hj2 hj3 τ hc
  obtain ⟨hirr, f, hf0, hfm, hf⟩ := hc
  let Ψ : GlobalTheory.DefU.AutSub E n := ⟨π, hπ⟩
  let F : Representation.IntertwiningMap τ.ρ (Ψ.rep.comp j) :=
    ⟨f.codRestrict _ hfm, fun g => LinearMap.ext fun v => Subtype.ext (by
      have h := hf ⟨j g, hj1 g⟩ v
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hj2] at h
      exact h)⟩
  have hF0 : F ≠ 0 := fun h => hf0 (LinearMap.ext fun v => by
    have := congrArg Subtype.val (DFunLike.congr_fun h v)
    exact this)
  obtain ⟨r, -, -, hr⟩ := GlobalTheory.DefU.LocRet.exists_ret E n w
  have htop := (GlobalTheory.CuspRep.CompUniq.isotypic (UA E n) (GLw n w) Ψ.V τ.V τ.V Ψ.rep j τ.ρ τ.ρ
    Ψ.isIrreducible_rep hirr hirr (fun g => ⟨cLoc w (r g).1, fun y => by
      rw [← hj3 _ (r g).2]
      exact hr g ⟨j y, hj1 y⟩⟩) F hF0).1
  intro φ hφ
  have hmem : φ ∈ (⨆ i : Representation.IntertwiningMap τ.ρ (Ψ.rep.comp j),
      LinearMap.range i.toLinearMap).map π.subtype := by
    rw [htop]; exact ⟨⟨φ, hφ⟩, Submodule.mem_top, rfl⟩
  rw [Submodule.map_iSup] at hmem
  refine SetLike.le_def.1 (iSup_le fun i => ?_) hmem
  refine le_iSup_of_le ⟨π.subtype ∘ₗ i.toLinearMap, fun g v =>
    congrArg Subtype.val (Representation.IntertwiningMap.isIntertwining _ _ i g v), ?_⟩ ?_
  · rintro _ ⟨v, rfl⟩
    exact (i.toLinearMap v).2
  · exact (LinearMap.range_comp _ _).ge
