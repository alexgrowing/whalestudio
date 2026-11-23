import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

private theorem UpperTheory.V.Hi.projective_transport_along_equiv {Λ₀ Λ V₀ V Q : Type} [CommRing Λ₀] [CommRing Λ] [AddCommGroup V₀] [AddCommGroup V]
    [Module Λ₀ V₀] [Module Λ V] [Group Q] (e : Λ₀ ≃+* Λ) (φ : V ≃+ V₀) (hφ : ∀ a v, φ (e a • v) = a • φ v)
    (ρ' : Representation Λ Q V) (hP : Module.Projective (MonoidAlgebra Λ Q) ρ'.asModule) :
    ∃ ρ'' : Representation Λ₀ Q V₀, (∀ q v, ρ'' q v = φ (ρ' q (φ.symm v))) ∧
      Module.Projective (MonoidAlgebra Λ₀ Q) ρ''.asModule := by
  have hφ' : ∀ (a : Λ₀) v, φ.symm (a • v) = e a • φ.symm v := fun a v => by
    apply φ.injective
    rw [hφ, φ.apply_symm_apply, φ.apply_symm_apply]
  let ρ'' : Representation Λ₀ Q V₀ :=
    { toFun := fun q =>
        { toFun := fun v => φ (ρ' q (φ.symm v))
          map_add' := fun x y => by simp only [map_add]
          map_smul' := fun a v => by rw [hφ', map_smul, hφ]; rfl }
      map_one' := by ext v; simp
      map_mul' := fun g h => by ext v; simp }
  refine ⟨ρ'', fun _ _ => rfl, ?_⟩
  let E : MonoidAlgebra Λ Q ≃+* MonoidAlgebra Λ₀ Q := MonoidAlgebra.mapRingEquiv Q e.symm
  haveI := RingHomInvPair.of_ringEquiv E
  haveI := RingHomInvPair.of_ringEquiv_symm E
  let ψ : ρ'.asModule ≃+ ρ''.asModule :=
    (ρ'.asModuleEquiv.toAddEquiv.trans φ).trans ρ''.asModuleEquiv.symm.toAddEquiv
  have hψ : ∀ (r : MonoidAlgebra Λ Q) (x : ρ'.asModule), ψ (r • x) = E r • ψ x := by
    intro r x
    induction r using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => rw [add_smul, map_add, map_add, add_smul, ha, hb]
    | single g a =>
      have hE : E (MonoidAlgebra.single g a) = MonoidAlgebra.single g (e.symm a) := by
        simp [E]
      rw [hE, Representation.single_smul, Representation.single_smul]
      change φ (a • ρ' g (ρ'.asModuleEquiv x)) = e.symm a • φ (ρ' g (φ.symm (φ (ρ'.asModuleEquiv x))))
      rw [φ.symm_apply_apply, ← hφ, e.apply_symm_apply]
  let Ψ : ρ'.asModule ≃ₛₗ[(E : MonoidAlgebra Λ Q →+* MonoidAlgebra Λ₀ Q)] ρ''.asModule :=
    { ψ with map_smul' := hψ }
  exact Module.Projective.of_equiv Ψ

theorem UpperTheory.V.Hi.levelUR2ProjTr :
    ∀ (Λ₀ Λ R P G : Type) [CommRing Λ₀] [CommRing Λ] [CommRing R] [Algebra Λ₀ R] [AddCommGroup P] [Module R P] [Module Λ₀ P] [IsScalarTower Λ₀ R P] [Module Λ P] [Group G] (e : Λ₀ ≃+* Λ), (∀ (a : Λ₀) (p : P), a • p = e a • p) → ∀ (ρ : Representation Λ G P) (ρR : Representation R G P), (∀ g p, ρR g p = ρ g p) → ∀ (U U₁ : Subgroup G) [(U₁.subgroupOf U).Normal], (Module.Finite Λ (fixd ρ U₁) → Module.Finite Λ₀ (fixd ρR U₁)) ∧ ∀ ρ' : Representation Λ (U ⧸ U₁.subgroupOf U) (fixd ρ U₁), (∀ (u : U) f, (ρ' (u : U ⧸ U₁.subgroupOf U) f).1 = ρ u f) → Module.Projective (MonoidAlgebra Λ (U ⧸ U₁.subgroupOf U)) ρ'.asModule → ∃ ρ'' : Representation Λ₀ (U ⧸ U₁.subgroupOf U) (fixd ρR U₁), (∀ (u : U) f, (ρ'' (u : U ⧸ U₁.subgroupOf U) f : P) = ρR u f) ∧ Module.Projective (MonoidAlgebra Λ₀ (U ⧸ U₁.subgroupOf U)) ρ''.asModule := by
  intro Λ₀ Λ R P G _ _ _ _ _ _ _ _ _ _ e he ρ ρR hρ U U₁ _
  have hmem : ∀ p : P, p ∈ fixd ρ U₁ ↔ p ∈ fixd ρR U₁ := fun p =>
    forall_congr' fun u => forall_congr' fun _ => by rw [hρ]
  let φ : fixd ρ U₁ ≃+ fixd ρR U₁ :=
    { toFun := fun v => ⟨v.1, (hmem _).1 v.2⟩
      invFun := fun v => ⟨v.1, (hmem _).2 v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  have hφ : ∀ (a : Λ₀) v, φ (e a • v) = a • φ v := fun a v => Subtype.ext (he a v.1).symm
  refine ⟨fun hfin => ?_, fun ρ' h' hP => ?_⟩
  · let f : fixd ρ U₁ →ₛₗ[(e.symm : Λ →+* Λ₀)] fixd ρR U₁ :=
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun a v => by
          rw [← hφ]
          simp }
    haveI : RingHomSurjective (e.symm : Λ →+* Λ₀) := ⟨e.symm.surjective⟩
    exact Module.Finite.of_surjective f φ.surjective
  · obtain ⟨ρ'', h1, h2⟩ := UpperTheory.V.Hi.projective_transport_along_equiv e φ hφ ρ' hP
    refine ⟨ρ'', fun u f => ?_, h2⟩
    rw [h1, hρ]
    exact h' u (φ.symm f)
