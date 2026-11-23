import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.EveryPointSatisfiesFrameCondition

open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.Base
open scoped Matrix

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing

namespace UpperTheory.V.Th.Db

theorem algClo (L Ω : Type) [Field L] [NumberField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] [Algebra L Ω] :
    IsAlgClosure L Ω := by
  haveI := IsAlgClosure.isAlgClosed ℚ (K := Ω)
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  exact ⟨inferInstance, Algebra.IsAlgebraic.tower_top (K := ℚ) L⟩

theorem algKL (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    [Algebra K Ω] [Algebra L Ω] (h : galOf ℚ L Ω ≤ galOf ℚ K Ω) : ∃ _ : Algebra K L, IsScalarTower K L Ω := by
  let g := IsScalarTower.toAlgHom ℚ L Ω
  let f := IsScalarTower.toAlgHom ℚ K Ω
  have hmem : ∀ x : K, f x ∈ g.range := by
    intro x
    have hfix : algebraMap K Ω x ∈ IntermediateField.fixedField g.fieldRange.fixingSubgroup := by
      rw [IntermediateField.mem_fixedField_iff]
      intro σ hσ
      have hL : σ ∈ galOf ℚ L Ω := by
        show ∀ y : L, σ (algebraMap L Ω y) = algebraMap L Ω y
        intro y
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ (g y) ⟨y, rfl⟩
      exact (show ∀ z : K, σ (algebraMap K Ω z) = algebraMap K Ω z from h hL) x
    rw [InfiniteGalois.fixedField_fixingSubgroup] at hfix
    obtain ⟨y, hy⟩ := hfix
    exact ⟨y, hy⟩
  let e := AlgEquiv.ofInjectiveField g
  let φ : K →+* L := e.symm.toRingHom.comp (f.codRestrict g.range hmem).toRingHom
  have key : ∀ x, algebraMap L Ω (φ x) = algebraMap K Ω x := by
    intro x
    exact congrArg Subtype.val (e.apply_symm_apply ⟨f x, hmem x⟩)
  letI : Algebra K L := φ.toAlgebra
  exact ⟨this, IsScalarTower.of_algebraMap_eq fun x => (key x).symm⟩

theorem galKL (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] (h : IsAbelianGalois ℚ L) :
    IsGalois K L ∧ IsSolvable (L ≃ₐ[K] L) := by
  haveI : IsGalois ℚ L := h.toIsGalois
  refine ⟨IsGalois.tower_top_of_isGalois ℚ K L, ?_⟩
  haveI : Group.IsSolvable (L ≃ₐ[ℚ] L) :=
    isSolvable_of_comm fun a b => h.toIsMulCommutative.is_comm.comm a b
  let f : (L ≃ₐ[K] L) →* (L ≃ₐ[ℚ] L) :=
    { toFun := fun σ => σ.restrictScalars ℚ
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact solvable_of_solvable_injective (f := f) fun a b hab =>
    AlgEquiv.ext fun x => DFunLike.congr_fun hab x

theorem cc_sq {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] {σ : G F Ω}
    (h : ∃ j : Ω →+* ℂ, ∀ x, j (σ x) = starRingEnd ℂ (j x)) : σ * σ = 1 := by
  obtain ⟨j, hj⟩ := h
  ext x
  apply j.injective
  show j (σ (σ x)) = j x
  rw [hj, hj, Complex.conj_conj]

theorem galEmb_comp (K L Ω : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Field Ω] [CharZero Ω]
    [Algebra K Ω] [Algebra L Ω] [Algebra K L] [IsScalarTower K L Ω] (s : G L Ω) :
    galEmb ℚ K Ω (galEmb K L Ω s) = galEmb ℚ L Ω s := rfl

theorem irr_of_matIrr {Γ Γ' k : Type} [Group Γ] [Group Γ'] [Field k] {n : ℕ} (hn : 1 ≤ n) (U : Subgroup Γ)
    (a : Γ → Matrix (Fin n) (Fin n) k) (ha : U3.MatIrr U a) (φ : Γ' →* Γ) (hφ : U ≤ φ.range) (r : Γ' →* GL (Fin n) k)
    (hr : ∀ s, (r s).val = a (φ s)) : Af.IsIrr r := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨top_ne_bot, fun _ _ _ => trivial, fun W _ hW => ha W fun g hg v hv => ?_⟩
  obtain ⟨s, rfl⟩ := hφ hg
  rw [← hr]
  exact hW s v hv

theorem locHom {l : ℕ} [Fact l.Prime] (c : Coef l) (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A]
    [Module.Finite c.O A] : IsLocalHom (algebraMap c.O A) := by
  haveI := c.dvr
  haveI : FaithfulSMul c.O A := (faithfulSMul_iff_algebraMap_injective c.O A).2
    (fun x y hxy => Subtype.ext (congrArg (fun z : A => (z : PadicAlgCl l)) hxy))
  infer_instance

theorem galL_le {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O]
    {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} {L : Type} [Field L] [NumberField L]
    [Algebra L Ω] {Φ : Fr.Frame l (ResidueField O)} (k : Pr.GalLink η Ψ σ g₁ B M L Φ) : galOf ℚ L Ω ≤ η.ker :=
  k.gal ▸ inf_le_right

end UpperTheory.V.Th.Db
