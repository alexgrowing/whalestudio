import Formalism.SharpRestriction.LevelLetterCocycles.BaseChangeMapMemLattice
import Formalism.SharpRestriction.LevelLetterCocycles.Imports
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CoefExt
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.BaseCoefJump

noncomputable section

open Classical TensorProduct

namespace Formalism.MainNotions.UnusedSlot80.BCW

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

section Crys

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

def matOf {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) :
    G →* Matrix (Fin k) (Fin k) LL :=
  (LinearMap.toMatrixAlgEquiv b).toAlgHom.toRingHom.toMonoidHom.comp ρ

theorem matOf_equiv {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V) (g : G) (x : V) :
    b.equivFun (ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL ≃ₐ[LL] _).toAlgHom.toRingHom.toMonoidHom.comp
        (matOf b ρ)) g (b.equivFun x) := by
  simp only [matOf, MonoidHom.coe_comp, Function.comp_apply, Module.Basis.equivFun_apply]
  change ⇑(b.repr ((ρ g) x)) = (Matrix.toLinAlgEquiv' (LinearMap.toMatrix b b (ρ g))) ⇑(b.repr x)
  rw [Matrix.toLinAlgEquiv'_apply, LinearMap.toMatrix_mulVec_repr]

theorem isCrys_bρ {k : ℕ} (b : Module.Basis (Fin k) LL V) (ρ : Representation LL G V)
    (h : IsCrys PD ρ) : IsCrys PD (bρ LL' ρ) := by
  have h1 := Formalism.MainNotions.N.K.Norm.isCrys_congr PD b.equivFun (matOf_equiv b ρ) h
  have h2 := coefficient_crystal_generation PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) h1
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  refine Formalism.MainNotions.N.K.Norm.isCrys_congr PD b'.equivFun.symm (fun g y => ?_) h2
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  apply b'.equivFun.injective
  rw [LinearEquiv.apply_symm_apply]
  have e1 := matOf_equiv b' (bρ LL' ρ) g (b'.equivFun.symm y)
  rw [LinearEquiv.apply_symm_apply] at e1
  rw [e1]
  simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
  rfl

end Crys

section LocC

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem crysLat_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) (hT : Formalism.MainNotions.WachCoordinates.CrysLat PD T) :
    Formalism.MainNotions.WachCoordinates.CrysLat PD (bLoc (O' := O') hc hO' T) :=
  ⟨(bLoc (O' := O') hc hO' T).fdim, (bLoc (O' := O') hc hO' T).mtop, (bLoc (O' := O') hc hO' T).cont,
    isCrys_bρ PD (Module.finBasis LL T.V) T.ρ hT.2.2.2⟩

theorem finrank_b (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (T : LocLat G Qp LL O) :
    Module.finrank LL' (bLoc (O' := O') hc hO' T).V = Module.finrank LL T.V :=
  Module.finrank_baseChange

end LocC

section Jmp

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' : Type} [Field LL] [Field LL'] [Algebra Qp LL]
    [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem isJumpV_bρ (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen) {k : ℕ} (b : Module.Basis (Fin k) LL V)
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    IsJumpV PD (bρ LL' ρ) ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a ↔ IsJumpV PD ρ τ a := by
  let b' : Module.Basis (Fin k) LL' (LL' ⊗[LL] V) := Algebra.TensorProduct.basis LL' b
  have hm : ∀ g, matOf b' (bρ LL' ρ) g =
      (IsScalarTower.toAlgHom Qp LL LL').mapMatrix (matOf b ρ g) := by
    intro g
    change LinearMap.toMatrix b' b' ((ρ g).baseChange LL') = (LinearMap.toMatrix b b (ρ g)).map _
    rw [LinearMap.toMatrix_baseChange]
    rfl
  have e1 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b.equivFun (matOf_equiv b ρ) τ a
  have e2 := hJ PD (IsScalarTower.toAlgHom Qp LL LL') (matOf b ρ) τ a
  have he' : ∀ g x, b'.equivFun (bρ LL' ρ g x) =
      ((Matrix.toLinAlgEquiv' : Matrix (Fin k) (Fin k) LL' ≃ₐ[LL'] _).toAlgHom.toRingHom.toMonoidHom.comp
        ((IsScalarTower.toAlgHom Qp LL LL').mapMatrix.toRingHom.toMonoidHom.comp (matOf b ρ))) g
        (b'.equivFun x) := by
    intro g x
    rw [matOf_equiv b' (bρ LL' ρ) g x]
    simp only [MonoidHom.coe_comp, Function.comp_apply, hm]
    rfl
  have e3 := Formalism.MainNotions.N.K.Norm.isJumpV_congr PD b'.equivFun he' ((IsScalarTower.toAlgHom Qp LL LL').comp τ) a
  rw [e3, ← e2, ← e1]

end Jmp

section Assemble

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) {LL LL' O O' : Type} [Field LL] [Field LL']
    [Algebra Qp LL] [Algebra Qp LL'] [Algebra LL LL'] [IsScalarTower Qp LL LL']
    [TopologicalSpace LL] [TopologicalSpace LL'] [IsTopologicalRing LL'] [CommRing O] [IsDomain O]
    [Algebra O LL] [IsFractionRing O LL] [CommRing O'] [Algebra O' LL'] [Algebra O O'] [Algebra O LL']
    [IsScalarTower O O' LL'] [IsScalarTower O LL LL']

theorem bcAt_of (hc : Continuous (algebraMap LL LL')) (hO' : Function.Injective (algebraMap O' LL'))
    (hJ : Formalism.MainNotions.N.GlobalTheory.CoefJumpGen)
    (hL : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ e, (bHom (O' := O') hc hO' F).LiftF PD e → F.LiftF PD e)
    (hC : ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Formalism.MainNotions.WachCoordinates.CrysLat PD T₁ →
      Formalism.MainNotions.WachCoordinates.CrysLat PD T₂ → F.Onto → ∀ x, Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD (bHom (O' := O') hc hO' F) x → Formalism.MainNotions.TruncatedSeriesCountingBounds.ColLeR PD F x) :
    Formalism.MainNotions.WachCoordinates.BCAt PD (LL := LL) (O := O) (O' := O') (IsScalarTower.toAlgHom Qp LL LL') := by
  intro T₁ T₂ F h₁ h₂ hF
  refine ⟨bLoc hc hO' T₁, bLoc hc hO' T₂, bHom hc hO' F, crysLat_b PD hc hO' T₁ h₁,
    crysLat_b PD hc hO' T₂ h₂, bHom_onto hc hO' F hF, fun τ a => ⟨?_, ?_⟩, finrank_b hc hO' T₂,
    hL T₁ T₂ F h₁ h₂ hF, hC T₁ T₂ F h₁ h₂ hF⟩
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₁.V) T₁.ρ τ a
  · exact isJumpV_bρ PD hJ (Module.finBasis LL T₂.V) T₂.ρ τ a

end Assemble

end Formalism.MainNotions.UnusedSlot80.BCW
