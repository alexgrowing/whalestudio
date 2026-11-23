import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.CubeCechEquivalences.CechCubeBaseChange.BcSumSingle
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.OmegaPullSCompRight
import Development.WeilBound.CoreStatements.PadicHodgeComparison.GoodCoverEigenspaces.Leaves
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh GlobalTheory.CechDR PositivityTheory.AutomorphicGaloisHodgeTate.G8.HBC UpperTheory.Gal.G3.HN
open KaehlerDifferential
open scoped TensorProduct

namespace UpperTheory.Gal.G3

private theorem isBC_iff {k k' : Type} [CommRing k] [CommRing k'] [Algebra k k'] {J : Type}
    (e : Module.Basis J k k') {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N]
    [Module k' N] [Module k N] [IsScalarTower k k' N] (ψ : M →ₛₗ[algebraMap k k'] N)
    (f : M →ₗ[k] N) (hf : ∀ m, f m = ψ m) : IsBC e ψ ↔ IsBaseChange k' f := by
  classical
  let L : k' ⊗[k] M →ₗ[k] N := TensorProduct.lift
    (((Algebra.linearMap k' (Module.End k' (M →ₗ[k] N))).flip f).restrictScalars k)
  let E := TensorProduct.equivFinsuppOfBasisLeft (N := M) e
  have hL : bcSum e ψ = L.toAddMonoidHom.comp E.symm.toLinearMap.toAddMonoidHom :=
    Finsupp.addHom_ext fun j m ↦ by
      rw [bcSum_single]
      simp [L, E, hf]
  change Function.Bijective (bcSum e ψ) ↔ Function.Bijective L
  rw [hL]
  exact Function.Bijective.of_comp_iff L E.symm.bijective

private theorem isBaseChange_bottom {k k' B B' : Type} [CommRing k] [CommRing k'] [CommRing B]
    [CommRing B'] [Algebra k k'] [Algebra k B] [Algebra k B'] [Algebra B B'] [Algebra k' B']
    [IsScalarTower k B B'] [IsScalarTower k k' B'] [Algebra.IsPushout k k' B B'] {P Q : Type*}
    [AddCommGroup P] [Module B P] [Module k P] [IsScalarTower k B P] [AddCommGroup Q] [Module B' Q]
    [Module B Q] [Module k' Q] [Module k Q] [IsScalarTower B B' Q] [IsScalarTower k' B' Q]
    [IsScalarTower k k' Q] [IsScalarTower k B Q] {u : P →ₗ[B] Q} (hu : IsBaseChange B' u) :
    IsBaseChange k' (u.restrictScalars k) :=
  IsBaseChange.of_equiv
    ((Algebra.IsPushout.cancelBaseChange k k' B B' P).symm ≪≫ₗ hu.equiv.restrictScalars k')
    fun p ↦ by simp

private theorem isBaseChange_map (k k' B B' : Type) [CommRing k] [CommRing k'] [CommRing B]
    [CommRing B'] [Algebra k k'] [Algebra k B] [Algebra k B'] [Algebra B B'] [Algebra k' B']
    [IsScalarTower k B B'] [IsScalarTower k k' B'] [Algebra.IsPushout k k' B B'] :
    IsBaseChange B' (KaehlerDifferential.map k k' B B') := by
  refine IsBaseChange.of_equiv (tensorKaehlerEquiv k k' B B') fun ω ↦ ?_
  have h : ((tensorKaehlerEquiv k k' B B').toLinearMap.restrictScalars B) ∘ₗ
      (TensorProduct.mk B B' Ω[B⁄k] 1) = KaehlerDifferential.map k k' B B' := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    simp [tensorKaehlerEquiv_tmul_D]
  exact LinearMap.congr_fun h ω

theorem jHForms : P_forms := by
  intro k k' _ _ _ J e B B' _ _ _ _ α hα hB j
  letI : Algebra B B' := α.toAlgebra
  letI : Algebra k B' := ((algebraMap k' B').comp (algebraMap k k')).toAlgebra
  haveI : IsScalarTower k k' B' := .of_algebraMap_eq fun _ ↦ rfl
  haveI : IsScalarTower k B B' := .of_algebraMap_eq fun r ↦ (hα.map_algebraMap r).symm
  haveI : Algebra.IsPushout k k' B B' := ⟨(isBC_iff e (semiSl hα) _ fun _ ↦ rfl).1 hB⟩
  have hone (ω : Ω[B⁄k]) : hα.m1 ω = KaehlerDifferential.map k k' B B' ω := by
    induction ω using ind1 with
    | h b c => rw [hα.oneFormMap_smul_semilinear, hα.m1_D, map_smul, map_D]; rfl
    | h0 => simp
    | ha x y hx hy => simp only [map_add, hx, hy]
  let pull : Om k B j →ₗ[B] Om k' B' j :=
    { toFun := hα.mOm j
      map_add' := map_add _
      map_smul' := fun b x ↦ hα.mOm_smul b x }
  have hpull : exteriorPowerMapOver B' j (KaehlerDifferential.map k k' B B') = pull := by
    apply exteriorPower.linearMap_ext
    ext1 v
    simp only [LinearMap.compAlternatingMap_apply, exteriorPowerMapOver_ιMulti]
    refine Subtype.ext ?_
    change _ = hα.mDR (exteriorPower.ιMulti B j v : DR k B)
    rw [exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
      ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
    congr 2
    funext i
    exact ((hα.mDR_ι (v i)).trans (congrArg ι1 (hone (v i)))).symm
  exact (isBC_iff e (hα.mOm j) _ fun x ↦ LinearMap.congr_fun hpull x).2
    (isBaseChange_bottom (k := k) (k' := k') (B := B) (B' := B')
      (TopForm.isBaseChange_exteriorPower (isBaseChange_map k k' B B') j))

end UpperTheory.Gal.G3

end
