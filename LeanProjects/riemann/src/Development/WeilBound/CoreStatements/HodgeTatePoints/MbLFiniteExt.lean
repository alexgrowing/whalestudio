import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.WeilBound.CoreStatements.HodgeTatePoints.FinClosure
import Development.WeilBound.CoreStatements.HodgeTatePoints.MaBase

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

noncomputable section

namespace PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite

theorem mem_regAt_genPt {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (a : Ω) : a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨s, hs⟩ := h.bij.2 a
  refine ⟨s, ?_⟩
  have e : X.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap]
  rw [e]
  erw [Category.id_comp]
  exact hs

theorem exists_eq_div_chRing {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type}
    [Finite κ] {x : κ → Ω} (M : PModel o x) {c : κ} (hc : x c ≠ 0) (a : Ω) :
    ∃ u ∈ chRing o x c, ∃ v ∈ chRing o x c, a = u / v := by
  have hp : InChart M.ξ x c ⟨genPt M.ξ, specializes_rfl⟩ :=
    ⟨hc, fun c' => mem_regAt_genPt M.tie.gen _⟩
  obtain ⟨u, hu, v, hv, -, e⟩ :=
    ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hp).2 a).1 (mem_regAt_genPt M.tie.gen a)
  exact ⟨u, hu, v, hv, e⟩

theorem finite_integralClosure_chRing {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type}
    [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω']
    [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ)
    (hc : x c ≠ 0) :
    Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c)
      (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') := by
  let φ : Ω →ₐ[o] Ω' := IsScalarTower.toAlgHom o Ω Ω'
  have hφ : Function.Injective φ := φ.toRingHom.injective
  have hmap : (chRing o x c).map φ = chRing o (fun k => algebraMap Ω Ω' (x k)) c := by
    simp only [chRing]
    rw [AlgHom.map_adjoin, ← Set.range_comp]
    congr 2
    ext j
    simp [φ]
  let e : chRing o x c ≃ₐ[o] chRing o (fun k => algebraMap Ω Ω' (x k)) c :=
    ((chRing o x c).equivMapOfInjective φ hφ).trans (Subalgebra.equivOfEq _ _ hmap)
  have he : ∀ a, ((e a : chRing o (fun k => algebraMap Ω Ω' (x k)) c) : Ω') =
      algebraMap Ω Ω' (a : Ω) := fun a => rfl
  haveI : Algebra.FiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) := by
    rw [← Subalgebra.fg_iff_finiteType]
    exact Subalgebra.fg_def.2 ⟨_, Set.finite_range _, rfl⟩
  haveI : Algebra.EssFiniteType o (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.of_finiteType _ _
  haveI : Algebra.EssFiniteType ℤ (chRing o (fun k => algebraMap Ω Ω' (x k)) c) :=
    Algebra.EssFiniteType.comp ℤ o _
  letI : Algebra (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    ((chRing o x c).val.toRingHom.comp e.symm.toRingEquiv.toRingHom).toAlgebra
  have hmapΩ : ∀ a : chRing o x c,
      algebraMap (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω (e a) = (a : Ω) := by
    intro a
    change ((e.symm (e a) : chRing o x c) : Ω) = a
    rw [AlgEquiv.symm_apply_apply]
  haveI : IsScalarTower (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω Ω' :=
    IsScalarTower.of_algebraMap_eq fun a => by
      obtain ⟨b, rfl⟩ := e.surjective a
      rw [hmapΩ]
      exact he b
  haveI : FaithfulSMul (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 fun a b h => by
      obtain ⟨a, rfl⟩ := e.surjective a
      obtain ⟨b, rfl⟩ := e.surjective b
      rw [hmapΩ, hmapΩ] at h
      rw [Subtype.ext h]
  haveI : IsFractionRing (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω :=
    IsFractionRing.of_field _ _ fun z => by
      obtain ⟨u, hu, v, hv, rfl⟩ := exists_eq_div_chRing M hc z
      exact ⟨e ⟨u, hu⟩, e ⟨v, hv⟩, by rw [hmapΩ, hmapΩ]⟩
  exact PositivityTheory.HtPt.Mb.fin_closure _ Ω Ω'

end PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.finite_ext : ∀ {o : Type} [CommRing o] [Algebra.EssFiniteType ℤ o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [FiniteDimensional Ω Ω'] [Algebra o Ω'] [IsScalarTower o Ω Ω'] (c : κ), x c ≠ 0 → Module.Finite (chRing o (fun k => algebraMap Ω Ω' (x k)) c) (integralClosure (chRing o (fun k => algebraMap Ω Ω' (x k)) c) Ω') :=
  @PositivityTheory.HtPt.Mb.LFiniteExt.ChartFinite.finite_integralClosure_chRing
