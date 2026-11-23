import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegFunctionFieldEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgFunctionField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldOneVariableTranscendentalFiniteAndE

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc IntermediateField

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Nef.CurveFF

theorem isFF_of_trdeg_eq_one {k F : Type} [Field k] [Field F] [Algebra k F] [Algebra.EssFiniteType k F]
    (h : Algebra.trdeg k F = 1) : IsFF k F := by
  have hna : ¬ Algebra.IsAlgebraic k F := fun ha => by
    rw [trdeg_eq_zero_iff.mpr ha] at h; exact zero_ne_one h
  obtain ⟨x, hx⟩ : ∃ x : F, Transcendental k x := by
    by_contra hc
    push_neg at hc
    exact hna ⟨fun x => by simpa [Transcendental] using hc x⟩
  exact ⟨x, hx, finiteDimensional_adjoin_of_trdeg_le_one h.le x hx⟩

theorem isFF_of_stalk (k K : Type) [Field k] [Field K] [Algebra k K] (C : Scheme.{0}) [IsIntegral C]
    [Algebra k Γ(C, ⊤)] (hp : IsProjOver (strHom k C)) (hd : topologicalKrullDim C = 1)
    (y : C) (hy : y = genericPoint C) (ψ : C.presheaf.stalk y ⟶ CommRingCat.of K)
    (hψ : Function.Surjective ψ.hom)
    (hc : Spec.map ψ ≫ C.fromSpecStalk y ≫ strHom k C = spMap (algebraMap k K)) : IsFF k K := by
  subst hy
  let φ : k →+* C.functionField := (Spec.preimage (C.fromSpecStalk (genericPoint C) ≫ strHom k C)).hom
  have hφ : C.fromSpecStalk (genericPoint C) ≫ strHom k C = spMap φ := (Spec.map_preimage _).symm
  letI : Algebra k C.functionField := φ.toAlgebra
  have htr : Algebra.trdeg k C.functionField = 1 := by
    have := FunctionFieldTrdeg.trdeg_functionField_eq k C (strHom k C) 1 hp (by simpa using hd) φ hφ
    simpa using this
  have hfg : (⊤ : IntermediateField k C.functionField).FG :=
    FGFun.fg_functionField k C (strHom k C) hp k C.functionField φ (𝟙 _) (RingHom.id _) (by simp [hφ])
  haveI : Algebra.EssFiniteType k C.functionField := IntermediateField.fg_top_iff.mp hfg
  let ψ' : C.functionField →+* K := ψ.hom
  have hinj : Function.Injective ψ' := ψ'.injective
  have hcomm : ∀ c : k, ψ' (φ c) = algebraMap k K c := by
    rw [hφ] at hc
    have h1 : Spec.map (CommRingCat.ofHom φ ≫ ψ) = Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
      rw [Spec.map_comp]; exact hc
    have h2 := Spec.map_injective h1
    intro c
    exact congrArg (fun f => f.hom c) h2
  let e : C.functionField ≃ₐ[k] K :=
    AlgEquiv.ofBijective { ψ' with commutes' := hcomm } ⟨hinj, hψ⟩
  haveI : Algebra.EssFiniteType k K := (Algebra.EssFiniteType.iff_of_algEquiv e).mp inferInstance
  exact isFF_of_trdeg_eq_one (e.trdeg_eq ▸ htr)

theorem isFF_of_isGenOver : ∀ (k K : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  IsFF k K := by
  intro k K _ _ _ _ _ C _ x hx
  obtain ⟨⟨hs, hp, hg⟩, ⟨hdom, hpre⟩, hxs⟩ := hx
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hs hg
  let p : Sp K := IsLocalRing.closedPoint (CommRingCat.of K)
  haveI : Nonempty C := ⟨x p⟩
  have hd : topologicalKrullDim C = 1 := LieSemineg.dim_curve hs
  have hgen : x p = genericPoint C := by
    have hr : Set.range x = {x p} := by
      ext w
      constructor
      · rintro ⟨v, rfl⟩
        rw [Set.mem_singleton_iff, Subsingleton.elim v p]
      · rintro rfl
        exact ⟨p, rfl⟩
    refine ((genericPoint_spec C).eq ?_).symm
    rw [isGenericPoint_def, ← hr]
    exact x.denseRange.closure_range
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo x).hom := by
    unfold Scheme.stalkClosedPointTo
    exact (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (.of K)).hom).2.comp
      (x.stalkMap_surjective _)
  refine isFF_of_stalk k K C hp hd _ hgen (Scheme.stalkClosedPointTo x) hsurj ?_
  rw [← Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hxs]

end GlobalTheory.Nef.CurveFF
