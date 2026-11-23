import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt

set_option autoImplicit false

namespace GlobalTheory.FrobFilt

theorem sections_leftExact {X : Scheme.{0}} (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (W : X.Opens) : Function.Injective (S.f.app W) ∧
      ∀ x : Γ(S.X₂, W), S.g.app W x = 0 → ∃ a : Γ(S.X₁, W), S.f.app W a = x := by
  let G : X.Modules ⥤ Ab := Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (Opposite.op W)
  haveI : PreservesLimitsOfSize.{0, 0} ((evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab).obj (Opposite.op W)) :=
    ⟨fun {J} _ => evaluation_preservesLimitsOfShape _⟩
  haveI : PreservesLimits G := comp_preservesLimits _ _
  haveI : PreservesFiniteLimits G := inferInstance
  haveI : G.PreservesZeroMorphisms := inferInstance
  haveI : Mono S.f := hS.mono_f
  have hM : Mono (G.map S.f) := inferInstance
  have hE : (S.map G).Exact := hS.exact.map_of_mono_of_preservesKernel G inferInstance inferInstance
  refine ⟨(AddCommGrpCat.mono_iff_injective _).1 hM, ?_⟩
  exact (ShortComplex.ab_exact_iff _).1 hE

theorem noEmb_of_shortExact (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (B : GlobalTheory.Vert.Model O) (S : ShortComplex B.X.Modules) (hS : S.ShortExact)
    (h₁ : NoEmb B S.X₁) (h₃ : NoEmb B S.X₃) : NoEmb B S.X₂ := by
  intro U V hVU hV
  let i : (Opposite.op U : B.X.Opensᵒᵖ) ⟶ Opposite.op V := (homOfLE hVU).op
  have natg : ∀ u : Γ(S.X₂, U), S.g.app V ((Scheme.Modules.presheaf S.X₂).map i u) =
      (Scheme.Modules.presheaf S.X₃).map i (S.g.app U u) := fun u =>
    ConcreteCategory.congr_hom (S.g.mapPresheaf.naturality i) u
  have natf : ∀ u : Γ(S.X₁, U), S.f.app V ((Scheme.Modules.presheaf S.X₁).map i u) =
      (Scheme.Modules.presheaf S.X₂).map i (S.f.app U u) := fun u =>
    ConcreteCategory.congr_hom (S.f.mapPresheaf.naturality i) u
  have hU := sections_leftExact S hS U
  have hVi := sections_leftExact S hS V
  refine (injective_iff_map_eq_zero ((Scheme.Modules.presheaf S.X₂).map i).hom).2 ?_
  intro s hs
  have hs' : (Scheme.Modules.presheaf S.X₂).map i s = 0 := hs
  have e3 : S.g.app U s = 0 := by
    apply h₃ U V hVU hV
    rw [← natg, hs']
    simp
  obtain ⟨a, rfl⟩ := hU.2 s e3
  have ea : a = 0 := by
    apply h₁ U V hVU hV
    apply hVi.1
    rw [natf, hs']
    simp
  subst ea
  simp

end GlobalTheory.FrobFilt
