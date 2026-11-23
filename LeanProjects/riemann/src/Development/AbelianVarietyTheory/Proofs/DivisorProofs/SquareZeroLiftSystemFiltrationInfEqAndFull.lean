import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealCochainOfCoboundaryConstantsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLocIsoSquareZeroSmoothLiftSystemsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocIsoTransportCochainsInIdealStatement
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

theorem mem_map_algebraMap_of_algHom {R : Type} [CommRing R] {I : Ideal R} {A B : Type} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (e : A →ₐ[R] B) {x : A} (hx : x ∈ I.map (algebraMap R A)) :
    e x ∈ I.map (algebraMap R B) := by
  have := Ideal.mem_map_of_mem (e : A →+* B) hx
  rwa [Ideal.map_map, AlgHom.comp_algebraMap] at this

theorem K_inf_eq_and_full : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀)
    (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Const s₀ →
    ∀ S S' : Sys I π s₀, S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) = S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ∧
      (S.Full hI → S'.Full hI) := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ hc
  have key : ∀ S S' : Sys I π s₀,
      S.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) ≤ S'.K hI ⊓ I • (⊤ : Submodule R (Cr hI π s₀)) := by
    intro S S' c hc'
    obtain ⟨hcK, hcI⟩ := hc'
    obtain ⟨Φ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S S'
    obtain ⟨-, h2, h3⟩ := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀ S S' Φ
    obtain ⟨z, z', hz, hmk, hmk', hzz⟩ := h3 c hcI
    have h0 : H1.mk _ z = 0 := hmk.trans (LinearMap.mem_ker.1 hcK)
    obtain ⟨g, hg, hdg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hc S z hz h0
    refine ⟨LinearMap.mem_ker.2 ?_, hcI⟩
    rw [← hmk']
    refine H1.mk_eq_zero.2 ⟨fun W ↦ Φ.φ W (g W), ?_⟩
    funext U V a
    rw [h2 g hg U V a, hdg, hzz]
  refine fun S S' ↦ ⟨le_antisymm (key S S') (key S' S), fun hF z₁' hz₁' ↦ ?_⟩
  obtain ⟨Ψ⟩ := GlobalTheory.T.nonempty_locIso_squareZeroSmoothLiftSystems R R₀ I hI π hπ hk X₀ s₀ S' S
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.locIso_transport_cochains_in_ideal R R₀ I hI π hπ hk X₀ s₀ S' S Ψ
  obtain ⟨z₁, hz₁, hz₁e⟩ := h1 z₁' hz₁'
  obtain ⟨c, hcI, hc₁⟩ := hF z₁ hz₁
  obtain ⟨y', y, hy'I, hy', hy, hyy⟩ := h3 c hcI
  have hyI : S.IsIdealValuedLiftSystemCocycle y := fun U V a ↦ by
    rw [hyy]; exact mem_map_algebraMap_of_algHom (Ψ.φ V : S'.F.obj V →ₐ[R] S.F.obj V) (hy'I U V a)
  have hd : H1.mk _ (y - z₁) = 0 := by rw [map_sub, hy, hc₁, sub_self]
  obtain ⟨g, hg, hdg⟩ := GlobalTheory.T.exists_ideal_cochain_of_coboundary_constants R R₀ I hI π hπ hk X₀ s₀ hc S (y - z₁)
    (fun U V a ↦ Ideal.sub_mem _ (hyI U V a) (hz₁ U V a)) hd
  let g' : C0 S'.F := fun W ↦ (Ψ.φ W).symm (g W)
  have hg' : S'.IsIdealValuedLiftSystemCochain g' := fun W ↦
    mem_map_algebraMap_of_algHom ((Ψ.φ W).symm : S.F.obj W →ₐ[R] S'.F.obj W) (hg W)
  have hgg : (fun W ↦ Ψ.φ W (g' W)) = g := funext fun W ↦ AlgEquiv.apply_symm_apply _ _
  refine ⟨c, hcI, hy'.symm.trans (H1.mk_eq_mk.2 ⟨g', ?_⟩)⟩
  funext U V a
  apply (Ψ.φ V).injective
  have e := h2 g' hg' U V a
  rw [hgg, hdg] at e
  rw [← e]
  show y.1 U V a - z₁.1 U V a = Ψ.φ V (y'.1 U V a - z₁'.1 U V a)
  rw [map_sub, hyy, hz₁e]
end GlobalTheory.LiftSys
