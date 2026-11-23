import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

namespace GlobalTheory.CompanionTheory.GE.PSupp

theorem cokernel_supportedIn_preimage : ∀ {X : Scheme.{0}} (O : X.Opens) {P : X.Modules} {E : (O : Scheme.{0}).Modules}, P.IsQuasicoherent → E.IsQuasicoherent → ∀ f : P.restrict O.ι ⟶ E, Epi f → ∀ Bb : Subobject P, ∀ B : Subobject E, (B : (O : Scheme.{0}).Modules).IsQuasicoherent → (∀ (W : (O : Scheme.{0}).Opens), IsAffineOpen W → secs B W = (fun x => f.app W ((P.restrictAppIso O.ι W).inv x)) '' secs Bb (O.ι ''ᵁ W)) → ∀ (C : Set X), (∀ U : X.Opens, IsAffineOpen U → Disjoint (U : Set X) C → secs Bb U = Set.univ) → Scheme.Modules.SupportedIn (cokernel B.arrow) (O.ι.base ⁻¹' C) := by
  intro X O P E hP hE f hf Bb B hB hsec C hC
  haveI : P.IsQuasicoherent := hP
  haveI : E.IsQuasicoherent := hE
  haveI : Epi f := hf
  refine GlobalTheory.CompanionTheory.GE.Comb.supportedIn_of_secs_eq_univ hE hB fun W hW hd => ?_
  have hWi : IsAffineOpen (O.ι ''ᵁ W) := hW.image_of_isOpenImmersion O.ι
  have hdis : Disjoint ((O.ι ''ᵁ W : X.Opens) : Set X) C := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨y, hy, rfl⟩ hyC
    exact Set.disjoint_left.1 hd hy hyC
  rw [hsec W hW, hC _ hWi hdis, Set.image_univ]
  refine Function.Surjective.range_eq fun y => ?_
  obtain ⟨z, rfl⟩ := surjective_app_of_epi f hW y
  refine ⟨(P.restrictAppIso O.ι W).hom z, ?_⟩
  simp

end GlobalTheory.CompanionTheory.GE.PSupp
