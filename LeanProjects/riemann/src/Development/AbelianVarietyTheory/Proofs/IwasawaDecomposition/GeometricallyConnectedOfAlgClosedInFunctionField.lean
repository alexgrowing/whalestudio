import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LinearDisjointAlgebraicClosure

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open scoped TensorProduct

namespace GlobalTheory.GeomConnFn

theorem isConnected_preimage {F : Type} [Field F] [CharZero F] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp F)
    [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range)
    (K : Type) [Field K] [Algebra F K] (U : X.Opens) (hU : IsAffineOpen U) (hx : genericPoint X ∈ U) :
    _root_.IsConnected
      (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) ⁻¹' (U : Set X)) := by
  let : Algebra F Γ(X, U) := (algX p U).toAlgebra
  let : Algebra F X.functionField := (GlobalTheory.Cartier.constFn p).toAlgebra
  have hft : (algX p U).FiniteType :=
    (HasRingHomProperty.appLE @LocallyOfFiniteType p inferInstance ⟨⊤, isAffineOpen_top _⟩ ⟨U, hU⟩
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)).comp
      (RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv.surjective)
  have : Algebra.FiniteType F Γ(X, U) := hft
  let j : Γ(X, U) →ₐ[F] X.functionField :=
    { GlobalTheory.Cartier.fnOf U hx with
      commutes' := fun a => RingHom.congr_fun (GlobalTheory.Cartier.fnOf_comp_algX p U hx) a }
  have : IsDomain (K ⊗[F] Γ(X, U)) :=
    GlobalTheory.GeomConn.isDomain_tensor j (GlobalTheory.Cartier.fnOf_injective U hx) (fun a ha => h a ha) K
  have : IsDomain (Γ(X, U) ⊗[F] K) := (Algebra.TensorProduct.comm F Γ(X, U) K).toMulEquiv.isDomain
  have hg : hU.fromSpec ≫ p = Spec.map (CommRingCat.ofHom (algebraMap F Γ(X, U))) := by
    have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU
      (show U ≤ p ⁻¹ᵁ ⊤ from le_top)
    rw [← h, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
    rfl
  have h1 : IsIntegral (pullback (hU.fromSpec ≫ p) (Spec.map (CommRingCat.ofHom (algebraMap F K)))) := by
    rw [hg]
    exact IsIntegral.of_isIso (pullbackSpecIso F Γ(X, U) K).inv
  have h2 := IsIntegral.of_isIso
    (pullbackRightPullbackFstIso p (Spec.map (CommRingCat.ofHom (algebraMap F K))) hU.fromSpec).inv
  rw [← hU.range_fromSpec, ← Scheme.Pullback.range_snd]
  exact isConnected_range (Scheme.Hom.continuous _)

theorem geometricallyConnected_of_locallyOfFiniteType {F : Type} [Field F] [CharZero F] {X : Scheme.{0}}
    [IsIntegral X] (p : X ⟶ Sp F) [LocallyOfFiniteType p]
    (h : ∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) →
      a ∈ (GlobalTheory.Cartier.constFn p).range) : GeometricallyConnected p := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.2 fun K _ _ => ?_⟩
  have : Surjective (Spec.map (CommRingCat.ofHom (algebraMap F K))) :=
    ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  obtain ⟨x₀, hx₀⟩ := (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K)))).surjective (genericPoint X)
  refine connectedSpace_iff_univ.2 ⟨⟨x₀, trivial⟩, isPreconnected_of_forall x₀ fun y _ => ?_⟩
  obtain ⟨U, hU, hy, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (Opens.mem_top (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap F K))) y))
  have hg := GlobalTheory.Cartier.gen_mem hy
  refine ⟨_, Set.subset_univ _, ?_, hy, (isConnected_preimage p h K U hU hg).isPreconnected⟩
  rw [Set.mem_preimage, hx₀]
  exact hg

theorem geometricallyConnected_of_algClosed_in_functionField : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) [Smooth p], IsProjOver p → (∀ a : X.functionField, (∃ P : Polynomial F, P ≠ 0 ∧ P.eval₂ (GlobalTheory.Cartier.constFn p) a = 0) → a ∈ (GlobalTheory.Cartier.constFn p).range) → GeometricallyConnected p :=
  fun _ _ _ _ _ p _ _ h => geometricallyConnected_of_locallyOfFiniteType p h

end GlobalTheory.GeomConnFn
