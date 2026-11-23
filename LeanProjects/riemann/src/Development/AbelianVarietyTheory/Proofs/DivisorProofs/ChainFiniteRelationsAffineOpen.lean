import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibilityBaseChangeProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VectorBundleSectionsFiniteProjectiveStatement

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison
open GlobalTheory.Twist (resM)
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.GroupBplus (AffOp)
open GlobalTheory.RingChain (RChain mv baseOf Qt IsFrobLin)
open GlobalTheory.ChainPts.PullHT (pullA)
open GlobalTheory.PerfdLat (piMap)
open scoped TensorProduct Pointwise
open GlobalTheory.ChainPts
open GlobalTheory.ChainDesc

namespace GlobalTheory.ChainDesc

set_option maxHeartbeats 1000000 in

theorem exists_isDown : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (Λ : Type) [CommRing Λ] (h o r r' : ℕ) (Lie Om : AM B Λ) (π : Γ(B.X, ⊤)) (γ : ℕ → Γ(B.X, ⊤)) (C : ChainsBp p h o Lie Om π γ), GlobalTheory.VB.IsVB Lie.V r → GlobalTheory.VB.IsVB Om.V r' → ∀ (U : AffOp B.X) (S : Set (Γ(Om.V, U.1) × (C U).L 0)), S.Finite → cstBp U π ≠ 0 → (∀ s ∈ S, (C U).ρ (1 ⊗ₜ s.1) = Submodule.Quotient.mk (Submodule.Quotient.mk s.2)) → ∃ T : Set U.Bp, T.Finite ∧ ∀ (B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (g : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), IsCov f g → T ⊆ Set.range (g U) → ∃ D : ChainUp p h o Lie Om π γ f (f.f ⁻¹ᵁ U.1), IsDown C f g U S D := by
  intro O _ _ _ p _ B Λ _ h o r r' Lie Om π γ C vL vO U S hS h0 hρ
  obtain ⟨fL, pL⟩ := GlobalTheory.T.vector_bundle_sections_finite_projective _ _ _ vL U.1 U.2.1
  obtain ⟨fO, pO⟩ := GlobalTheory.T.vector_bundle_sections_finite_projective _ _ _ vO U.1 U.2.1
  haveI := vL.isQuasicoherent
  haveI := vO.isQuasicoherent
  haveI : Algebra.IsIntegral Γ(B.X, U.1) U.Bp := inferInstance
  obtain ⟨T, hT, H⟩ := GlobalTheory.RingChain.RingDesc.main p Γ(B.X, U.1) U.Bp h o (resG B.X le_top π)
    (fun n => resG B.X le_top (γ n)) Γ(Lie.V, U.1) Γ(Om.V, U.1) (C U) S hS h0 hρ
  refine ⟨T, hT, fun B' f g k hTg => ?_⟩
  have hW := k.isAffineOpen U
  have hg := k.2.2.1 U
  haveI : IsDomain Γ(B'.X, f.f ⁻¹ᵁ U.1) := hg.isDomain (g U)
  haveI : IsIntegrallyClosed Γ(B'.X, f.f ⁻¹ᵁ U.1) := by
    have := k.1
    exact GlobalTheory.IsNormalScheme.isIntegrallyClosed_of_isAffineOpen hW
  letI := appLEAlgebra f.f (le_refl (f.f ⁻¹ᵁ U.1))
  letI := appLEModule f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_refl (f.f ⁻¹ᵁ U.1))
  haveI := appLE_isScalarTower f.f ((Scheme.Modules.pullback f.f).obj Lie.V) (le_refl (f.f ⁻¹ᵁ U.1))
  letI := appLEModule f.f ((Scheme.Modules.pullback f.f).obj Om.V) (le_refl (f.f ⁻¹ᵁ U.1))
  haveI := appLE_isScalarTower f.f ((Scheme.Modules.pullback f.f).obj Om.V) (le_refl (f.f ⁻¹ᵁ U.1))
  have bL := isBaseChange_pullbackSections f.f Lie.V hW U.2.1 le_rfl
  have bO := isBaseChange_pullbackSections f.f Om.V hW U.2.1 le_rfl
  have hc : ∀ a, g U (algebraMap Γ(B.X, U.1) Γ(B'.X, f.f ⁻¹ᵁ U.1) a) = algebraMap Γ(B.X, U.1) U.Bp a := fun a => by
    rw [← k.2.2.2.1]
    congr 1
    exact congr($(f.f.appLE_eq_app (U := U.1)) a)
  have hi : ∀ a : Γ(B.X, ⊤), resG B'.X le_top (f.f.appTop a) =
      algebraMap Γ(B.X, U.1) Γ(B'.X, f.f ⁻¹ᵁ U.1) (resG B.X le_top a) := fun a =>
    hg ((k.map_cst U a).trans (hc _).symm)
  obtain ⟨D, l, m, hl, hm, h1, h2, h3, h4⟩ := H Γ(B'.X, f.f ⁻¹ᵁ U.1) (g U) hg hc hTg _ _ (hi π) (fun n => hi (γ n)) _ _
    bL.equiv bO.equiv
  obtain ⟨q1, q2⟩ := GlobalTheory.T.divisibility_base_change_projective Γ(B.X, U.1) Γ(B'.X, f.f ⁻¹ᵁ U.1) U.Bp (g U) hg hc
  have eL : ∀ y, bL.equiv (1 ⊗ₜ y) = pullbackSections f.f Lie.V le_rfl y := fun y => by
    rw [bL.equiv_tmul, one_smul]
  have eO : ∀ y, bO.equiv (1 ⊗ₜ y) = pullbackSections f.f Om.V le_rfl y := fun y => by
    rw [bO.equiv_tmul, one_smul]
  refine ⟨D, l, m, fun s => (congrArg l (eL s)).symm.trans (hl s),
    fun s => (congrArg m (eO s)).symm.trans (hm s), h3, h1, h2, fun s hs => ?_, fun x hx => ?_,
    fun y hy => ?_⟩
  · obtain ⟨x, hx, hx'⟩ := h4 s hs
    exact ⟨x, hx, (congrArg D.ρ (eO s.1)).symm.trans hx'⟩
  · exact q1 _ _ (by rw [k.map_cst]; exact hx)
  · exact q2 _ _ bL.equiv l hl p y (by rw [map_natCast]; exact hy)

end GlobalTheory.ChainDesc
