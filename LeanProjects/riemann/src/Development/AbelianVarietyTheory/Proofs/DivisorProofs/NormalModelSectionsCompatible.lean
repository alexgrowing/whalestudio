import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRingOver
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PiMapMemLocalSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubmoduleMembershipLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoherentSubmoduleSectionsAffineStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveLatticeLocalBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoherentSubmodulesGlueFiniteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedLatticesFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendedLatticeFiniteProjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeNonzeroInFunctionFieldStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.PerfdLat GlobalTheory.Published GlobalTheory.GroupBplus GlobalTheory.BplusDescent GlobalTheory.LatGlue
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (resG)

namespace GlobalTheory.LatGlue

theorem glue_descended_lattices : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O] (B B' : GlobalTheory.Vert.Model O) (f : GlobalTheory.Vert.Model.Hom B' B) (K' : IntermediateField B.X.functionField (Kbar B.X)) (γ : ∀ U : AffOp B.X, Γ(B'.X, f.f ⁻¹ᵁ U.1) →+* U.Bp), IsFinite f.f → (∀ U, Function.Injective (γ U)) → (∀ (U : AffOp B.X) (a : Γ(B.X, U.1)), γ U ((f.f.app U.1).hom a) = algebraMap Γ(B.X, U.1) U.Bp a) → (∀ (U U' : AffOp B.X) (hle : U'.1 ≤ U.1) (a : Γ(B'.X, f.f ⁻¹ᵁ U.1)), γ U' ((B'.X.presheaf.map (homOfLE (f.f.preimage_mono hle)).op).hom a) = AffOp.res hle (γ U a)) → (∀ U, (γ U).range = ringOver K' U) → ∀ (J : Type) [Finite J] (h : ℕ) (L : J → ∀ U : AffOp B.X, Submodule U.Bp (Fin h → U.Bp)), (∀ j U, IsDescended K' U (L j U) ∧ ∀ x : Fin h → U.Bp, (p : U.Bp) • x ∈ L j U) → (∀ j (U U' : AffOp B.X) (hle : U'.1 ≤ U.1), L j U' = Submodule.span U'.Bp (piMap (AffOp.res hle) (Fin h) '' (L j U : Set (Fin h → U.Bp)))) → ∃ (E : J → B'.X.Modules) (ι : ∀ j, E j ⟶ freeModule B'.X (Fin h)), ∀ j, GlobalTheory.VB.IsVB (E j) h ∧ Mono (ι j) ∧ ∀ U : AffOp B.X, L j U = Submodule.span U.Bp {x | ∃ s : Γ(E j, f.f ⁻¹ᵁ U.1), ∀ i, x i = γ U (((GlobalTheory.VB.isFrame_freeFrame B'.X (Fin h)).basis le_top).repr ((ι j).app _ s) i)} := by
  intro O _ _ _ p _ _ B B' f K' γ hfin hinj halg hres hrange J _ h L hL hLres
  let V : AffOp B.X → B'.X.Opens := fun U => f.f ⁻¹ᵁ U.1
  let P : J → ∀ U : AffOp B.X, Submodule Γ(B'.X, V U) (Fin h → Γ(B'.X, V U)) :=
    fun j U => (L j U).comap (piMap (γ U) (Fin h))
  have hpK : ((p : ℕ) : Kbar B.X) ≠ 0 := GlobalTheory.T.prime_nonzero_in_function_field O p B
  have hV : ∀ U, IsAffineOpen (V U) := fun U => U.2.1.preimage f.f
  have hsurj : Function.Surjective f.f := by haveI := f.surjective; exact f.f.surjective
  have hle_of : ∀ U U' : AffOp B.X, V U' ≤ V U → U'.1 ≤ U.1 := by
    intro U U' hle x hx
    obtain ⟨y, rfl⟩ := hsurj x
    exact hle hx
  have hcov : ∀ y : B'.X, ∃ U, y ∈ V U := by
    intro y
    obtain ⟨U, hU, hy, -⟩ := QCoh.exists_affine_mem_le (U := ⊤) (f.f y) trivial
    exact ⟨⟨U, hU, ⟨⟨_, hy⟩⟩⟩, hy⟩
  have href : ∀ (U₁ U₂ : AffOp B.X) (y : B'.X), y ∈ V U₁ → y ∈ V U₂ → ∃ U₃, y ∈ V U₃ ∧ V U₃ ≤ V U₁ ∧ V U₃ ≤ V U₂ := by
    intro U₁ U₂ y h₁ h₂
    obtain ⟨U, hU, hy, hle⟩ := QCoh.exists_affine_mem_le (U := U₁.1 ⊓ U₂.1) (f.f y) ⟨h₁, h₂⟩
    exact ⟨⟨U, hU, ⟨⟨_, hy⟩⟩⟩, hy, f.f.preimage_mono (hle.trans inf_le_left), f.f.preimage_mono (hle.trans inf_le_right)⟩
  have hcomp : ∀ (j : J) (U U' : AffOp B.X) (hle : V U' ≤ V U), P j U' = Submodule.span Γ(B'.X, V U') (piMap (resG B'.X hle) (Fin h) '' (P j U : Set (Fin h → Γ(B'.X, V U)))) :=
    fun j U U' hle => GlobalTheory.T.descended_lattices_family B.X B'.X f.f K' γ hinj hres hrange h p hpK (L j) (hL j) (hLres j) U U' (hle_of U U' hle)
  have hfp : ∀ (j : J) (U : AffOp B.X), Module.Finite Γ(B'.X, V U) (P j U) ∧ Module.Projective Γ(B'.X, V U) (P j U) :=
    fun j U => GlobalTheory.T.descended_lattice_finite_projective B.X K' U _ (γ U) (hinj U) (hrange U) h (L j U) (hL j U).1
  have hc : ((p : ℕ) : Γ(B'.X, ⊤)) ≠ 0 := by
    obtain ⟨U, -⟩ := hcov (Classical.arbitrary B'.X)
    intro h0
    have := congrArg (fun a => ((γ U (resG B'.X (le_top : V U ≤ ⊤) a) : U.Bp) : Kbar B.X)) h0
    simp only [map_natCast, map_zero] at this
    exact hpK (by simpa using this)
  have hcP : ∀ (j : J) (U : AffOp B.X) (x : Fin h → Γ(B'.X, V U)), resG B'.X (le_top : V U ≤ ⊤) ((p : ℕ) : Γ(B'.X, ⊤)) • x ∈ P j U := by
    intro j U x
    rw [map_natCast]
    show piMap (γ U) (Fin h) (((p : ℕ) : Γ(B'.X, V U)) • x) ∈ L j U
    rw [LinearMap.map_smulₛₗ, map_natCast]
    exact (hL j U).2 _
  refine ⟨fun j => (glueSub V (P j)).toMod, fun j => (glueSub V (P j)).incl, fun j =>
    ⟨GlobalTheory.T.coherent_submodules_glue_finite B'.X h _ V (P j) hV hcov href (hcomp j) (hfp j) _ hc (hcP j), inferInstance, fun U => ?_⟩⟩
  have himg : piMap (resG B'.X (le_rfl : V U ≤ V U)) (Fin h) '' (P j U : Set (Fin h → Γ(B'.X, V U))) = P j U := by
    ext v
    refine ⟨?_, fun hv => ⟨v, hv, funext fun l => GlobalTheory.LB.resG_self _ (v l)⟩⟩
    rintro ⟨u, hu, rfl⟩
    have e : piMap (resG B'.X (le_rfl : V U ≤ V U)) (Fin h) u = u := funext fun l => GlobalTheory.LB.resG_self _ (u l)
    rw [e]
    exact hu
  have hsec : ∀ s : Γ(freeModule B'.X (Fin h), V U), s ∈ (glueSub V (P j)).sec (V U) ↔ coords B'.X h (V U) s ∈ P j U := by
    intro s
    rw [GlobalTheory.T.coherent_submodule_sections_affine B'.X h _ V (P j) href (hcomp j) U (V U) (hV U) le_rfl s, himg, Submodule.span_eq]
  have hset : {x : Fin h → U.Bp | ∃ s : Γ((glueSub V (P j)).toMod, f.f ⁻¹ᵁ U.1), ∀ i, x i = γ U (((GlobalTheory.VB.isFrame_freeFrame B'.X (Fin h)).basis le_top).repr ((glueSub V (P j)).incl.app _ s) i)} = piMap (γ U) (Fin h) '' (P j U : Set (Fin h → Γ(B'.X, V U))) := by
    ext x
    constructor
    · rintro ⟨s, hs⟩
      have hm := (hsec _).1 ((glueSub V (P j)).incl_app_mem s)
      exact ⟨_, hm, funext fun l => (hs l).symm⟩
    · rintro ⟨v, hv, rfl⟩
      have hm : (coords B'.X h (V U)).symm v ∈ (glueSub V (P j)).sec (V U) := by
        rw [hsec, LinearEquiv.apply_symm_apply]
        exact hv
      refine ⟨(glueSub V (P j)).mkSec _ hm, fun l => ?_⟩
      rw [GlobalTheory.VB.Sub.incl_app_mkSec]
      show γ U (v l) = γ U (coords B'.X h (V U) ((coords B'.X h (V U)).symm v) l)
      rw [LinearEquiv.apply_symm_apply]
  rw [hset]
  obtain ⟨-, -, hspan⟩ := (hL j U).1
  conv_lhs => rw [hspan]
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hr : ∀ l, (a l : U.Bp) ∈ (γ U).range := fun l => by rw [hrange U]; exact (a l).2
    choose v hv using hr
    refine ⟨v, ?_, funext fun l => hv l⟩
    show piMap (γ U) (Fin h) v ∈ L j U
    have e : piMap (γ U) (Fin h) v = fun i => (a i : U.Bp) := funext fun l => hv l
    rw [e]
    exact ha
  · rintro ⟨v, hv, rfl⟩
    have hr : ∀ l, γ U (v l) ∈ ringOver K' U := fun l => by rw [← hrange U]; exact ⟨v l, rfl⟩
    exact ⟨fun l => ⟨γ U (v l), hr l⟩, hv, rfl⟩

end GlobalTheory.LatGlue
