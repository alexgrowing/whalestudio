import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.NotExistsOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator

set_option autoImplicit false

open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains

noncomputable section

namespace GlobalTheory.MixedLocalChains.FrobQuot

theorem nonempty_pullback_cokernel {X Y : Scheme.{0}} (π : Y ⟶ X) (a : Γ(X, ⊤)) (b : Γ(Y, ⊤))
    (hb : π.appTop a = b) :
    Nonempty ((Scheme.Modules.pullback π).obj (cokernel (smulHom (QCoh.structureModule X) a)) ≅
      cokernel (smulHom (QCoh.structureModule Y) b)) := by
  obtain ⟨e⟩ := GlobalTheory.AbLaw.LbSheafModel.pullback_unit π
  subst hb
  exact ⟨PreservesCokernel.iso (Scheme.Modules.pullback π) _ ≪≫
    cokernel.mapIso _ _ e e (by rw [VB.pullback_map_smulHom]; exact smulHom_comp e.hom _)⟩

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime]
  (B : GlobalTheory.Vert.Model O)

theorem natCast_eq_zero_fibI : (p : Γ((fibI p B).subscheme, ⊤)) = 0 := by
  set I := fibI p B
  refine I.subscheme.sheaf.eq_of_locally_eq' (fun U : B.X.affineOpens => I.subschemeι ⁻¹ᵁ U.1) ⊤
    (fun _ => homOfLE le_top) ?_ _ 0 fun U => ?_
  · intro z _
    have hz : I.subschemeι z ∈ (⨆ U : B.X.affineOpens, (U : B.X.Opens)) := by
      rw [iSup_affineOpens_eq_top]; trivial
    obtain ⟨U, hU⟩ := TopologicalSpace.Opens.mem_iSup.1 hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨U, hU⟩
  · have h0 : (I.subschemeι.app U.1).hom (p : Γ(B.X, U.1)) = 0 := by
      rw [← RingHom.mem_ker, I.ker_subschemeι_app U]
      simp only [I, fibI, Scheme.IdealSheafData.ofIdealTop_ideal]
      have := Ideal.mem_map_of_mem (B.X.presheaf.map (homOfLE (le_top : U.1 ≤ ⊤)).op).hom
        (Ideal.mem_span_singleton_self (p : Γ(B.X, ⊤)))
      rwa [map_natCast] at this
    rw [map_natCast] at h0
    change (I.subscheme.presheaf.map _).hom (p : Γ(I.subscheme, ⊤)) = (I.subscheme.presheaf.map _).hom 0
    rw [map_natCast, map_zero]
    exact h0

theorem isIso_unit_fibI (F : B.X.Modules) [F.IsQuasicoherent]
    (hF : smulHom F (p : Γ(B.X, ⊤)) = 0) :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction (fibI p B).subschemeι).unit.app F) := by
  refine (QCoh.isIso_iff_forall_affine (M := F) (N := (Scheme.Modules.pushforward (fibI p B).subschemeι).obj
    ((Scheme.Modules.pullback (fibI p B).subschemeι).obj F)) _).2 fun U hU => ?_
  obtain ⟨h₁, h₂⟩ := surjective_and_ker_unit_subschemeι (fibI p B) F ⟨U, hU⟩
  refine ⟨(LinearMap.ker_eq_bot (f := QCoh.appLinear _ U)).1 (h₂.trans ?_), h₁⟩
  refine Submodule.le_annihilator_iff.1 (le_trans ?_ Submodule.annihilator_top.ge)
  simp only [fibI, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton,
    Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
  rw [Module.mem_annihilator]
  intro m
  have := congrArg (fun φ => φ.app U m) hF
  simpa using this

end GlobalTheory.MixedLocalChains.FrobQuot

namespace GlobalTheory.MixedLocalChains.FrobQuot

theorem appTop_absFrob_comp (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0)
    (f : Γ(B.X, ⊤)) :
    (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp ≫ (fibI p B).subschemeι).appTop f =
      ((fibI p B).subschemeι.appTop f) ^ p := by
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
  exact (GlobalTheory.SS.FrobField.absFrob_appLE _ p 1 Fact.out hp ⊤ le_rfl _).trans (by rw [pow_one])

end GlobalTheory.MixedLocalChains.FrobQuot

namespace GlobalTheory.MixedLocalChains

open GlobalTheory.MixedLocalChains.FrobQuot in

theorem isFrob_cokernel_smulHom_pow : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ)
    [Fact p.Prime] (B : GlobalTheory.Vert.Model O) (f : Γ(B.X, ⊤)), f ^ p ∣ (p : Γ(B.X, ⊤)) →
    IsFrob p (cokernel (GlobalTheory.smulHom (GlobalTheory.QCoh.structureModule B.X) f))
      (cokernel (GlobalTheory.smulHom (GlobalTheory.QCoh.structureModule B.X) (f ^ p))) := by
  intro O _ _ _ p _ B f hf
  have hp := natCast_eq_zero_fibI p B
  refine ⟨hp, ?_⟩
  have hC : smulHom (cokernel (smulHom (QCoh.structureModule B.X) (f ^ p))) (f ^ p) = 0 :=
    (cancel_epi (cokernel.π _)).1 (by rw [comp_zero, ← smulHom_comp, cokernel.condition])
  have hCp : smulHom (cokernel (smulHom (QCoh.structureModule B.X) (f ^ p))) (p : Γ(B.X, ⊤)) = 0 := by
    obtain ⟨c, hc⟩ := hf
    rw [hc, smulHom_mul, hC, comp_zero]
  have hI := isIso_unit_fibI p B (cokernel (smulHom (QCoh.structureModule B.X) (f ^ p))) hCp
  obtain ⟨e₁⟩ := nonempty_pullback_cokernel (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp ≫ (fibI p B).subschemeι)
    f (((fibI p B).subschemeι.appTop f) ^ p) (appTop_absFrob_comp p B hp f)
  obtain ⟨e₂⟩ := nonempty_pullback_cokernel (fibI p B).subschemeι (f ^ p) (((fibI p B).subschemeι.appTop f) ^ p)
    (map_pow _ _ _)
  have e₃ : (Scheme.Modules.pullback (fibI p B).subschemeι).obj
      (cokernel (smulHom (QCoh.structureModule B.X) (f ^ p))) ≅
      (Scheme.Modules.pullback (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out hp ≫ (fibI p B).subschemeι)).obj
        (cokernel (smulHom (QCoh.structureModule B.X) f)) := e₂ ≪≫ e₁.symm
  have e₄ := @asIso _ _ _ _ ((Scheme.Modules.pullbackPushforwardAdjunction (fibI p B).subschemeι).unit.app
      (cokernel (smulHom (QCoh.structureModule B.X) (f ^ p)))) hI
  exact ⟨e₄ ≪≫ (Scheme.Modules.pushforward (fibI p B).subschemeι).mapIso e₃⟩

end GlobalTheory.MixedLocalChains
