import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAdditiveLineBundleFamilyAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedKernelFiniteFlatSurjectiveOverBaseStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCover

theorem twistedKernel_affine : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A],
    IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → ∀ (T : Over (Sp R)) [IsAffine T.left]
    (N : LB (A ⊗ T).left), Fam A N → ∃ (H : Over (Sp R)) (h : H ⟶ A ⊗ T), IsClosedImmersion h.left ∧
    IsFinite (h ≫ snd A T).left ∧ Flat (h ≫ snd A T).left ∧ Surjective (h ≫ snd A T).left ∧
    ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (t : Y ⟶ T), Same A (abelian₂ A L) N a t ↔ ∃ z : Y ⟶ H, z ≫ h = lift a t := by
  intro R _ _ A _ hA L hL hamp T _ N hN
  obtain ⟨T₀, φ, N₀, hT₀, hft, hN₀, hsame⟩ := GlobalTheory.DualApprox.exists_fam_finiteType R A hA T N hN
  obtain ⟨H₀, h₀, hci, hfin, hfl, hsurj, hrep⟩ := GlobalTheory.T.twistedKernel_finite_flat_surjective_over_base R A hA L hL hamp T₀ hft N₀ hN₀
  have sq₂ : IsPullback (A ◁ φ) (snd A T) (snd A T₀) φ := GlobalTheory.SS.TorusSlice.isPullback_whiskerLeft A φ
  have sq₁ : IsPullback (pullback.fst h₀ (A ◁ φ)) (pullback.snd h₀ (A ◁ φ)) h₀ (A ◁ φ) :=
    IsPullback.of_hasPullback _ _
  have sq : IsPullback (pullback.fst h₀ (A ◁ φ)) (pullback.snd h₀ (A ◁ φ) ≫ snd A T) (h₀ ≫ snd A T₀) φ :=
    sq₁.paste_vert sq₂
  have sq₁' := sq₁.map (Over.forget (Sp R))
  have sq' := sq.map (Over.forget (Sp R))
  have hΛ : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  refine ⟨pullback h₀ (A ◁ φ), pullback.snd h₀ (A ◁ φ), ?_, ?_, ?_, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq₁' hci
  · exact MorphismProperty.of_isPullback (P := @IsFinite) sq' hfin
  · exact MorphismProperty.of_isPullback (P := @Flat) sq' hfl
  · exact MorphismProperty.of_isPullback (P := @Surjective) sq' hsurj
  · intro Y a t

    have key : evc hN.isLB (fst A Y) (snd A Y ≫ t) = evc hN₀.isLB (fst A Y) (snd A Y ≫ t ≫ φ) := by
      have e := congrArg (CechPic.pull (lift (fst A Y) (snd A Y ≫ t)).left)
        ((same_iff hN.isLB hN₀.isLB (𝟙 T) φ).1 hsame)
      simpa only [pull_evc, lift_fst, lift_snd_assoc, lift_snd, Category.comp_id, Category.assoc] using e
    have e₁ : Same A (abelian₂ A L) N a t ↔ Same A (abelian₂ A L) N₀ a (t ≫ φ) := by
      rw [same_iff hΛ hN.isLB, same_iff hΛ hN₀.isLB, key]
    have e₂ : lift a (t ≫ φ) = lift a t ≫ (A ◁ φ) := by
      ext <;> simp
    rw [e₁, hrep, e₂]
    constructor
    · rintro ⟨z₀, hz₀⟩
      exact ⟨pullback.lift z₀ (lift a t) hz₀, pullback.lift_snd _ _ _⟩
    · rintro ⟨z, hz⟩
      exact ⟨z ≫ pullback.fst h₀ (A ◁ φ), by rw [Category.assoc, pullback.condition, ← Category.assoc, hz]⟩

end GlobalTheory.DualCover
