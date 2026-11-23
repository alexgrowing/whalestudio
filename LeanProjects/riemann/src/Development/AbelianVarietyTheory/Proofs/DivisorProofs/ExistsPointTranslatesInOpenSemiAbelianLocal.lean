import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShearMeet

theorem exists_fst_mul_mem : ∀ (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ V : G.left.Opens, (∃ y₀ ∈ V, G.hom y₀ = closedPoint R) → ∀ y : G.left, ∃ z : (G ⊗ G).left, (fst G G).left z = y ∧ (fst G G * snd G G).left z ∈ V ∧ (fst G G * (snd G G)⁻¹).left z ∈ V := by
  intro R _ _ G _ hG V ⟨y₀, hy₀, e₀⟩ y
  have := hG.smooth
  have : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G

  obtain ⟨y₁, hy₁, e₁⟩ : ∃ y₁ ∈ V, G.hom y₁ = G.hom y := by
    have hs : G.hom y ⤳ G.hom y₀ := by rw [e₀]; exact IsLocalRing.specializes_closedPoint _
    obtain ⟨y₁, h₁, h₂⟩ := (Flat.generalizingMap G.hom) hs
    exact ⟨y₁, h₁.mem_open V.2 hy₀, h₂⟩
  let f := fst G G
  let g := snd G G
  obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback (f := G.hom) (g := G.hom) y y₁ e₁.symm
  have hf : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst G.hom G.hom))
  have hwf : f.left w = y := hw1
  have hwg : g.left w = y₁ := hw2

  let bp : G ⊗ G ⟶ G ⊗ G := lift f (f⁻¹ * g)
  let bm : G ⊗ G ⟶ G ⊗ G := lift f (g⁻¹ * f)
  have bp1 : bp ≫ (f * g) = g := by
    rw [MonObj.comp_mul, lift_fst, lift_snd, mul_inv_cancel_left]
  have bm1 : bm ≫ (f * g⁻¹) = g := by
    rw [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have bp2 : bp ≫ f = f := lift_fst _ _
  have bm2 : bm ≫ f = f := lift_fst _ _
  have hi : IsIrreducible (f.left ⁻¹' {y}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι y).continuous.continuousOn
  have mp : (bp.left w) ∈ f.left ⁻¹' {y} ∩ (f * g).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bp.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp2]; exact hwf
    · show (f * g).left (bp.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bp1, hwg]; exact hy₁
  have mm : (bm.left w) ∈ f.left ⁻¹' {y} ∩ (f * g⁻¹).left ⁻¹ᵁ V := by
    refine ⟨?_, ?_⟩
    · show f.left (bm.left w) = y
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm2]; exact hwf
    · show (f * g⁻¹).left (bm.left w) ∈ V
      rw [← Scheme.Hom.comp_apply, ← Over.comp_left, bm1, hwg]; exact hy₁
  obtain ⟨z, hz, k₁, k₂⟩ := hi.2 _ _ ((f * g).left ⁻¹ᵁ V).2 ((f * g⁻¹).left ⁻¹ᵁ V).2 ⟨_, mp⟩ ⟨_, mm⟩
  exact ⟨z, hz, k₁, k₂⟩

end GlobalTheory.ShearMeet
