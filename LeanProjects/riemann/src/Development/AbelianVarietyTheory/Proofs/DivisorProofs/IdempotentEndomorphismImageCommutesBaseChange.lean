import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleSpreadSubring
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.ImgPB

@[reassoc]
theorem tensorHom_fst_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (fst Y W).left = (fst X Z).left ≫ f.left := by
  rw [← Over.comp_left, tensorHom_fst, Over.comp_left]

@[reassoc]
theorem tensorHom_snd_left {B : Scheme.{0}} {X Y Z W : Over B} (f : X ⟶ Y) (h : Z ⟶ W) :
    (f ⊗ₘ h).left ≫ (snd Y W).left = (snd X Z).left ≫ h.left := by
  rw [← Over.comp_left, tensorHom_snd, Over.comp_left]

theorem image_idem_pullback : ∀ (S' T : Scheme.{0}) (g : T ⟶ S') (A G : Over S') [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (inc : G ⟶ A) (pr : A ⟶ G) (ε : A ⟶ A) (A' G' : Over T) [GrpObj A'] [IsCommMonObj A'] [GrpObj G'] [IsCommMonObj G'] (inc' : G' ⟶ A') (pr' : A' ⟶ G') (ε' : A' ⟶ A') (ψ : A'.left ⟶ A.left) (ψ₂ : (G2 A').left ⟶ (G2 A).left), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = ε → IsMonHom inc' → IsMonHom pr' → inc' ≫ pr' = 𝟙 G' → pr' ≫ inc' = ε' → IsGrpPullback A' A g ψ → IsSquare ψ ψ₂ → ε'.left ≫ ψ = ψ ≫ ε.left → ∃ (φ : G'.left ⟶ G.left) (φ₂ : (G2 G').left ⟶ (G2 G).left), IsGrpPullback G' G g φ ∧ IsSquare φ φ₂ ∧ inc'.left ≫ ψ = φ ≫ inc.left ∧ (inc' ⊗ₘ inc').left ≫ ψ₂ = φ₂ ≫ (inc ⊗ₘ inc).left := by
  intro S' T g A G _ _ _ _ inc pr ε A' G' _ _ _ _ inc' pr' ε' ψ ψ₂ hinc hpr hip hpi hinc' hpr' hip' hpi' hψ hsq hεψ
  have hε' : inc' ≫ ε' = inc' := by rw [← hpi', ← Category.assoc, hip', Category.id_comp]
  have key : inc'.left ≫ ψ = inc'.left ≫ ψ ≫ pr.left ≫ inc.left := by
    rw [← Over.comp_left, hpi, ← hεψ, ← Category.assoc, ← Over.comp_left, hε']
  have hipl : inc.left ≫ pr.left = 𝟙 _ := by rw [← Over.comp_left, hip]; rfl
  have hipl' : inc'.left ≫ pr'.left = 𝟙 _ := by rw [← Over.comp_left, hip']; rfl
  have e2' : inc ≫ ε ≫ pr = 𝟙 G := by rw [← hpi, Category.assoc, reassoc_of% hip, hip]
  have e2 : inc.left ≫ ε.left ≫ pr.left = 𝟙 _ := by
    rw [← Over.comp_left, ← Over.comp_left, e2']; rfl
  have e1 : pr'.left ≫ inc'.left ≫ ψ ≫ pr.left = ψ ≫ ε.left ≫ pr.left := by
    rw [← Category.assoc, ← Over.comp_left, hpi', ← Category.assoc, hεψ, Category.assoc]
  have hψp := hψ.1
  refine ⟨inc'.left ≫ ψ ≫ pr.left, (inc' ⊗ₘ inc').left ≫ ψ₂ ≫ (pr ⊗ₘ pr).left, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    key.trans (by simp only [Category.assoc]), ?_⟩
  · have w : (inc'.left ≫ ψ ≫ pr.left) ≫ G.hom = G'.hom ≫ g := by
      rw [Category.assoc, Category.assoc, Over.w pr, hψp.w, ← Category.assoc, Over.w inc']
    refine IsPullback.of_isLimit' ⟨w⟩ (PullbackCone.IsLimit.mk _
      (fun s => hψp.lift (s.fst ≫ inc.left) s.snd (by rw [Category.assoc, Over.w inc]; exact s.condition) ≫ pr'.left)
      ?_ ?_ ?_)
    · intro s
      simp only [Category.assoc]
      rw [e1, hψp.lift_fst_assoc, Category.assoc, e2, Category.comp_id]
    · intro s
      rw [Category.assoc, Over.w pr', hψp.lift_snd]
    · intro s m hm1 hm2
      have hm : m ≫ inc'.left = hψp.lift (s.fst ≫ inc.left) s.snd
          (by rw [Category.assoc, Over.w inc]; exact s.condition) := by
        apply hψp.hom_ext
        · rw [hψp.lift_fst, ← hm1, Category.assoc, key]
          simp only [Category.assoc]
        · rw [hψp.lift_snd, Category.assoc, Over.w inc', hm2]
      calc m = m ≫ inc'.left ≫ pr'.left := by rw [hipl', Category.comp_id]
        _ = _ := by rw [← Category.assoc, hm]
  · intro U x y x₀ y₀ hx hy
    have h1 : (x₀ ≫ inc).left = (x ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hx, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have h2 : (y₀ ≫ inc).left = (y ≫ inc').left ≫ ψ := by
      rw [Over.comp_left, hy, Over.comp_left]
      simp only [Category.assoc]
      rw [← key]
    have hm := hψ.2 U (x ≫ inc') (y ≫ inc') (x₀ ≫ inc) (y₀ ≫ inc) h1 h2
    calc (x₀ * y₀).left = ((x₀ * y₀) ≫ inc).left ≫ pr.left := by
          rw [Over.comp_left, Category.assoc, hipl, Category.comp_id]
      _ = ((x * y) ≫ inc').left ≫ ψ ≫ pr.left := by
          rw [MonObj.mul_comp, MonObj.mul_comp, hm, Category.assoc]
      _ = _ := by rw [Over.comp_left, Category.assoc]
  · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, tensorHom_fst_left_assoc]
  · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, tensorHom_snd_left_assoc]
  · apply Pdiv.PullbackComparison.adelic_GL2_ext_of_local_components
    · simp only [Category.assoc, tensorHom_fst_left, reassoc_of% hsq.1, hsq.1, tensorHom_fst_left_assoc]
      rw [← key]
    · simp only [Category.assoc, tensorHom_snd_left, reassoc_of% hsq.2, hsq.2, tensorHom_snd_left_assoc]
      rw [← key]

end GlobalTheory.ImgPB
