import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelOn
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieRankAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAbelianSchemeQuotientByFiniteTranslations
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualAbelianSchemeExistsBiduality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

open scoped CategoryTheory.Obj
open GlobalTheory.AbDual GlobalTheory.CechPic

namespace GlobalTheory.DualHomPull

theorem exists_dual_hom : ∀ (Y : Scheme.{0}) (A G : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj G] [IsCommMonObj G] (χ : A ⟶ G) (P'' : LB (G2 G).left), IsAbelianScheme A → IsAbelianScheme G → IsMonHom χ → P''.IsLB → (∃ t : (P''.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, t.IsGen) → (∃ t : (P''.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, t.IsGen) → ∃ (D : Over Y) (_ : GrpObj D) (Q : LB (A ⊗ D).left) (h : A ⟶ D), IsAbelianScheme D ∧ GlobalTheory.AbDual.IsDual A D Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (P''.pull (χ ⊗ₘ χ).left) (Q.pull (lift (fst A A) (snd A A ≫ h)).left) := by
  intro Y A G _ _ _ _ χ P'' hA hG hχ hP h₁ h₂
  obtain ⟨D, _, Q, hD, -, q, q'⟩ := GlobalTheory.dualAbelianScheme Y A hA
  obtain ⟨a₁, a₂⟩ := GlobalTheory.CubeAxes.additive_of_triv_axes hG hP h₁ h₂
  have eχ : χ ⊗ₘ χ = lift (fst A A ≫ χ) (snd A A ≫ χ) := by ext <;> simp
  rw [eχ]
  have hE : (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)).IsLB := pull_isLB hP _
  have k : ∀ {T : Over Y} (a t : T ⟶ A), evc hE a t = evc hP (a ≫ χ) (t ≫ χ) := fun a t ↦ by
    rw [evc_ev hP _ _ hE, lift_fst_assoc, lift_snd_assoc]
  have b₁ : IsAdditive (ev P'' (fst A A ≫ χ) (snd A A ≫ χ)) := (isAdditive_iff hE).2 fun T a a' t ↦ by
    haveI := hχ
    rw [k, k, k, MonObj.mul_comp]
    exact (isAdditive_iff hP).1 a₁ _ _ _ _
  have b₂ : IsAdditive (swap (ev P'' (fst A A ≫ χ) (snd A A ≫ χ))) :=
    (GlobalTheory.BirigidLift.isAdditive_swap_iff hE).2 fun T a t t' ↦ by
      haveI := hχ
      rw [k, k, k, MonObj.mul_comp]
      exact (GlobalTheory.BirigidLift.isAdditive_swap_iff hP).1 a₂ _ _ _ _
  obtain ⟨x, hx, e⟩ := GlobalTheory.BirigidLift.exists_hom q q'.additive hE b₁ b₂
  exact ⟨D, inferInstance, Q, x, hD, q, q'.additive, hx, (cls_eq_iff hE (pull_isLB q.isLB _)).1 e⟩

end GlobalTheory.DualHomPull
