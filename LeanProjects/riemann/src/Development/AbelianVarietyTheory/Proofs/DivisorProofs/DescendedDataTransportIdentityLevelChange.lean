import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLev

theorem descData_transport_id : ∀ (h n N d : ℕ) (B B' : Type) [CommRing B] [CommRing B'] (ζ : B) (ζ' : B') (X Y : Scheme.{0}) (s : X ⟶ Sp B) (s' : X ⟶ Sp B') (C : SiegPre h N ζ' s') (c : SiegPre h n ζ s) (π : X ⟶ Y) (A₀ : Over Y) [GrpObj A₀] (φ : C.A.left ⟶ A₀.left) (φ₂ : (G2 C.A).left ⟶ (G2 A₀).left) (P₀ : LB (G2 A₀).left) (lev₀ : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over Y) ⟶ A₀)), SRel C c d 1 (𝟙 X) → IsGrpPullback C.A A₀ π φ → IsSquare φ φ₂ → P₀.IsLB → LBIso C.P (P₀.pull φ₂) → (∀ a, (C.lev a ^ d).left ≫ φ = π ≫ (lev₀ a).left) → ∃ (φ' : c.A.left ⟶ A₀.left) (φ₂' : (G2 c.A).left ⟶ (G2 A₀).left), IsGrpPullback c.A A₀ π φ' ∧ IsSquare φ' φ₂' ∧ LBIso c.P (P₀.pull φ₂') ∧ ∀ a, (c.lev a).left ≫ φ' = π ≫ (lev₀ a).left := by
  intro h n N d B B' _ _ ζ ζ' X Y s s' C c π A₀ _ φ φ₂ P₀ lev₀ hS hA hsq hP₀ hw hlev
  obtain ⟨ψ, hψ, ⟨ψ₂, hsqψ, hC⟩, hlevψ⟩ := hS
  haveI : IsMonHom (Iso.refl c.A).hom := inferInstanceAs (IsMonHom (𝟙 c.A))
  obtain ⟨e, he, heψ⟩ := grpPullback_iso (isGrpPullback_of_iso (Iso.refl c.A)) hψ
  haveI := he
  have heψ' : e.hom.left ≫ ψ = 𝟙 _ := by simpa using heψ
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  have hψe : ψ = e.inv.left := by
    rw [← Category.id_comp ψ, ← hie, Category.assoc, heψ', Category.comp_id]
  let E₂ : G2 c.A ⟶ G2 C.A := lift (fst c.A c.A ≫ e.hom) (snd c.A c.A ≫ e.hom)
  have hE₂ : E₂.left ≫ ψ₂ = 𝟙 _ := by
    have := GlobalTheory.SiegelDescent.lift_square hsqψ (τ := 𝟙 (G2 c.A).left) (a := fst c.A c.A ≫ e.hom)
      (b := snd c.A c.A ≫ e.hom) (a₀ := fst c.A c.A) (b₀ := snd c.A c.A)
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
      (by rw [Over.comp_left, Category.assoc, heψ', Category.comp_id, Category.id_comp])
    rw [this, lift_fst_snd, Over.id_left, Category.comp_id]
  refine ⟨e.hom.left ≫ φ, E₂.left ≫ φ₂, ((isGrpPullback_of_iso e).comp hA).congr (Category.id_comp π) rfl, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left, Category.assoc]
  · rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left, Category.assoc]
  · have h1 : LBIso (C.P.pull E₂.left) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame P₀ _ (fun _ => φ₂) _ E₂.left fun _ => rfl) hw
    have h2 : LBIso (C.P.pull E₂.left) (c.P.pull (E₂.left ≫ ψ₂)) :=
      LBIso.chartPull (chartPullPull C.P E₂.left)
        (chartPullSame c.P _ (fun _ => ψ₂) _ E₂.left fun _ => rfl) hC
    have h3 : LBIso (c.P.pull (E₂.left ≫ ψ₂)) (P₀.pull (E₂.left ≫ φ₂)) :=
      LBIso.trans (pull_isLB c.isLB _) (pull_isLB C.isLB _) (pull_isLB hP₀ _) h2.symm h1
    exact LBIso.chartPull (chartPullUnpull c.P _ hE₂)
      (chartPullSame P₀ _ _ _ (𝟙 _) fun _ => (Category.id_comp _).symm) h3
  · intro a
    have h₀ := hlevψ a
    rw [pow_one, Category.id_comp, hψe] at h₀
    rw [← h₀, Category.assoc, ← Category.assoc e.inv.left, hie, Category.id_comp, hlev a]

end GlobalTheory.SiegLev
