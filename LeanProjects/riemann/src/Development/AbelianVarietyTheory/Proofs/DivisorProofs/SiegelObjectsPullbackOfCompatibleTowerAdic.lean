import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalAlgebraisationMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoAlgebraisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsLocalRingQuotientPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegFormalAssemble

theorem siegPB_id_of_tower : ∀ (g n : ℕ) (B : Type) [CommRing B] (ζ : B) (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (s s' : Sp R ⟶ Sp B) (c : SiegPre g n ζ s) (c' : SiegPre g n ζ s') (t : ∀ e : ℕ, Sp (R ⧸ I ^ (e + 1)) ⟶ Sp B) (ce : ∀ e, SiegPre g n ζ (t e)) (φ : ∀ e, (ce e).A.left ⟶ c.A.left) (ψ : ∀ e, (ce e).A.left ⟶ c'.A.left) (β : ∀ e, (ce e).A.left ⟶ (ce (e + 1)).A.left), c.Principal → (∀ e, SRelBy (ce e) c 1 1 (Out.thick R I e) (φ e)) → (∀ e, SRelBy (ce e) c' 1 1 (Out.thick R I e) (ψ e)) → (∀ e, β e ≫ φ (e + 1) = φ e) → (∀ e, β e ≫ ψ (e + 1) = ψ e) → SiegPB c c' (𝟙 _) := by
  intro g n B _ ζ R _ _ I hI s s' c c' t ce φ ψ β hc hφ hψ hβφ hβψ
  have H := GlobalTheory.FormalAlgMorphisms.formalAlgebraisation_morphisms
  have hp : GlobalTheory.AbLaw.IsProjBy c.A.hom :=
    GlobalTheory.WtTower.isProjBy_of_relAmple c.A (pull_isLB c.isLB _) hc.1
  obtain ⟨G, hG, hGφ, -, -, hGP⟩ := GlobalTheory.AlgUniq.exists_iso_algebraisation H R I hI (fun e => (ce e).A) β c.A c'.A
    c.ab c'.ab hp φ ψ (fun e => (hφ e).1) hβφ (fun e => (hψ e).1) hβψ
  choose b₂ hb₂ hb₂P using fun e => (hφ e).2.1
  choose b₂' hb₂' hb₂'P using fun e => (hψ e).2.1
  have hP := hGP c.P c'.P b₂ b₂' c.isLB c'.isLB hb₂ hb₂' fun e =>
    LBIso.trans (pull_isLB c.isLB _) (ce e).isLB (pull_isLB c'.isLB _) (LBIso.symm (hb₂P e)) (hb₂'P e)
  refine ⟨G.hom.left, (G.hom ⊗ₘ G.hom).left, isGrpPullback_of_iso G, ⟨?_, ?_⟩, hP, fun a => ?_⟩
  · rw [← Over.comp_left, tensorHom_fst, Over.comp_left]
  · rw [← Over.comp_left, tensorHom_snd, Over.comp_left]
  · have : IsProper c'.A.hom := c'.ab.proper
    have : IsProper (𝟙_ (Over (Sp R))).hom := show IsProper (𝟙 _) from inferInstance
    have key : c.lev a ≫ G.hom = c'.lev a := by
      refine GlobalTheory.Published.FormalAlgebraisation.Morphisms.hom_ext H hI fun e => ?_
      have hw : pullback.fst (𝟙_ (Over (Sp R))).hom (Out.thick R I e) =
          pullback.snd (𝟙_ (Over (Sp R))).hom (Out.thick R I e) ≫ Out.thick R I e := by
        rw [← pullback.condition]; exact (Category.comp_id _).symm
      have l1 := (hφ e).2.2 a
      have l2 := (hψ e).2.2 a
      simp only [pow_one] at l1 l2
      rw [hw, Over.comp_left, Category.assoc, Category.assoc, ← reassoc_of% l1, ← l2, ← hGφ e]
    rw [Category.id_comp, ← key, Over.comp_left]

end GlobalTheory.SiegFormalAssemble
