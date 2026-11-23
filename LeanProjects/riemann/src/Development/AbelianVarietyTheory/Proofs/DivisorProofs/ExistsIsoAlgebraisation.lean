import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsProjByOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpHomAlgebraisationOfReductionsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfIsoOnAllReductionsStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AlgUniq

theorem isPullback_square {S S' : Scheme.{0}} {G : Over S} {A : Over S'} {f : S' ⟶ S}
    {a : A.left ⟶ G.left} (hA : IsPullback a A.hom G.hom f)
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} (h : Geo.Tor.IsSquare a φ₂) :
    IsPullback φ₂ (A ⊗ A).hom (G ⊗ G).hom f := by
  have w₁ : (fst G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have w₂ : (snd G G).left ≫ G.hom = (G ⊗ G).hom := Over.w _
  have v₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have v₂ : (snd A A).left ≫ A.hom = (A ⊗ A).hom := Over.w _
  have h₁ := h.1
  have h₂ := h.2
  refine ⟨⟨by rw [← w₁, reassoc_of% h₁, hA.w, reassoc_of% v₁]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => pullback.lift
      (hA.lift (s.fst ≫ (fst G G).left) s.snd (by rw [Category.assoc, w₁, s.condition]))
      (hA.lift (s.fst ≫ (snd G G).left) s.snd (by rw [Category.assoc, w₂, s.condition]))
      (by rw [IsPullback.lift_snd, IsPullback.lift_snd])) (fun s => ?_) (fun s => ?_)
    (fun s m h1 h2 => ?_)⟩⟩
  · apply pullback.hom_ext
    · change _ ≫ (fst G G).left = _ ≫ (fst G G).left
      rw [Category.assoc, h₁, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
    · change _ ≫ (snd G G).left = _ ≫ (snd G G).left
      rw [Category.assoc, h₂, ← Category.assoc]
      exact (congrArg (· ≫ a) (pullback.lift_snd _ _ _)).trans (IsPullback.lift_fst _ _ _ _)
  · rw [← v₁, ← Category.assoc]
    exact (congrArg (· ≫ A.hom) (pullback.lift_fst _ _ _)).trans (IsPullback.lift_snd _ _ _ _)
  · apply pullback.hom_ext
    · refine Eq.trans ?_ (pullback.lift_fst _ _ _).symm
      change _ ≫ (fst A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₁]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₁]
    · refine Eq.trans ?_ (pullback.lift_snd _ _ _).symm
      change _ ≫ (snd A A).left = _
      apply hA.hom_ext
      · rw [IsPullback.lift_fst, ← h1, Category.assoc, Category.assoc, h₂]
      · rw [IsPullback.lift_snd, ← h2, Category.assoc, v₂]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (a : Y ⟶ X) (b : Z ⟶ Y)
    (c : Z ⟶ X) (e : b ≫ a = c) : LBIso (L.pull c) ((L.pull a).pull b) := by
  subst e
  exact LBIso.symm (LBIso.chartPull (chartPullLinComb L a (fun _ : PUnit => b)
      (fun _ => b ≫ a) (fun _ => 1) (𝟙 _) fun _ => (Category.id_comp _).symm)
      (chartPullId _) (PolBaseChange.lbIso_refl (pull_isLB hL _)))

theorem square_comp {S S' : Scheme.{0}} {G G' : Over S} {A : Over S'} {a : A.left ⟶ G.left}
    {a' : A.left ⟶ G'.left} {g : G ⟶ G'} (hg : a ≫ g.left = a')
    {φ₂ : (A ⊗ A).left ⟶ (G ⊗ G).left} {φ₂' : (A ⊗ A).left ⟶ (G' ⊗ G').left}
    (h : Geo.Tor.IsSquare a φ₂) (h' : Geo.Tor.IsSquare a' φ₂') : φ₂ ≫ (g ⊗ₘ g).left = φ₂' := by
  have h₁ := h.1
  have h₂ := h.2
  apply pullback.hom_ext
  · change _ ≫ (fst G' G').left = _ ≫ (fst G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_fst, Over.comp_left, reassoc_of% h₁, hg, h'.1]
  · change _ ≫ (snd G' G').left = _ ≫ (snd G' G').left
    rw [Category.assoc, ← Over.comp_left, tensorHom_snd, Over.comp_left, reassoc_of% h₂, hg, h'.2]

theorem exists_iso_algebraisation : GlobalTheory.Published.FormalAlgebraisation.Morphisms → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R), IsAdicComplete I R → ∀ (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) [∀ e, GrpObj (Y e)] (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (B B' : Over (Spec (CommRingCat.of R))) [GrpObj B] [GrpObj B'], IsAbelianScheme B → IsAbelianScheme B' → IsProjBy B.hom → ∀ (b : ∀ e, (Y e).left ⟶ B.left) (b' : ∀ e, (Y e).left ⟶ B'.left), (∀ e, IsGrpPullback (Y e) B (thick R I e) (b e)) → (∀ e, β e ≫ b (e + 1) = b e) → (∀ e, IsGrpPullback (Y e) B' (thick R I e) (b' e)) → (∀ e, β e ≫ b' (e + 1) = b' e) → ∃ g : B ≅ B', IsMonHom g.hom ∧ (∀ e, b e ≫ g.hom.left = b' e) ∧ (∀ g' : B ⟶ B', (∀ e, b e ≫ g'.left = b' e) → g' = g.hom) ∧ (∀ (M : LB B.left) (M' : LB B'.left), M.IsLB → M'.IsLB → (∀ e, LBIso (M.pull (b e)) (M'.pull (b' e))) → LBIso M (M'.pull g.hom.left)) ∧ ∀ (P : LB (B ⊗ B).left) (P' : LB (B' ⊗ B').left) (b₂ : ∀ e, (Y e ⊗ Y e).left ⟶ (B ⊗ B).left) (b₂' : ∀ e, (Y e ⊗ Y e).left ⟶ (B' ⊗ B').left), P.IsLB → P'.IsLB → (∀ e, Geo.Tor.IsSquare (b e) (b₂ e)) → (∀ e, Geo.Tor.IsSquare (b' e) (b₂' e)) → (∀ e, LBIso (P.pull (b₂ e)) (P'.pull (b₂' e))) → LBIso P (P'.pull (g.hom ⊗ₘ g.hom).left) := by
  intro H R _ _ I hI Y _ β B B' _ _ hB hB' hp b b' hb hβ hb' hβ'
  have := hB.proper
  have := hB'.proper
  obtain ⟨g, hg, hu⟩ := H.exists_iso hI (fun e => (hb e).1) hβ (fun e => (hb' e).1) hβ'
  obtain ⟨k, hk, hk', -⟩ := GlobalTheory.T.grpHom_algebraisation_of_reductions H R I hI B B' hB.proper hB'.proper Y Y β β b b' hb hβ hb' hβ'
    (fun e => 𝟙 _) (fun e => inferInstance)
    (fun e => by rw [Over.id_left, Over.id_left, Category.comp_id, Category.id_comp])
  have hkg : k = g.hom := hu k fun e => by rw [hk', Over.id_left, Category.id_comp]
  refine ⟨g, hkg ▸ hk, hg, hu, fun M M' hM hM' h => ?_, fun P P' b₂ b₂' hP hP' hs hs' h => ?_⟩
  · exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI B hB.smooth hp hB.geomConnected Y b (fun e => (hb e).1) M _ hM
      (pull_isLB hM' _) fun e => (h e).trans (pull_isLB hM _) (pull_isLB hM' _)
        (pull_isLB (pull_isLB hM' _) _) (lbIso_pull_comp hM' _ _ _ (hg e))
  · have hBB := AbelianSchemeGerms.isAbelianScheme_tensor B B hB hB
    exact GlobalTheory.T.lineBundle_iso_of_iso_on_all_reductions R I hI (B ⊗ B) hBB.smooth (isProjBy_tensor R B B hp hp) hBB.geomConnected
      (fun e => Y e ⊗ Y e) b₂ (fun e => isPullback_square (hb e).1 (hs e)) P _ hP
      (pull_isLB hP' _) fun e => (h e).trans (pull_isLB hP _) (pull_isLB hP' _)
        (pull_isLB (pull_isLB hP' _) _) (lbIso_pull_comp hP' _ _ _ (square_comp (hg e) (hs e) (hs' e)))

end GlobalTheory.AlgUniq
