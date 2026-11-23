import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsQProjOverCompImmersion
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.UPel.HT

theorem siegPre_actPB_pullback : ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (O : Type) [Ring O] (bar : O → O)
    (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B) (f : S' ⟶ S) (z : SiegPre h M ζ s)
    (act : O → (z.A ⟶ z.A)), f ≫ s = s' → z.Principal → IsRAct z.A act → Adj z.A z.P bar act →
    ∃ (w : SiegPre h M ζ s') (actw : O → (w.A ⟶ w.A)), w.Principal ∧ IsRAct w.A actw ∧
      Adj w.A w.P bar actw ∧ ActPB w actw z act f := by
  intro h M B _ ζ O _ bar S S' s s' f z act hs hz hR hA
  obtain ⟨⟨w, φ, φ₂, hφ, hsq, hP, hlev⟩, hpr⟩ := GlobalTheory.siegPre_pullback h M B ζ S S' s s' f z hs
  have hwP : w.Principal := hpr w ⟨φ, φ₂, hφ, hsq, hP, hlev⟩ hz
  obtain ⟨e, he, heφ⟩ := grpPullback_iso hφ (isGrpPullback_pullback z.A f)
  haveI := he
  have hie : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]
  let actw : O → (w.A ⟶ w.A) := fun a => e.hom ≫ (Over.pullback f).map (act a) ≫ e.inv
  have hv : ∀ a, (actw a).left ≫ φ = φ ≫ (act a).left := fun a => by
    have hm : ((Over.pullback f).map (act a)).left ≫ pullback.fst z.A.hom f =
        pullback.fst z.A.hom f ≫ (act a).left := pullback.lift_fst _ _ _
    rw [← heφ]
    simp only [actw, Over.comp_left, Category.assoc]
    rw [reassoc_of% hie, hm]
  have hRw : IsRAct w.A actw := ActUnr.isRAct_conj e _ (ActUnr.isRAct_pullback f z.A act hR)
  have lf : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (fst Y Y).left = x.left :=
    fun x y => by rw [← Over.comp_left, lift_fst]
  have ls : ∀ {T : Scheme.{0}} {X Y : Over T} (x y : X ⟶ Y), (lift x y).left ≫ (snd Y Y).left = y.left :=
    fun x y => by rw [← Over.comp_left, lift_snd]
  have hc1 : ∀ a, (lift (fst w.A w.A ≫ actw a) (snd w.A w.A)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A ≫ act a) (snd z.A z.A)).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, Over.comp_left _ _ _ (fst w.A w.A) (actw a),
        Over.comp_left _ _ _ (fst z.A z.A) (act a), Category.assoc, hv, ← Category.assoc, ← hsq.1, Category.assoc]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, hsq.2]
  have hc2 : ∀ a, (lift (fst w.A w.A) (snd w.A w.A ≫ actw (bar a))).left ≫ φ₂ =
      φ₂ ≫ (lift (fst z.A z.A) (snd z.A z.A ≫ act (bar a))).left := fun a => by
    apply ActUnr.left_hom_ext
    · rw [Category.assoc, hsq.1, ← Category.assoc, lf, Category.assoc, lf, hsq.1]
    · rw [Category.assoc, hsq.2, ← Category.assoc, ls, Category.assoc, ls, Over.comp_left _ _ _ (snd w.A w.A) (actw (bar a)),
        Over.comp_left _ _ _ (snd z.A z.A) (act (bar a)), Category.assoc, hv, ← Category.assoc, ← hsq.2, Category.assoc]
  have hadj : Adj w.A w.P bar actw := fun a => by
    have h1 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc1 a).symm
    have h2 := GlobalTheory.GenSpread.lbIso_pull_comp (L := z.P) (M := z.P) φ₂ rfl rfl (hA a)
    have h3 := GlobalTheory.GenSpread.lbIso_pull_of_lbIso hP _ (hc2 a).symm
    exact LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB w.isLB _)
      (LBIso.trans (pull_isLB w.isLB _) (pull_isLB z.isLB _) (pull_isLB z.isLB _) h1 h2) h3.symm
  exact ⟨w, actw, hwP, hRw, hadj, φ, φ₂, hφ, hsq, hP, hlev, hv⟩

end GlobalTheory.UPel.HT
