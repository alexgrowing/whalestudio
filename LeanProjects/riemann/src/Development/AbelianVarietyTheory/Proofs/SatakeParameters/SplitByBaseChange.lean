import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoveringOfForallMem
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory.EtC.Tr

theorem splitBy_baseChange : ∀ {Z X V T : Scheme.{0}} {f : Z ⟶ X} {y : V ⟶ X} {m : ℕ} {s : Fin m → (V ⟶ Z)},
    GlobalTheory.EtC.Tr.SplitBy f y s → ∀ (w : T ⟶ V), GlobalTheory.EtC.Tr.SplitBy f (w ≫ y) (fun j => w ≫ s j) := by
  intro Z X V T f y m s ⟨hs, hiso⟩ w
  have hs' : ∀ j, (w ≫ s j) ≫ f = w ≫ y := fun j => by rw [Category.assoc, hs j]
  refine ⟨hs', ?_⟩

  let c : Cofan (fun _ : Fin m => V) :=
    Cofan.mk (pullback f y) (fun j => pullback.lift (s j) (𝟙 V) (by rw [hs j, Category.id_comp]))
  have hc : IsColimit c := by
    haveI : IsIso ((coproductIsCoproduct (fun _ : Fin m => V)).desc c) := hiso
    exact IsColimit.ofPointIso (coproductIsCoproduct (fun _ : Fin m => V))
  let c' : Cofan (fun _ : Fin m => T) :=
    Cofan.mk (pullback f (w ≫ y)) (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp]))
  let g : pullback f (w ≫ y) ⟶ pullback f y :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ w) (by rw [pullback.condition, Category.assoc])
  have hg1 : g ≫ pullback.fst f y = pullback.fst f (w ≫ y) := pullback.lift_fst _ _ _
  have hg2 : g ≫ pullback.snd f y = pullback.snd f (w ≫ y) ≫ w := pullback.lift_snd _ _ _

  have hA : IsPullback (pullback.snd f (w ≫ y)) g w (pullback.snd f y) := by
    refine IsPullback.of_bot (v₂₁ := pullback.fst f y) (v₂₂ := y) (h₃₁ := f) ?_ hg2.symm
      (IsPullback.of_hasPullback f y).flip
    rw [hg1]
    exact (IsPullback.of_hasPullback f (w ≫ y)).flip
  let α : Discrete.functor (fun _ : Fin m => T) ⟶ Discrete.functor (fun _ : Fin m => V) :=
    Discrete.natTrans (fun _ => w)
  have hsq : ∀ j, w ≫ c.ι.app ⟨j⟩ = c'.ι.app ⟨j⟩ ≫ g := by
    intro j
    show w ≫ pullback.lift (s j) (𝟙 V) _ = pullback.lift (w ≫ s j) (𝟙 T) _ ≫ g
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.lift_fst, hg1, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, hg2, ← Category.assoc, pullback.lift_snd,
        Category.comp_id, Category.id_comp]
  have hcc : α ≫ c.ι = c'.ι ≫ (Functor.const _).map g := by
    ext ⟨j⟩
    exact hsq j
  have hpb : ∀ j, IsPullback (c'.ι.app j) (α.app j) g (c.ι.app j) := by
    rintro ⟨j⟩
    refine IsPullback.of_right (h₁₂ := pullback.snd f (w ≫ y)) (v₁₃ := w) (h₂₂ := pullback.snd f y) ?_ (hsq j).symm hA
    have e1 : c'.ι.app ⟨j⟩ ≫ pullback.snd f (w ≫ y) = 𝟙 T := pullback.lift_snd _ _ _
    have e2 : c.ι.app ⟨j⟩ ≫ pullback.snd f y = 𝟙 V := pullback.lift_snd _ _ _
    rw [e1, e2]
    show IsPullback (𝟙 T) w w (𝟙 V)
    exact IsPullback.id_horiz w
  obtain ⟨hc'⟩ := FinitaryPreExtensive.isUniversal_finiteCoproducts hc c' α g hcc
    (NatTrans.Equifibered.of_discrete _) hpb
  have : Sigma.desc (fun j => pullback.lift (w ≫ s j) (𝟙 T) (by rw [hs' j, Category.id_comp])) =
      ((coproductIsCoproduct (fun _ : Fin m => T)).coconePointUniqueUpToIso hc').hom := by
    apply Sigma.hom_ext; intro j
    rw [Sigma.ι_desc]
    exact ((coproductIsCoproduct (fun _ : Fin m => T)).comp_coconePointUniqueUpToIso_hom hc' ⟨j⟩).symm
  rw [this]
  infer_instance

end GlobalTheory.EtC.Tr
