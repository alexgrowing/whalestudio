import Mathlib
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibrePowerProper

theorem isProper_hom_of_iso {T : Scheme.{0}} {X Y : Over T} (e : X ≅ Y) (h : IsProper Y.hom) :
    IsProper X.hom := by
  have hw : X.hom = e.hom.left ≫ Y.hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  rw [hw]
  infer_instance

theorem isProper_prod_hom {T : Scheme.{0}} (X Y : Over T) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by
  have h1 : (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Over.w (prod.fst : X ⨯ Y ⟶ X)).symm
  have hfst : IsProper (pullback.fst X.hom Y.hom) := by haveI := hY; infer_instance
  rw [h1]
  infer_instance

theorem isProper_fan_pt {T : Scheme.{0}} : ∀ (n : ℕ) (f : Fin n → Over T),
    (∀ i, IsProper (f i).hom) → ∀ (c : Fan f), IsLimit c → IsProper c.pt.hom
  | 0, f, _, c, hc => by
      have h0 : IsLimit (Fan.mk (Over.mk (𝟙 T)) (fun i => i.elim0 : ∀ i, Over.mk (𝟙 T) ⟶ f i)) :=
        Fan.IsLimit.mk _ (fun _ => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
          (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso h0) (by dsimp; infer_instance)
  | n + 1, f, hf, c, hc => by
      let c₁ : Fan (fun i : Fin n => f i.succ) := limit.cone (Discrete.functor fun i : Fin n => f i.succ)
      have h1 : IsProper c₁.pt.hom :=
        isProper_fan_pt n (fun i => f i.succ) (fun i => hf _) c₁ (limit.isLimit _)
      have hl := extendFanIsLimit f (limit.isLimit (Discrete.functor fun i : Fin n => f i.succ))
        (prodIsProd (f 0) c₁.pt)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso hl) (isProper_prod_hom _ _ (hf 0) h1)

theorem isProper_eighth_fibre_power : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)),
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) →
    IsProper C.hom → IsProper B.hom := by
  intro T B C pr hu hC
  have hl : IsLimit (Fan.mk B pr) :=
    Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose)
      (fun s a => (hu s.pt s.proj).choose_spec.1 a)
      (fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm)
  exact isProper_fan_pt 8 (fun _ => C) (fun _ => hC) _ hl

end GlobalTheory.FibrePowerProper
