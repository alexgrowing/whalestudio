import Development.EtaleCohomology.EtaleSheaves.QuotAcycCut

noncomputable section
open CategoryTheory Limits GlobalTheory.EtC

namespace LateralTheory.E.HensCut

def LocAIC : Prop := ∀ (B : Type) [CommRing B] [IsDomain B] (M : Submonoid B), (0 : B) ∉ M → AIC B →
  IsDomain (Localization M) ∧ AIC (Localization M)

def MonicSplits : Prop := ∀ (R : Type) [CommRing R] [IsDomain R], AIC R → ∀ p : Polynomial R, p.Monic →
  ∃ s : Multiset R, p = (s.map fun a => Polynomial.X - Polynomial.C a).prod

def IdemPart : Prop := ∀ (A : Type) [CommRing A] (n : ℕ) (y : Fin n → A), ∏ l, y l = 0 →
  IsUnit (∑ l, ∏ m ∈ Finset.univ.erase l, y m) →
  ∃ e : Fin n → A, (∀ l, IsIdempotentElem (e l)) ∧ (∀ l m, l ≠ m → e l * e m = 0) ∧ ∑ l, e l = 1 ∧ ∀ l, e l * y l = 0

def ColimHens : Prop := ∀ (B : Type) [CommRing B] (I : Ideal B) (J : Type) [SmallCategory J] [IsFiltered J]
  (D : J ⥤ CommRingCat.{0}) (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D) (c : Cocone D), IsColimit c →
  (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) →
  (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) →
  (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
    IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
    ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧ a - (D.map f).hom a₀ ∈ I.map (β.app j').hom) →
  ∃ K : Ideal c.pt, HenselianRing c.pt K ∧ Nonempty (B ⧸ I ≃+* c.pt ⧸ K)

def PartDiag : Prop := ∀ (q : ℕ) (B : Type) [CommRing B] [IsDomain B] (I : Ideal B), AIC B → IsUnit (q : B) →
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0})
    (β : (Functor.const J).obj (CommRingCat.of B) ⟶ D),
    (∀ j, ∃ (m : ℕ) (R : Fin m → Type) (_ : ∀ k, CommRing (R k)),
      (∀ k, IsDomain (R k) ∧ AIC (R k) ∧ IsUnit (q : R k)) ∧ Nonempty (D.obj j ≃+* ∀ k, R k)) ∧
    (∀ j, Function.Bijective (Ideal.quotientMap (I.map (β.app j).hom) (β.app j).hom Ideal.le_comap_map)) ∧
    (∀ j, ∀ x ∈ I.map (β.app j).hom, ∃ (j' : J) (f : j ⟶ j'), IsUnit ((D.map f).hom (1 + x))) ∧
    (∀ j (p : Polynomial (D.obj j)) (a₀ : D.obj j), p.Monic → p.eval a₀ ∈ I.map (β.app j).hom →
      IsUnit (Ideal.Quotient.mk (I.map (β.app j).hom) (p.derivative.eval a₀)) →
      ∃ (j' : J) (f : j ⟶ j') (a : D.obj j'), (p.map (D.map f).hom).IsRoot a ∧
        a - (D.map f).hom a₀ ∈ I.map (β.app j').hom)

theorem goal_of (_hL : LocAIC) (_hM : MonicSplits) (_hI : IdemPart) (hC : ColimHens) (hD : PartDiag) :
    LateralTheory.E.QuotAcycCut.Hens := by
  intro q B _ _ I hB hq
  obtain ⟨J, _, _, D, β, hst, ha, hb, hc⟩ := hD q B I hB hq
  obtain ⟨K, hK, he⟩ := hC B I J D β (colimit.cocone D) (colimit.isColimit D) ha hb hc
  refine ⟨J, inferInstance, inferInstance, D, colimit.cocone D, colimit.isColimit D, hst, ?_, K, hK, he⟩
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have h1 : IsUnit ((q : B)) := hq
  have h2 := h1.map ((β.app j) ≫ (colimit.cocone D).ι.app j).hom
  simpa using h2

end LateralTheory.E.HensCut
