import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZarLocalPf

def LocSH : Prop := ∀ (S : Type) [CommRing S], AIC S → ∀ p : PrimeSpectrum S, SH (Localization.AtPrime p.asIdeal)

def LocDiag : Prop := ∀ (S : Type) [CommRing S] (p : PrimeSpectrum S),
  ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
    Nonempty (IsColimit c) ∧ (SH (Localization.AtPrime p.asIdeal) → SH c.pt) ∧
    ∃ (j0 : J) (a : S →+* D.obj j0), ∀ (k : J) (m : j0 ⟶ k), ∃ f : S, f ∉ p.asIdeal ∧
      ∃ r : D.obj k →+* Localization.Away f, r.comp ((D.map m).hom.comp a) = algebraMap S (Localization.Away f)

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem ZarLocal_of (hSH : LocSH) (hD : LocDiag) : LateralTheory.E.t_E1Cut.ZarLocal := by
  intro hB1 hB2 q S _ hS hq n i hn x p
  obtain ⟨J, _, _, D, c, ⟨hc⟩, hpt, j0, a, hk⟩ := hD S p
  have hsh : SH c.pt := hpt (hSH S hS p)
  set y := pull _ (spMap a) _ _ x with hy
  have hqa : IsUnit ((q : ℕ) : D.obj j0) := by simpa using hq.map a
  have h0 : pull _ (spMap (c.ι.app j0).hom) _ _ y = 0 := by
    exact @Subsingleton.elim _ (hB2 (ZMod q) c.pt hsh (tw q i) n hn) _ _
  obtain ⟨k, m, hm⟩ := (hB1 q D c hc n i).2 j0 y hqa h0
  obtain ⟨f, hf, r, hr⟩ := hk k m
  refine ⟨f, hf, ?_⟩
  rw [← hr, spMap_comp, pull_comp, spMap_comp, pull_comp, ← hy, hm, map_zero]

end LateralTheory.E.ZarLocalPf
