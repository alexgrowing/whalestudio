import Development.EtaleCohomology.WeilConjectures.PushCxTPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.EWeil.ArtinCut LateralTheory.EWeil.LerayCut LateralTheory.EWeil.PushPf LateralTheory.EWeil.PushCxTPf

namespace LateralTheory.EWeil.AcycPf

def incl (S : Scheme.{0}) : S.Etale ⥤ Over S := MorphismProperty.Over.forget _ _ _

def ResInj : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (s : ℤ), Injective ((res R F).X s)

def RestrInj : Prop := ∀ (R : Type) [CommRing R] (S : Scheme.{0})
  (G : Sheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))) [Injective G],
  ∃ h : Presheaf.IsSheaf S.smallEtaleTopology ((incl S).op ⋙ G.val),
    Injective (⟨_, h⟩ : Sheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R)))

def ModAcyc : Prop := Base → ∀ (q : ℕ) (A : CommRingCat.{0})
  (G : Sheaf (Spec A).smallEtaleTopology (ModuleCat.{1} (ULift.{1} (ZMod q)))) [Injective G]
  (h : Presheaf.IsSheaf (Spec A).smallEtaleTopology (G.val ⋙ forget₂ (ModuleCat.{1} (ULift.{1} (ZMod q))) AddCommGrpCat.{1}))
  (n : ℕ), 0 < n → Subsingleton (Sheaf.H.{1} (⟨_, h⟩ : Sm A) n)

end LateralTheory.EWeil.AcycPf
