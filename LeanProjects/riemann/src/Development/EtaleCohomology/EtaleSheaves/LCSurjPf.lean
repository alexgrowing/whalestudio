import Development.EtaleCohomology.EtaleSheaves.LCBijPf
import Development.EtaleCohomology.EtaleSheaves.LSecGluePf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut LateralTheory.E.LocallyConstantH0

namespace LateralTheory.E.LCSurjPf

def LocForm : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
  Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)

def Descent : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (y : Sec (tw q i) (Spec (CommRingCat.of B))),
    (Loc (Spec (CommRingCat.of B)) fun _ g => ∃ c : ZMod q, Sec.res g y = c.val • twGen i ((gam ζ).map g.appTop.hom)) →
    ∃ ψ : LocallyConstant (PrimeSpectrum B) (ZMod q),
      Loc (Spec (CommRingCat.of B)) fun _ g => Sec.res g y = Sec.res g (m B ζ ψ)

theorem sec_sep {R : Type} [CommRing R] (F : Shv R) (U : Scheme.{0}) (a b : Sec F U)
    (h : Loc U fun _ g => Sec.res g a = Sec.res g b) : a = b := by
  obtain ⟨S, hS, hab⟩ := h
  exact (LateralTheory.E.L_sec_gluePf.typeSheaf F S hS).isSeparatedFor.ext fun V g hg => hab V g hg

theorem LCSurj_of (hL : LocForm) (hD : Descent) : LateralTheory.E.LCBijPf.LCSurj := by
  intro q _ i m hm B _ ζ y
  obtain ⟨ψ, hψ⟩ := hD q i m hm B ζ y (hL q i B ζ y)
  exact ⟨ψ, (sec_sep _ _ _ _ hψ).symm⟩

end LateralTheory.E.LCSurjPf
