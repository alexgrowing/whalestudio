import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E1Cut

namespace LateralTheory.E.LocallyConstantH0

def gam {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) : Prim q Γ(Spec (CommRingCat.of B), ⊤) :=
  ζ.map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom

def IsLCMap (q : ℕ) [NeZero q] (i : ℤ)
    (m : ∀ (B : Type) [CommRing B], Prim q B → (LocallyConstant (PrimeSpectrum B) (ZMod q) →+ Sec (tw q i) (Spec (CommRingCat.of B)))) :
    Prop :=
  (∀ (B C : Type) [CommRing B] [CommRing C] (f : B →+* C) (ζ : Prim q B) (φ : LocallyConstant (PrimeSpectrum B) (ZMod q)),
      Sec.res (Spec.map (CommRingCat.ofHom f)) (m B ζ φ) = m C (ζ.map f) (lcMap f φ)) ∧
  ∀ (B : Type) [CommRing B] (ζ : Prim q B) (c : ZMod q), m B ζ (LocallyConstant.const _ c) = c.val • twGen i (gam ζ)

def LCMap : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ), ∃ m, IsLCMap q i m

def LCBij : Prop := ∀ (q : ℕ) [NeZero q] (i : ℤ) m, IsLCMap q i m →
  ∀ (B : Type) [CommRing B] (ζ : Prim q B), Function.Bijective (m B ζ)

theorem localConstant_H0 (hM : LCMap) (hB : LCBij) : LateralTheory.E.t_E1Cut.EtaleDegreeZeroCohomologyEquivLocallyConstantFunctions := by
  intro hA9 q _ i
  obtain ⟨m, hm⟩ := hM q i
  obtain ⟨-, e0, hnat, -⟩ := hA9 (ZMod q) (tw q i)
  refine ⟨fun B _ ζ => (AddEquiv.ofBijective (m B ζ) (hB q i m hm B ζ)).trans (e0 (Spec (CommRingCat.of B))), ?_⟩
  intro B C _ _ f ζ φ
  simp only [AddEquiv.trans_apply, AddEquiv.ofBijective_apply]
  rw [hnat, hm.1]

end LateralTheory.E.LocallyConstantH0
