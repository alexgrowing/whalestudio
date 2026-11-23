import Development.EtaleCohomology.EtaleSheaves.LeafOneSpecPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneExistsPf

open LateralTheory.E.CupProductRingLaws

def LeafUnitSec : Prop := ∀ (q : ℕ) [NeZero q], ∃ one : ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Sec (tw q 0) U,
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : IsUnit (q : Γ(U, ⊤))) (hV : IsUnit (q : Γ(V, ⊤))),
    Sec.res g (one U hU) = one V hV) ∧
  ∀ (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (ζ : Prim q Γ(U, ⊤)), one U hU = twGen 0 ζ

def LeafCocycleOfSec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U),
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) →
  ∃ α : Cocycle ((chains R).obj E) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev α.1 0 0 (by simp) U x = Sec.map (resι R F) (s U ⟨x⟩)

theorem LeafOneExists_of (hU : LeafUnitSec) (hC : LeafCocycleOfSec) : LateralTheory.E.LeafOneSpecPf.LeafOneExists := by
  intro q _ E hE
  obtain ⟨one, hnat, hone⟩ := hU q
  obtain ⟨α, hα⟩ := hC (ZMod q) (tw q 0) E (fun U h => one U (hE U h))
    (fun V U g hU' hV' => hnat V U g _ _)
  refine ⟨α, fun U x ζ => ?_⟩
  rw [hα U x, hone U _ ζ]
  rfl

end LateralTheory.E.LeafOneExistsPf
