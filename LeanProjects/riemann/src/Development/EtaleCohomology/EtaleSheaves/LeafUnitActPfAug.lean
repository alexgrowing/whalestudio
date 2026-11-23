import Development.EtaleCohomology.EtaleSheaves.LeafUnitActPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitActPfAug

def sumC (q : ℕ) (A : Type) [CommRing A] : (Prim q A →₀ ULift.{1} (ZMod q)) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  Finsupp.linearCombination _ (fun _ => 1)

theorem twRel_zero_le (q : ℕ) (A : Type) [CommRing A] : twRel q 0 A ≤ LinearMap.ker (sumC q A) := by
  refine Submodule.span_le.2 ?_
  rintro x ⟨ζ, ξ, a, -, rfl⟩
  simp [sumC]
  exact sub_self _

def aug (q : ℕ) (A : Type) [CommRing A] :
    ((Prim q A →₀ ULift.{1} (ZMod q)) ⧸ twRel q 0 A) →ₗ[ULift.{1} (ZMod q)] ULift.{1} (ZMod q) :=
  (twRel q 0 A).liftQ (sumC q A) (twRel_zero_le q A)

theorem aug_mk_single (q : ℕ) {A : Type} [CommRing A] (ζ : Prim q A) :
    aug q A (Submodule.Quotient.mk (Finsupp.single ζ 1)) = 1 := by
  simp [aug, sumC]

theorem aug_map (q : ℕ) {A B : CommRingCat.{0}} (f : A ⟶ B) (x : (twF q 0).obj A) :
    aug q B (((twF q 0).map f).hom x) = aug q A x := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    change aug q B (Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map f.hom) y)) = aug q A (Submodule.Quotient.mk y)
    simp only [aug, Submodule.liftQ_apply, sumC]
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add u v hu hv => simp [Finsupp.mapDomain_add, hu, hv]
    | single p c => simp [Finsupp.mapDomain_single]

end LateralTheory.E.LeafUnitActPfAug

namespace LateralTheory.E.LeafUnitActPfAug
open LateralTheory.E.CupProductRingLaws

theorem etale_tate_twist_zero_section_locally_lifts_to_ring_value (q : ℕ) {U : Scheme.{0}} (a : Sec (tw q 0) U) :
    Loc U (fun V g => ∃ x : (twF q 0).obj Γ(V, ⊤), Sec.res g a = ofRings.sec (twF q 0) V x) := by
  refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)) (U := op U) a, fun V g ⟨t, ht⟩ => ⟨t, ht.symm⟩⟩

theorem etale_tate_twist_zero_sections_eq_locally_of_sheafified_eq (q : ℕ) {U : Scheme.{0}} (x y : (twF q 0).obj Γ(U, ⊤))
    (h : ofRings.sec (twF q 0) U x = ofRings.sec (twF q 0) U y) :
    Loc U (fun V g => ((twF q 0).map g.appTop).hom x = ((twF q 0).map g.appTop).hom y) := by
  refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology.{0}
    (toSheafify Scheme.etaleTopology.{0} (Scheme.Γ ⋙ twF q 0)) (X := op U) x y h, fun V g hg => hg⟩

end LateralTheory.E.LeafUnitActPfAug
