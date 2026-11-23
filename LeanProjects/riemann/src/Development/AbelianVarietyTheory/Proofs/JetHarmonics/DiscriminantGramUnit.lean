import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.SplitUnramifiedPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniqueMaximalAbovePlace
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DifferentPowerUnramifiedIffStatement

noncomputable section
open scoped TensorProduct
open Matrix

namespace GlobalTheory.CutMultiplicationUnits

section Lin

variable {k A O : Type} [CommRing k] [CommRing A] [Algebra k A] [CommRing O] [Algebra k O]

abbrev cut (k : Type) {A : Type} [CommRing k] [CommRing A] [Algebra k A] (e : A) : Submodule k A :=
  LinearMap.range (LinearMap.mulLeft k e)

theorem mul_mem_cut {e : A} (y : A) {a : A} (ha : a ∈ cut k e) : y * a ∈ cut k e := by
  obtain ⟨c, rfl⟩ := ha
  exact ⟨y * c, by simp [mul_left_comm]⟩

theorem e_mul_of_mem {e : A} (he : e * e = e) {a : A} (ha : a ∈ cut k e) : e * a = a := by
  obtain ⟨c, rfl⟩ := ha
  simp [← mul_assoc, he]

def mulCut (e y : A) : cut k e →ₗ[k] cut k e :=
  (LinearMap.mulLeft k y).restrict (fun _ ha => mul_mem_cut y ha)

variable {n : ℕ} {e : A} (b : Module.Basis (Fin n) k (cut k e))

variable (T : Fin n → (A →ₐ[k] O))

end Lin

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

def extFun (l : R →ₗ[ℤ] ℤ) : Op p R →ₗ[ℤ_[p]] ℤ_[p] :=
  (TensorProduct.AlgebraTensorModule.rid ℤ ℤ_[p] ℤ_[p]).toLinearMap ∘ₗ l.baseChange ℤ_[p]

variable [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
  {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]
  [Algebra ℤ_[p] O]

end Local

section Compare

open GlobalTheory.IndefiniteRowSideFullHecke.SplitUnramifiedPlaces ReciprocityTheory.ChartRestriction.G.Pdiv

variable {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R]

theorem sig_eq_bar [StarRing R] (x : Op p R) : AvDefs.sig p R x = bar p R x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul z a => rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy]

def placeUEquiv : AvDefs.PlaceU p R ≃ Place p R where
  toFun w := ⟨w.e, w.idem, w.ne_zero, w.prim⟩
  invFun w := ⟨w.e, w.idem, w.ne_zero, w.primitive⟩
  left_inv _ := rfl
  right_inv _ := rfl

def placeEquiv [StarRing R] : AvDefs.Place p R ≃ SplitPlace p R where
  toFun w := ⟨⟨w.e, w.idem, w.ne_zero, w.prim⟩, fun h =>
    w.split ((sig_eq_bar w.e).trans (congrArg Place.e h).symm)⟩
  invFun w := ⟨w.e, w.idem, w.ne_zero, w.primitive, fun h =>
    w.ne_conj (Place.ext ((sig_eq_bar w.e).symm.trans h).symm)⟩
  left_inv _ := rfl
  right_inv _ := rfl

def owEquiv (w : Place p R) : cut ℤ_[p] w.e ≃ₗ[ℤ_[p]] w.Ow :=
  LinearEquiv.ofBijective
    ((Ideal.Quotient.mkₐ ℤ_[p] (Ideal.span {1 - w.e})).toLinearMap ∘ₗ (cut ℤ_[p] w.e).subtype) (by
      constructor
      · rw [injective_iff_map_eq_zero]
        intro a ha
        obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
        have hc' : c * (1 - w.e) = (a : Op p R) := hc
        apply Subtype.ext
        rw [← e_mul_of_mem w.idem a.2, ← hc', mul_left_comm, mul_sub, w.idem.eq, mul_one,
          sub_self, mul_zero]
        rfl
      · intro s
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        refine ⟨⟨w.e * a, a, rfl⟩, Ideal.Quotient.eq.2 ?_⟩
        exact Ideal.mem_span_singleton'.2 ⟨-a, by
          show -a * (1 - w.e) = w.e * a - a
          ring⟩)

def embEquiv (w : Place p R) (O : Type) [CommRing O] [Algebra ℤ_[p] O] :
    AvDefs.Emb (O := O) w.e ≃ w.Emb O := Equiv.refl _

variable [IsDedekindDomain R] [CharZero R] [Module.Finite ℤ R]
  {C : Type} [Field C] [CharZero C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O]

end Compare

end GlobalTheory.CutMultiplicationUnits
