import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsLocRingIntClosure
import GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingChartLoc
import GroundTheory.HeightsAndTheta.Heights.Intersections.StIntClosureLocFinite
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

open Classical in

theorem subfield_closure_coords_eq_top {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    (P' : Ideal (MRing ι')) [P'.IsPrime] :
    Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
      algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
        Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := MRing ι' ⧸ P') x
  have h : ∀ f : MRing ι', algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' f) ∈
      Subfield.closure ((Finset.univ.image fun q : Σ k, ι' k =>
        algebraMap (MRing ι' ⧸ P') (FractionRing (MRing ι' ⧸ P')) (Ideal.Quotient.mk P' (X q)) :
          Finset (FractionRing (MRing ι' ⧸ P'))) : Set (FractionRing (MRing ι' ⧸ P'))) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eq_intCast C r, map_intCast, map_intCast]; exact intCast_mem _ r
    | add f g hf hg => rw [map_add, map_add]; exact add_mem hf hg
    | mul_X f q hf =>
      rw [map_mul, map_mul]
      exact mul_mem hf (Subfield.subset_closure (by simp))
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  exact div_mem (h f) (h g)

theorem LocRingIntClosureFinite.proof (h₁ : LocRingChartLoc.Statement) (h₂ : IntClosureLocFinite.Statement) :
    LocRingIntClosureFinite.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' n s α W _hv hP' _hQ _hs _hsQ hW
  have := hP'.2.1.1
  have := imageZ_isPrime_of_prime v P'
  obtain ⟨T, hTA, hloc⟩ := h₁ K ι (imageZ v P') W hW.1.1.1 (le_sup_left.trans hW.1.1.2) hW.2
  obtain ⟨t, ht⟩ := h₂ _ _ (fracMapZ v P') _ (subfield_closure_coords_eq_top P') _ T hTA hloc
  exact ⟨t, fun x _ hx => ht x hx⟩

end GroundTheory.Heights₂.Heights.Inter
