import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsExtraAlt
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def locRing {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)) :
    Subring (FractionRing (MRing ι ⧸ P)) :=
  Subring.closure {x | ∃ (u v : MRing ι) (a : K → ℕ)
    (hv : Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P)),
    v ∉ W ∧ IsMultiHomog u a ∧ IsMultiHomog v a ∧
      x = IsLocalization.mk' (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) ⟨_, hv⟩}

def locIdeal {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι))
    (y : FractionRing (MRing ι ⧸ P)) : Ideal (locRing P W) :=
  Ideal.span {z | (z : FractionRing (MRing ι ⧸ P)) = y}

theorem locIdeal_eq_span {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {P W : Ideal (MRing ι)}
    {y : FractionRing (MRing ι ⧸ P)} (hy : y ∈ locRing P W) :
    locIdeal P W y = Ideal.span {(⟨y, hy⟩ : locRing P W)} := by
  unfold locIdeal
  congr 1
  ext z
  simp only [Set.mem_singleton_iff]
  exact ⟨fun h => Subtype.ext h, fun h => by rw [h]; rfl⟩

def specZTwo : Ideal (MRing (PBlk 1)) := Ideal.span {C 2}

end

end GroundTheory.Heights₂.Heights.Inter
