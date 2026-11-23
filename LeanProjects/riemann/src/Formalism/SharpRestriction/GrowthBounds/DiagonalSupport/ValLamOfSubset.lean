import Formalism.SharpRestriction.GrowthBounds.DiagonalSupport.MembDefs
import Formalism.SharpRestriction.GrowthBounds.ValuationLowestDegreeRename

noncomputable section

open MvPolynomial Finset Classical

namespace Formalism.MainNotions.Proposition5Numerics

open Formalism.MainNotions.G

section Z

variable {B : Type*} [CommRing B] {σ τ : Type*}

def FinalFormK (k : ℤ) (H : MvPolynomial σ (LaurentPolynomial B)) : Prop := ∀ m, (H.coeff m).coeff k = 0

end Z

section S

variable {R : Type*} [CommRing R] {ι : Type*} {n : ℕ}

theorem notMem_sDegs_iff (LL : Letters ι) (S : Set ι) (j : Fin n) (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    k ∉ sDegs LL S j G ↔ FinalFormK k (twistSub LL S j G) := by
  unfold sDegs FinalFormK
  rw [Finset.mem_biUnion]
  constructor
  · intro h m
    by_contra hm
    apply h
    refine ⟨m, ?_, Finsupp.mem_support_iff.2 hm⟩
    rw [mem_support_iff]
    intro h0
    rw [h0] at hm
    simp at hm
  · rintro h ⟨m, _, hm⟩
    exact (Finsupp.mem_support_iff.1 hm) (h m)

theorem sDegs_subset_of {ι' : Type*} (LL : Letters ι) (S : Set ι) (LL' : Letters ι') (S' : Set ι') (j : Fin n)
    (G : MvPolynomial (ι × Fin n) R) (F : MvPolynomial (ι' × Fin n) R)
    (h : ∀ k, FinalFormK k (twistSub LL' S' j F) → FinalFormK k (twistSub LL S j G)) : sDegs LL S j G ⊆ sDegs LL' S' j F := by
  intro k hk
  by_contra hk'
  exact ((notMem_sDegs_iff LL S j G k).2 (h k ((notMem_sDegs_iff LL' S' j F k).1 hk'))) hk

theorem val_lam_of_subset [NeZero n] {ι' : Type*} (LL : Letters ι) (S : Set ι) (LL' : Letters ι') (S' : Set ι')
    (G : MvPolynomial (ι × Fin n) R) (F : MvPolynomial (ι' × Fin n) R)
    (h : ∀ j, sDegs LL S j G ⊆ sDegs LL' S' j F) :
    valS LL' S' F ≤ valS LL S G ∧ lam1S LL S G ≤ lam1S LL' S' F :=
  ⟨Finset.inf_mono (h _), Finset.sup_mono (h _)⟩

end S

end Formalism.MainNotions.Proposition5Numerics
