import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnVanishingOnSubalgebraKilledSqStatement
open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_mem_span_of_trData : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S]
    [AddCommGroup M] [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → ∀ x ∈ C,
      (e * e) • D x ∈ Submodule.span S (D '' (B : Set S)) := by
  intro A S M _ _ _ _ _ B C tr n a b e ht D hD x hx
  set N : Submodule S M := Submodule.span S (D '' (B : Set S))
  have hD' : IsDerOn C (fun s => N.mkQ (D s)) :=
    { add := fun u hu v hv => by simp only [hD.add u hu v hv, map_add]
      mul := fun u hu v hv => by simp only [hD.mul u hu v hv, map_add, map_smul]
      alg := fun r => by simp only [hD.alg r, map_zero] }
  have hB : ∀ β ∈ B, N.mkQ (D β) = 0 := fun β hβ => by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨β, hβ, rfl⟩
  have h := GlobalTheory.T.derivationOn_vanishing_on_subalgebra_killed_sq A S (M ⧸ N) B C tr n a b e ht (fun s => N.mkQ (D s)) hD' hB x hx
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  exact h

end GlobalTheory.AlmostEt
