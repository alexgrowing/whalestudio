import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssEtaleLocalLeOfDirectedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalRingEtaleOverIndEtaleDirectedUnionStatement
open IsLocalRing

namespace GlobalTheory

theorem indEtale_localPieces_trans : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra S T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra S A) (_ : Algebra.Etale S A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[S] Si i)) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R T), Monotone Si ∧ (∀ s : T, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)) := by
  intro R S T _ _ _ _ _ _ _ hS hT
  obtain ⟨κ, _, _, _, Tj, hmono, hcov, hpc⟩ := hT
  have hK : ∀ j, ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ)
      (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ (Tj j).restrictScalars R) ∧
      (∀ x ∈ Tj j, ∃ m, x ∈ V m) ∧
      (∀ m, ∀ x ∈ V m, ∀ y ∈ Tj j, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
    intro j
    obtain ⟨B, _, _, _, Q, _, ⟨e⟩⟩ := hpc j
    exact GlobalTheory.T.localRing_etale_over_indEtale_directedUnion R S T hS (Tj j) B Q ⟨e⟩
  choose μ pre dir ne V hVmono hVle hVcov hVloc hVee using hK
  let P : Subalgebra R T → Prop := fun W => ∃ (j : κ) (m : μ j), V j m = W
  have key : ∀ (j₁ : κ) (m₁ : μ j₁) (j : κ), j₁ ≤ j → ∃ m : μ j, V j₁ m₁ ≤ V j m := by
    intro j₁ m₁ j hj
    letI := pre j; haveI := dir j; haveI := ne j
    refine GlobalTheory.T.exists_le_of_essEtaleLocal_directed R T ((Tj j).restrictScalars R) (μ j) (V j) (hVmono j) ?_ ?_ (V j₁ m₁) ?_
      (hVee j₁ m₁)
    · intro x hx; exact hVcov j x hx
    · intro m x hx y hy hxy; exact hVloc j m x hx y hy hxy
    · intro x hx
      have := hVle j₁ m₁ hx
      exact hmono hj this
  refine ⟨{W : Subalgebra R T // P W}, inferInstance, ⟨?_⟩, ?_, Subtype.val, fun a b h => h, ?_, ?_⟩
  · rintro ⟨W₁, j₁, m₁, rfl⟩ ⟨W₂, j₂, m₂, rfl⟩
    obtain ⟨j, h₁, h₂⟩ := directed_of (· ≤ ·) j₁ j₂
    obtain ⟨a, ha⟩ := key j₁ m₁ j h₁
    obtain ⟨b, hb⟩ := key j₂ m₂ j h₂
    letI := pre j; haveI := dir j
    obtain ⟨c, hac, hbc⟩ := directed_of (· ≤ ·) a b
    exact ⟨⟨V j c, j, c, rfl⟩, ha.trans (hVmono j hac), hb.trans (hVmono j hbc)⟩
  · obtain ⟨j⟩ := (inferInstance : Nonempty κ)
    obtain ⟨m⟩ := ne j
    exact ⟨⟨V j m, j, m, rfl⟩⟩
  · intro t
    obtain ⟨j, hj⟩ := hcov t
    obtain ⟨m, hm⟩ := hVcov j t hj
    exact ⟨⟨V j m, j, m, rfl⟩, hm⟩
  · rintro ⟨W, j, m, rfl⟩
    exact hVee j m

end GlobalTheory
