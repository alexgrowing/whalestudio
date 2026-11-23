import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfDirectedEssentiallyEtaleUnionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationDirectedUnionEssEtaleLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleOverDirectedUnionEssEtaleLocalStatement
open IsLocalRing

namespace GlobalTheory

theorem localDecomp_indEtale : ∀ (R S T : Type) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra S T] [Algebra R T] [IsScalarTower R S T], (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧ ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i))) → ∀ (U : Subalgebra S T) (B : Type) [CommRing B] [Algebra S B] [Algebra.Etale S B] (Q : Ideal B) [Q.IsPrime], Nonempty (Localization.AtPrime Q ≃ₐ[S] U) → ∃ (μ : Type) (_ : Preorder μ) (_ : IsDirected μ (· ≤ ·)) (_ : Nonempty μ) (V : μ → Subalgebra R T), Monotone V ∧ (∀ m, V m ≤ U.restrictScalars R) ∧ (∀ x ∈ U, ∃ m, x ∈ V m) ∧ (∀ m, ∀ x ∈ V m, ∀ y ∈ U, x * y = 1 → ∃ z ∈ V m, x * z = 1) ∧ ∀ m, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] V m)) := by
  intro R S T _ _ _ _ _ _ _ hS U B _ _ _ Q _ hf
  obtain ⟨f⟩ := hf
  letI : Algebra R B := ((algebraMap S B).comp (algebraMap R S)).toAlgebra
  haveI : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨ι, _, _, _, C, hCm, hCc, hCe⟩ := GlobalTheory.T.etale_over_directedUnion_essEtale_local R S B hS
  have hCe' : ∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B)))) :=
    fun i => hCe i _ inferInstance
  have hann := GlobalTheory.T.annihilator_of_directed_essentiallyEtale_union R B Q ι C hCm hCc hCe'
  obtain ⟨μ, _, _, _, W, hWm, hWc, hWu, hWe⟩ := GlobalTheory.T.localization_directedUnion_essEtale_local R B Q ι C hCm hCc hCe' hann
  let g : Localization.AtPrime Q →ₐ[R] T :=
    { toRingHom := U.val.toRingHom.comp f.toRingHom
      commutes' := fun r => by
        show ((f (algebraMap R _ r) : U) : T) = algebraMap R T r
        rw [IsScalarTower.algebraMap_apply R S (Localization.AtPrime Q), f.commutes,
          IsScalarTower.algebraMap_apply R S T]
        rfl }
  have hg : ∀ x, g x = ((f x : U) : T) := fun _ => rfl
  have hinj : Function.Injective g := fun x y h => f.injective (Subtype.ext (by simpa [hg] using h))
  refine ⟨μ, inferInstance, inferInstance, inferInstance, fun m => (W m).map g, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun m n h => Subalgebra.map_mono (hWm h)
  · rintro m x ⟨w, -, rfl⟩
    exact (f w).2
  · intro x hx
    obtain ⟨m, hm⟩ := hWc (f.symm ⟨x, hx⟩)
    exact ⟨m, f.symm ⟨x, hx⟩, hm, by simp [hg]⟩
  · rintro m x ⟨w, hw, rfl⟩ y hy hxy
    have h1 : f w * ⟨y, hy⟩ = 1 := Subtype.ext (by simpa [hg] using hxy)
    have hu : IsUnit w := by
      have h2 : w * f.symm ⟨y, hy⟩ = 1 := by apply f.injective; simpa using h1
      exact ⟨⟨w, _, h2, by rw [mul_comm]; exact h2⟩, rfl⟩
    obtain ⟨z, hz, hwz⟩ := hWu m w hw hu
    exact ⟨g z, ⟨z, hz, rfl⟩, by show g w * g z = 1; rw [← map_mul, hwz, map_one]⟩
  · intro m
    obtain ⟨A, _, _, _, q, _, ⟨e⟩⟩ := hWe m
    exact ⟨A, inferInstance, inferInstance, inferInstance, q, inferInstance,
      ⟨e.trans (Subalgebra.equivMapOfInjective (W m) g hinj)⟩⟩

end GlobalTheory
