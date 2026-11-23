import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem surjective_spMap_of_sq {A B : Type} [CommRing A] [CommRing B] (π : A →+* B) (hπ : Function.Surjective π)
    (hsq : ∀ a ∈ RingHom.ker π, a * a = 0) : Function.Surjective (spMap π) := fun x ↦ by
  have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker π : Set A) := fun a ha ↦
    (x.isPrime.mem_or_mem ((hsq a ha).symm ▸ x.asIdeal.zero_mem)).elim id id
  rw [← range_comap_of_surjective B π hπ] at hx
  exact hx

theorem pt_dual_le_of_fst : ∀ (R : Type) [CommRing R] (H : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D]
      (Z : Pt H (DualNumber D)) (U : H.left.Opens),
      ⊤ ≤ (spOver (TrivSqZeroExt.fstHom R D D) ≫ Z).left ⁻¹ᵁ U → ⊤ ≤ Z.left ⁻¹ᵁ U := by
  intro R _ H D _ _ Z U h x _
  have hs : Function.Surjective (spMap ((TrivSqZeroExt.fstHom R D D : DualNumber D →ₐ[R] D) : DualNumber D →+* D)) :=
    surjective_spMap_of_sq _ (fun d ↦ ⟨TrivSqZeroExt.inl d, rfl⟩) fun a ha ↦ by
      have h0 : a.fst = 0 := ha
      ext <;> simp [h0]
  obtain ⟨y, rfl⟩ := hs x
  have hy := h (show y ∈ (⊤ : (Sp D).Opens) from trivial)
  simpa [Over.comp_left, PDiv.spOver_left] using hy

end GlobalTheory.PtExt
