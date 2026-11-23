import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem factor_through_fractionField_of_range :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (T : Scheme.{0})
      (g : T ⟶ Sp O), Set.range g ⊆ Set.range (spMap (algebraMap O K)) →
        ∃ f : T ⟶ Sp K, f ≫ spMap (algebraMap O K) = g := by
  intro O K _ _ _ _ _ T g hg
  let φ : O →+* Γ(T, ⊤) := ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ g.appTop).hom
  have hgφ : g = T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom φ) := by
    have h := Scheme.toSpecΓ_naturality g
    have e : g = g ≫ (Sp O).toSpecΓ ≫ Spec.map (Scheme.ΓSpecIso (CommRingCat.of O)).inv := by simp
    rw [e, ← Category.assoc, h, Category.assoc, ← Spec.map_comp]
    simp [φ]
  have hunit : ∀ b : nonZeroDivisors O, IsUnit (φ b) := by
    rintro ⟨b, hb⟩
    refine T.toRingedSpace.isUnit_of_isUnit_germ ⊤ (φ b) fun x hx => ?_
    have hmem : x ∈ T.basicOpen (φ b) := by
      have e : T.basicOpen (φ b) = g ⁻¹ᵁ (Sp O).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv b) := by
        rw [Scheme.preimage_basicOpen_top]; rfl
      rw [e]
      show g x ∈ (Sp O).basicOpen _
      rw [basicOpen_eq_of_affine (R := CommRingCat.of O) b]
      obtain ⟨y, hy⟩ := hg ⟨x, rfl⟩
      show b ∉ (g x).asIdeal
      rw [← hy]
      intro hbm
      have hbm' : algebraMap O K b ∈ y.asIdeal := hbm
      have hu : IsUnit (algebraMap O K b) :=
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb).isUnit
      exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hbm' hu)
    exact (T.mem_basicOpen (φ b) x hx).1 hmem
  let ψ : K →+* Γ(T, ⊤) := IsLocalization.lift (M := nonZeroDivisors O) hunit
  refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), ?_⟩
  rw [hgφ, Category.assoc, ← Spec.map_comp]
  congr 2
  ext b
  simp [ψ]

end GlobalTheory
