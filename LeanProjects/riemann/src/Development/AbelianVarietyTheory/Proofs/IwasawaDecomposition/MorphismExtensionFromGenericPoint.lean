import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecMapFromSpecOfRangeSubset
open AlgebraicGeometry CategoryTheory Limits IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

theorem dvd_of_flat_local_map_dvd {A R : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R]
    (φ : A →+* R) (hf : φ.Flat) [hl : IsLocalHom φ] {a s : A} (h : φ s ∣ φ a) : s ∣ a := by
  letI := φ.toAlgebra
  haveI : Module.Flat A R := hf
  haveI : IsLocalHom (algebraMap A R) := hl
  haveI : Module.FaithfullyFlat A R := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hm : a ∈ Ideal.comap (algebraMap A R) (Ideal.map (algebraMap A R) (Ideal.span {s})) := by
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_comap, Ideal.mem_span_singleton]
    exact h
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat, Ideal.mem_span_singleton] at hm
  exact hm

theorem extension_descends_of_flat : ∀ (A R : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [CommRing R] [IsDomain R] [IsLocalRing R]
    (φ : A →+* R), φ.Flat → IsLocalHom φ → ∀ (γ : FractionRing A →+* FractionRing R),
    (∀ a, γ (algebraMap A _ a) = algebraMap R _ (φ a)) → ∀ (Y : Scheme.{0})
    (ψ₀ : Sp (FractionRing A) ⟶ Y) (χ : Sp R ⟶ Y), jK R ≫ χ = spMap γ ≫ ψ₀ →
    ∃ ψ : Sp A ⟶ Y, jK A ≫ ψ = ψ₀ ∧ spMap φ ≫ ψ = χ := by
  intro A R _ _ _ _ _ _ φ hf hl γ hg Y ψ₀ χ hc
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y)
    (x := χ (IsLocalRing.closedPoint R)) (U := ⊤) trivial
  have h2 : ∀ x, χ x ∈ U := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map χ.continuous).mem_open U.2 hxU
  have h1 : ∀ x, ψ₀ x ∈ U := by
    intro x
    obtain ⟨z⟩ : Nonempty (Sp (FractionRing R)) := ⟨IsLocalRing.closedPoint (FractionRing R)⟩
    have hx : x = spMap γ z :=
      Subsingleton.elim (α := PrimeSpectrum (FractionRing A)) _ _
    rw [hx, ← Scheme.Hom.comp_apply, ← hc, Scheme.Hom.comp_apply]
    exact h2 _
  obtain ⟨c, rfl⟩ := exists_specMap_fromSpec_of_range_subset χ hU h2
  obtain ⟨p, rfl⟩ := exists_specMap_fromSpec_of_range_subset ψ₀ hU h1
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ← Spec.map_comp, ← Spec.map_comp,
    Spec.map_inj] at hc
  have hb : ∀ b, algebraMap R (FractionRing R) (c.hom b) = γ (p.hom b) := fun b =>
    congrArg (fun t => t.hom b) hc
  have hi : ∀ b, ∃ t : A, algebraMap A (FractionRing A) t = p.hom b := by
    intro b
    obtain ⟨a, s, hs, hq⟩ := IsFractionRing.div_surjective A (p.hom b)
    have hs0 : algebraMap A (FractionRing A) s ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
    have hφs : algebraMap R (FractionRing R) (φ s) ≠ 0 := by
      rw [← hg]
      exact (map_ne_zero γ).2 hs0
    have key : φ a = c.hom b * φ s := by
      apply IsFractionRing.injective R (FractionRing R)
      have h1 := hb b
      rw [← hq, map_div₀, hg, hg] at h1
      rw [map_mul, h1, div_mul_cancel₀ _ hφs]
    obtain ⟨t, rfl⟩ := dvd_of_flat_local_map_dvd φ hf (Dvd.intro_left _ key.symm)
    refine ⟨t, ?_⟩
    rw [← hq]
    change _ = algebraMap A (FractionRing A) (s * t) / algebraMap A (FractionRing A) s
    rw [map_mul, mul_div_cancel_left₀ _ hs0]
  have hinj := IsFractionRing.injective A (FractionRing A)
  choose s hs using hi
  let ρ : Γ(Y, U) →+* A :=
    { toFun := s
      map_one' := hinj (by simp [hs])
      map_mul' := fun a b => hinj (by simp [hs])
      map_zero' := hinj (by simp [hs])
      map_add' := fun a b => hinj (by simp [hs]) }
  refine ⟨Spec.map (CommRingCat.ofHom ρ) ≫ hU.fromSpec, ?_, ?_⟩
  · rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext b
    exact hs b
  · rw [← Category.assoc, ← Spec.map_comp]
    congr 2
    ext b
    apply IsFractionRing.injective R (FractionRing R)
    show algebraMap R _ (φ (s b)) = algebraMap R _ (c.hom b)
    rw [hb, ← hs, hg]

end GlobalTheory
