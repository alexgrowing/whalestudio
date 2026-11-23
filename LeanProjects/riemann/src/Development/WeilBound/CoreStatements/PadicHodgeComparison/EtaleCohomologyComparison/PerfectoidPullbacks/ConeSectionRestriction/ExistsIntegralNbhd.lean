import Mathlib

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace CrystallineSemistableComparison.Pb.EtaleIntegralityFacts

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in

theorem exists_integral_nbhd {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [Smooth q]
    (hE : ∀ (A : Type) [CommRing A] [Algebra K A] [Algebra.Smooth K A] (p : Ideal A) [p.IsPrime],
      ∃ r ∉ p, ∀ (S : Type) [CommRing S] [Algebra A S] [IsLocalization.Away r S], IsDomain S)
    (x : X) : ∃ W : X.Opens, x ∈ W ∧ IsIntegral W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hVU : V ≤ q ⁻¹ᵁ ⊤ := fun _ _ => trivial
  have hsm := q.smooth_appLE (isAffineOpen_top (Spec (CommRingCat.of K))) hV hVU
  let φ : K →+* Γ(X, V) :=
    (q.appLE ⊤ V hVU).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hφ : φ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective)
    hsm
  let := φ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hφ
  obtain ⟨r, hr, hdom⟩ := hE Γ(X, V) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have hxW : x ∈ X.basicOpen r := by
    rwa [← PrimeSpectrum.mem_basicOpen, IsAffineOpen.primeIdealOf,
      ← hV.fromSpec_preimage_basicOpen, Scheme.Hom.mem_preimage, ← Scheme.Hom.comp_apply,
      IsAffineOpen.isoSpec_hom, IsAffineOpen.toSpecΓ_fromSpec] at hr
  refine ⟨X.basicOpen r, hxW, ?_⟩
  have hW : IsAffineOpen (X.basicOpen r) := hV.basicOpen r
  have : IsAffine (X.basicOpen r) := hW
  have : Nonempty (X.basicOpen r) := ⟨⟨x, hxW⟩⟩
  let := (X.presheaf.map (homOfLE <| X.basicOpen_le r).op).hom.toAlgebra
  have := hV.isLocalization_basicOpen r
  have : IsDomain Γ(X, X.basicOpen r) := hdom _
  have : IsDomain Γ(X.basicOpen r, ⊤) :=
    (X.basicOpen r).topIso.commRingCatIsoToRingEquiv.injective.isDomain
      (X.basicOpen r).topIso.commRingCatIsoToRingEquiv
  exact isIntegral_of_isAffine_of_isDomain _

end CrystallineSemistableComparison.Pb.EtaleIntegralityFacts
