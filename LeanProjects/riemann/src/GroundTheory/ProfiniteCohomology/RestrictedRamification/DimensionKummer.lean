import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.ExistsNsmulEqLocalPrimaryKernel
import GroundTheory.ProfiniteCohomology.CohomologicalDimension.SubsingletonCohomologyOfPrimaryOfFinite
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem nsmul_rootsOfUnity_eq_zero {E : Type*} [CommMonoid E] (ℓ : ℕ)
    (a : Additive (rootsOfUnity ℓ E)) : ℓ • a = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_zero]
  exact Subtype.ext ((mem_rootsOfUnity ℓ _).1 (Additive.toMul a).2)

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {E : ShortComplex (Rep.{0} (ULift.{0} ℤ) G)} [IsDiscreteRep E.X₁]
  [IsDiscreteRep E.X₂] [IsDiscreteRep E.X₃]

theorem eq_zero_h3_of_shortExact (hE : E.ShortExact) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hX : ∀ a : E.X₁, ℓ • a = 0) (h3 : ∀ z : cohomology E.X₂ 3, ℓ • z = 0 → z = 0)
    (hdiv : ∀ y : cohomology E.X₃ 2, (∃ j : ℕ, ℓ ^ j • y = 0) →
      ∃ z : cohomology E.X₂ 2, (cohomologyMap E.g 2).hom z = y)
    (x : cohomology E.X₁ 3) : x = 0 := by
  have hfx : (cohomologyMap E.f 3).hom x = 0 := by
    refine h3 _ ?_
    rw [← map_nsmul, nsmul_cohomology_eq_zero _ hX 3 x, map_zero]
  obtain ⟨y, rfl⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hE 2 3 rfl x hfx
  have hyt : IsOfFinAddOrder y := isTorsion_cohomology _ (by norm_num) y
  have hδℓ : ℓ ^ 1 • (δ hE 2 3 rfl).hom.toAddMonoidHom y = 0 := by
    rw [pow_one]
    exact nsmul_cohomology_eq_zero _ hX 3 _
  obtain ⟨y', hj, hy'⟩ := exists_primary_map_eq (δ hE 2 3 rfl).hom.toAddMonoidHom hℓ hyt hδℓ
  change (δ hE 2 3 rfl).hom y = 0
  rw [← show (δ hE 2 3 rfl).hom y' = (δ hE 2 3 rfl).hom y from hy']
  obtain ⟨z, rfl⟩ := hdiv y' hj
  rw [← ModuleCat.comp_apply, comp_δ]
  rfl

end Abstract

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 1000000 in
include hℓ hS in

theorem eq_zero_h3_rootsOfUnity_of_h3_sUnits (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (h3 : ∀ z : cohomology (galSUnitsMax K.1 ℚ̄ S) 3, ℓ • z = 0 → z = 0)
    (x : cohomology (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 3) : x = 0 := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hE := sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ (fun v hv h => hv (hS v h))
  refine eq_zero_h3_of_shortExact (E := sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) hE hℓ (nsmul_rootsOfUnity_eq_zero ℓ) h3 (fun y hy => ?_) x
  obtain ⟨z, hz⟩ := exists_nsmul_eq_h2SUnits K S ℓ hℓ hS hK ⟨y, hy⟩
  refine ⟨z.1, ?_⟩
  rw [sUnitsKummerSequence_g]
  exact (cohomologyMap_nsmul_id_apply _ ℓ 2 z.1).trans (congrArg Subtype.val hz)

end

end GroundTheory.ProfCoh
