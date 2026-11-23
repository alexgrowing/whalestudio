import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeMackey
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology
import GroundTheory.ProfiniteCohomology.LocalTateDuality.TensorHomDualRepRootsOfUnityIsoCartierPairing
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain CategoryTheory GroundTheory.Global FiniteSubfield

local notation "ℚ̄" => AlgebraicClosure ℚ

universe u

section Abstract

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type u} {H : ι → Type u} [∀ v, Group (H v)] [∀ v, TopologicalSpace (H v)]
  [∀ v, IsTopologicalGroup (H v)] (φ : ∀ v, H v →ₜ* G)
  (A : Rep.{u} k G) [IsDiscreteRep A] (Aᵥ : ∀ v, Rep.{u} k (H v)) [∀ v, IsDiscreteRep (Aᵥ v)]
  (a : ∀ v, Rep.res (φ v).toMonoidHom A ⟶ Aᵥ v)

theorem finite_compactCohomology [Finite ι] (n : ℕ) [Finite (cohomology A n)]
    (hloc : ∀ m, m + 1 = n → ∀ v, Finite (cohomology (Aᵥ v) m)) :
    Finite (compactCohomology φ A Aᵥ a n) := by
  cases n with
  | zero =>
    have := mono_compactToGlobal_zero φ A Aᵥ a
    exact Finite.of_injective _ ((ModuleCat.mono_iff_injective _).1 this)
  | succ m =>
    have : ∀ v, Finite (cohomology (Aᵥ v) m) := hloc m rfl
    have : Finite (ModuleCat.of k (∀ v, cohomology (Aᵥ v) m)) :=
      inferInstanceAs (Finite (∀ v, cohomology (Aᵥ v) m))
    exact finite_of_exact (localToCompact φ A Aᵥ a m).hom.toAddMonoidHom
      (compactToGlobal φ A Aᵥ a (m + 1)).hom.toAddMonoidHom
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
        (compactCohomology_exact_compact φ A Aᵥ a m))

end Abstract

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) [Finite S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

theorem finite_compactCohomologyRes_gs_of_finite
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (r : ℕ) [Finite (cohomology M r)] :
    Finite (compactCohomologyRes (gsFinFamily S ιs) M r) := by
  refine finite_compactCohomology _ M _ _ r fun m _ v => ?_
  have : Finite (Rep.res (gsFinFamily S ιs v).toMonoidHom M) := inferInstanceAs (Finite M)
  refine finite_cohomology_localField _ (by
    change ((Nat.card M : ℕ) : (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≠ 0
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne') m

theorem finite_compactCohomologyRes_gs
    (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
    (r : ℕ) (hr : r ≤ 2) :
    Finite (compactCohomologyRes (gsFinFamily S ιs) M r) := by
  have := finite_cohomology_gs K S M hS r hr
  exact finite_compactCohomologyRes_gs_of_finite K S ιs M r

end GroundTheory.ProfCoh
