import Mathlib
import GroundTheory.ProfiniteCohomology.RealPlaces.GSDefs
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.ContinuousCochains.Functoriality
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))

section Places

variable (ι : ∀ v : InfinitePlace K.1, ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)

def gsInfFamily (v : InfinitePlace K.1) :
    Gal(AlgebraicClosure v.Completion / v.Completion) →ₜ* galUnramifiedOutside K.1 ℚ̄ S :=
  ⟨decompHomS v.Completion S (ι v), continuous_decompHomS (Kv := v.Completion) S (ι v)⟩

theorem gsInfFamily_real (v : {v : InfinitePlace K.1 // v.IsReal}) :
    gsInfFamily S ι v.1 = gsRealFamily S (fun w => ι w.1) v :=
  rfl

theorem eq_one_of_isComplex {v : InfinitePlace K.1} (hv : v.IsComplex)
    (σ : Gal(AlgebraicClosure v.Completion / v.Completion)) : σ = 1 := by
  have : IsAlgClosed v.Completion :=
    IsAlgClosed.of_ringEquiv ℂ _ (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).symm
  ext x
  obtain ⟨c, rfl⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral
    (k := v.Completion) (K := AlgebraicClosure v.Completion)).2 x
  simp

end Places

section Factor

variable (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M]

def gsRealH0Card
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion)
    (v : {v : InfinitePlace K.1 // v.IsReal}) : ℕ :=
  Nat.card (cohomology (Rep.res (gsRealFamily S ιr v).toMonoidHom M) 0)

def gsInfH0Card (ι : ∀ v : InfinitePlace K.1, ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion)
    (v : InfinitePlace K.1) : ℕ :=
  Nat.card (cohomology (Rep.res (gsInfFamily S ι v).toMonoidHom M) 0)

def gsEulerInfFactor (ι : ∀ v : InfinitePlace K.1, ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) : ℚ :=
  ∏ v : InfinitePlace K.1, (gsInfH0Card S M ι v : ℚ) / (Nat.card M : ℚ) ^ v.mult

open scoped Classical in

def gsEulerRatio
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion) : ℚ :=
  eulerChar M * (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K.1) /
    ∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S M ιr v : ℚ)

end Factor

section Statement

open scoped Classical in

def GlobalEulerFormula
    (ιr : ∀ v : {v : InfinitePlace K.1 // v.IsReal}, ℚ̄ →ₐ[K.1] AlgebraicClosure v.1.Completion) :
    Prop :=
  ∀ (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M],
    (∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) →
      eulerChar M = (∏ v : {v : InfinitePlace K.1 // v.IsReal}, (gsRealH0Card S M ιr v : ℚ)) /
        (Nat.card M : ℚ) ^ Fintype.card (InfinitePlace K.1)

def GlobalEulerFormulaInf (ι : ∀ v : InfinitePlace K.1, ℚ̄ →ₐ[K.1] AlgebraicClosure v.Completion) :
    Prop :=
  ∀ (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S)) [IsDiscreteRep M] [Finite M],
    (∀ v : HeightOneSpectrum (𝓞 K.1), ((Nat.card M : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) →
      eulerChar M = gsEulerInfFactor S M ι

end Statement

end

end GroundTheory.ProfCoh
