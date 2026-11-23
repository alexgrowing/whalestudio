import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.BddInt
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.KkCpt
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

private lemma eq_one_of_mul' {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a b : Γ}
    (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) : a = 1 := by
  refine le_antisymm ha ?_
  have := mul_le_mul' (le_refl a) hb
  rwa [h, mul_one] at this

private lemma mem_UU_iff' (t : IdeleGroup ℚ) :
    t ∈ UU ↔ IdeleGroup.toInfinite ℚ t = 1 ∧ IdeleGroup.toFinite ℚ t ∈ finiteIntegralUnits ℚ := by
  have hinv : ∀ v : H.P ℚ, Valued.v ((((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) * Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
      FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := by
    intro v
    rw [← map_mul]
    have h := congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) (Units.inv_mul (IdeleGroup.toFinite ℚ t))
    have h' : (((IdeleGroup.toFinite ℚ t)⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v *
        ((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := h
    rw [h', map_one]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨Units.ext h1, (mem_finiteIntegralUnits ℚ).2 fun v => ?_⟩
    have hv : Valued.v (((IdeleGroup.toFinite ℚ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
        FiniteAdeleRing (𝓞 ℚ) ℚ) v) = 1 := h2 v
    have hi := hinv v
    rw [hv, mul_one] at hi
    exact ⟨(HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hv.le,
      (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).2 hi.le⟩
  · rintro ⟨h1, h2⟩
    refine ⟨congrArg Units.val h1, fun v => ?_⟩
    obtain ⟨ha, hb⟩ := (mem_finiteIntegralUnits ℚ).1 h2 v
    exact eq_one_of_mul' ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 ha)
      ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 ℚ) ℚ v).1 hb) (by rw [mul_comm]; exact hinv v)

private lemma ofFinite_toFinite' {t : IdeleGroup ℚ} (h : IdeleGroup.toInfinite ℚ t = 1) :
    IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ t) = t := by
  refine (IdeleGroup.prodEquiv ℚ).injective (Prod.ext ?_ ?_)
  · change IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite _) = IdeleGroup.toInfinite ℚ t
    rw [IdeleGroup.toInfinite_ofFinite, h]
  · change IdeleGroup.toFinite ℚ (IdeleGroup.ofFinite _) = IdeleGroup.toFinite ℚ t
    rw [IdeleGroup.toFinite_ofFinite]

private lemma ab_ofFinite' {z : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ}
    (hz : z ∈ finiteIntegralUnits ℚ) : ab (IdeleGroup.ofFinite z : IdeleGroup ℚ) = 1 := by
  have hmem : (IdeleGroup.ofFinite z : IdeleGroup ℚ) ∈ IdeleGroup.standardOpenSubgroup ℚ := hz
  have hinf : IdeleGroup.infiniteModule (IdeleGroup.ofFinite z : IdeleGroup ℚ) = 1 := by
    have e : ((IdeleGroup.ofFinite z : IdeleGroup ℚ) : NumberField.AdeleRing (𝓞 ℚ) ℚ).1 = 1 := by
      change ((IdeleGroup.toInfinite ℚ (IdeleGroup.ofFinite z) : (InfiniteAdeleRing ℚ)ˣ) : InfiniteAdeleRing ℚ) = 1
      rw [IdeleGroup.toInfinite_ofFinite, Units.val_one]
    simp only [IdeleGroup.infiniteModule, e]
    exact Finset.prod_eq_one fun w _ => by
      rw [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]
  unfold ab
  rw [IdeleGroup.ideleModule_apply, hinf, IdeleGroup.finiteModule_eq_one_of_mem hmem, one_mul]

theorem UpperTheory.isCompact_integralIdeleUnits_and_abs_eq_one :
    IsCompact UU ∧ ∀ u ∈ UU, ab u = 1 := by
  have hset : (UU : Set (IdeleGroup ℚ)) =
      (fun z => (IdeleGroup.ofFinite z : IdeleGroup ℚ)) '' (finiteIntegralUnits ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨h1, h2⟩ := (mem_UU_iff' t).1 ht
      exact ⟨_, h2, ofFinite_toFinite' h1⟩
    · rintro ⟨z, hz, rfl⟩
      refine (mem_UU_iff' _).2 ⟨IdeleGroup.toInfinite_ofFinite _, ?_⟩
      change IdeleGroup.toFinite ℚ (IdeleGroup.ofFinite z) ∈ _
      rwa [IdeleGroup.toFinite_ofFinite]
  refine ⟨?_, fun u hu => ?_⟩
  · rw [hset]
    exact (isCompact_finiteIntegralUnits ℚ).image IdeleGroup.continuous_ofFinite
  · obtain ⟨h1, h2⟩ := (mem_UU_iff' u).1 hu
    rw [← ofFinite_toFinite' h1]
    exact ab_ofFinite' h2
