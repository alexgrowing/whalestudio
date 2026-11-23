import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ConcretePkgSpec
import Formalism.LocalToGlobal.IndefiniteReal.CutTuples2
import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAntiInvolutionOfChars
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DiscreteCountableGQ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffSetIntegralNat

namespace GlobalTheory.RowPartsOrth

section Generic
open MeasureTheory Formalism.IndefR.Bridge GlobalTheory.DoubleCosetAdjoint

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [MeasurableSpace H]
  [BorelSpace H] (μ : Measure H) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
  (Γ : Subgroup H) [Countable Γ] (𝓕 : Set H)

def Sq (F : H → ℂ) : Prop :=
  Continuous F ∧ (∀ γ ∈ Γ, ∀ h, F (γ * h) = F h) ∧ IntegrableOn (fun h => star (F h) * F h) 𝓕 μ

variable {μ Γ 𝓕}

omit [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] in
theorem Sq.int {F F' : H → ℂ} (h : Sq μ Γ 𝓕 F) (h' : Sq μ Γ 𝓕 F') :
    IntegrableOn (fun g => star (F g) * F' g) 𝓕 μ :=
  integrableOn_star_mul μ 𝓕 F F' h.1 h'.1 h.2.2 h'.2.2

omit [IsTopologicalGroup H] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [Countable Γ] in
theorem Sq.add {F F' : H → ℂ} (h : Sq μ Γ 𝓕 F) (h' : Sq μ Γ 𝓕 F') : Sq μ Γ 𝓕 (fun g => F g + F' g) := by
  refine ⟨h.1.add h'.1, fun γ hγ g => by simp only [h.2.1 γ hγ, h'.2.1 γ hγ], ?_⟩
  have := ((h.int h).add (h.int h')).add ((h'.int h).add (h'.int h'))
  refine this.congr (Filter.Eventually.of_forall fun g => ?_)
  simp only [Pi.add_apply, star_add]
  ring

theorem Sq.transl (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {F : H → ℂ} (h : Sq μ Γ 𝓕 F) (y : H) :
    Sq μ Γ 𝓕 (fun g => F (g * y)) :=
  ⟨h.1.comp (continuous_mul_right y), fun γ hγ g => by simp only [mul_assoc, h.2.1 γ hγ],
    integrableOn_mul_right μ Γ 𝓕 h𝓕 (fun h => star (F h) * F h) (fun γ hγ g => by simp only [h.2.1 γ hγ]) y h.2.2⟩

theorem Sq.sum (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {F : H → ℂ} (h : Sq μ Γ 𝓕 F) (A : Finset H) :
    Sq μ Γ 𝓕 (fun g => ∑ a ∈ A, F (g * a)) := by
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨by simpa using continuous_const, by simp, by simp⟩
  | insert a A ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h.transl h𝓕 a).add ih

theorem isDC_of_local {H : Type} [Group H] (J L : Subgroup H) (x : H) (A : Finset H) (hx : x ∈ L)
    (hs : ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l)
    (hL : ∀ a ∈ A, a ∈ L) (hA : IsDC (J ⊓ L) x A) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, k₂, e⟩ := hA.1 a ha
    exact ⟨⟨k₁, k₁.2.1⟩, ⟨k₂, k₂.2.1⟩, e⟩
  · rintro g ⟨k₁, k₂, rfl⟩
    obtain ⟨a, ha, b, hb, haL, e, hc⟩ := hs k₁ k₁.2
    have e2 : (k₁ : H) * x * k₂ = a * x * (b * k₂) := by
      rw [e, mul_assoc a b x, (hc x hx).eq]; simp only [mul_assoc]
    obtain ⟨r, ⟨hr, hr2⟩, hu⟩ := hA.2 (a * x) ⟨⟨a, ha, haL⟩, 1, by simp⟩
    rw [e2]
    refine ⟨r, ⟨hr, ?_⟩, fun r' hr' => hu r' ⟨hr'.1, ?_, ?_⟩⟩
    · have := J.mul_mem hr2.1 (J.mul_mem hb k₂.2)
      simpa only [mul_assoc] using this
    · have := J.mul_mem hr'.2 (J.inv_mem (J.mul_mem hb k₂.2))
      simpa [mul_assoc] using this
    · exact L.mul_mem (L.inv_mem (hL r' hr'.1)) (L.mul_mem haL hx)

end Generic

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx NumberField IsDedekindDomain Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

end GlobalTheory.RowPartsOrth
