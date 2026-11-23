import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KerDatTuple
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.LocalToGlobal.IndefiniteReal.RhoGeo
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseRatAtOfPhaseOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicLiftEqGeometricClassSumAllTuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameConstantsOfCharacterisationCore
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstUpToCenter
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Formalism.MirabolicMackeyTheory.MirabolicMackeyProofs.RamBasic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NotMemOfCoprime
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)

noncomputable section

namespace GlobalTheory.TameHeckeIntegral

open Formalism.L2.Host GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing GlobalTheory.ChiUnit

theorem unitOff_onId (E : Type) [Field E] [NumberField E] (ψ : HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ)
    (n : I → ℤ) (hinf : ψ.HasInf φs n) (ht : ∀ v, ψ.TameAt v) (b : ℕ) (hb : b ≠ 0)
    (hu : ∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) (cc : Ideal (𝓞 E)) (hcc : cc ≠ ⊥)
    (hcop : cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤) :
    UnitOff (Ideal.absNorm cc) ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ) := by
  classical
  have hb0 : (b : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hfin : {w | ¬ ψ.UnrAt w}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(b : 𝓞 E)}) (by simpa using hb0)).subset fun w hw => ?_
    have hbw : (b : 𝓞 E) ∈ w.asIdeal := by
      by_contra h
      exact hw (hu w h)
    show w.asIdeal ∣ Ideal.span {(b : 𝓞 E)}
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact hbw
  have hcc0 : cc ≠ 0 := hcc
  unfold HChar.onId
  refine finprod_induction (fun u : ℂˣ => UnitOff (Ideal.absNorm cc) (u : ℂ)) (by simpa using unitOff_one _)
    (fun x y hx hy => by simpa [Units.val_mul] using unitOff_mul hx hy) fun v => ?_
  show UnitOff _ (((ψ.val v ^ FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ)) : ℂ)
  rw [Units.val_zpow_eq_zpow_val]
  by_cases hdv : v.asIdeal ∣ cc
  · have hle : cc ≤ v.asIdeal := Ideal.le_of_dvd hdv
    have hbv : (b : 𝓞 E) ∉ v.asIdeal := fun h => v.isPrime.ne_top (by
      rw [eq_top_iff, ← hcop]
      exact sup_le hle (by rw [Ideal.span_singleton_le_iff_mem]; exact h))
    have hq : ((Ideal.absNorm cc : ℕ) : 𝓞 E) ∈ v.asIdeal := hle (Ideal.absNorm_mem cc)
    exact unitOff_zpow (GlobalTheory.ValUnit.unitOff_val E ψ I φs n v _ hinf hfin ht (hu v hbv) hq) _
  · have h0 : FractionalIdeal.count E v (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) = 0 := by
      rw [FractionalIdeal.count_coe E v hcc0, Nat.cast_eq_zero]
      by_contra h
      exact hdv ((Associates.count_ne_zero_iff_dvd hcc0 (HeightOneSpectrum.prime v).irreducible).1 h)
    rw [h0, zpow_zero]
    exact unitOff_one _

theorem isIntegral_absNorm_pow_mul_onId : ∀ (E : Type) [Field E] [NumberField E] (ψ : Formalism.L2.Host.HChar E) (I : Type) [Fintype I] (φs : I → E →+* ℂ) (n : I → ℤ), ψ.HasInf φs n → (∀ v, ψ.TameAt v) → ∀ b : ℕ, b ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 E), (b : 𝓞 E) ∉ v.asIdeal → ψ.UnrAt v) → ∀ cc : Ideal (𝓞 E), cc ≠ ⊥ → cc ⊔ Ideal.span {(b : 𝓞 E)} = ⊤ → ∃ K : ℕ, IsIntegral ℤ (((Ideal.absNorm cc : ℕ) : ℂ) ^ K * ((ψ.onId (cc : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ℂˣ) : ℂ)) := by
  intro E _ _ ψ I _ φs n hinf ht b hb hu cc hcc hcop
  obtain ⟨_, K, hK, _⟩ := unitOff_onId E ψ I φs n hinf ht b hb hu cc hcc hcop
  exact ⟨K, hK⟩

end GlobalTheory.TameHeckeIntegral
