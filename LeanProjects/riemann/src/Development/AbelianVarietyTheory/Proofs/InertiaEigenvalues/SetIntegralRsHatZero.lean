import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TsumRsPsiEqTsumNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MspanLeBddForms
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBddFormsOfWithSmoothings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFiniteMeasureQuotMeasure
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors

open GlobalTheory.RSTheta GlobalTheory.ThetaPoisson GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix GroundTheory.Global
open scoped ComplexConjugate

noncomputable section

namespace GlobalTheory.RSResidue

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem mem_bddForms {π : CuspSub E a} {ω : HChar E} (hω : ω.IsUnitary) (h : π.HasCentChar ω) {φ : Sm E a}
    (hφ : φ ∈ π.V ∨ φ.1 ∈ GlobalTheory.JSW.mspan π) : φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω :=
  hφ.elim (fun h' => GlobalTheory.Petersson.mem_bddForms_of_cuspSub GlobalTheory.CuspOrth.cuspFormsBounded hω h h')
    (fun h' => GlobalTheory.JSWPos.mspan_le_bddForms hω h h')

theorem rsHat_zero {ℓ : Fin a} {Φ : (Fin a → Cinf E) → ℂ} (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E)
    (F F' : Sm E a) (hΦ : GlobalTheory.CuspQuot.IsTest (rowSet E ℓ) Φ) (g : GA E a) :
    adelicFourierPi E (rsPsi ℓ F.1 F'.1 Φ J η g) 0 =
      (∫ x, rsInf ℓ F.1 F'.1 Φ g x ∂infMeasure E a) * ((finiteMeasurePi E (latt a J)).toReal : ℂ) := by
  have h := rsHat_eq J η F F' hΦ g 0
  simp only [rsHat] at h
  rw [h]
  have h0 : (fun i => pFin E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h1 : (fun i => pInf E ((0 : Fin a → Ad E) i)) = 0 := funext fun _ => map_zero _
  have h2 : (latt a (traceDualIdeal E J)).indicator (1 : (Fin a → Af E) → ℂ) 0 = 1 :=
    Set.indicator_of_mem (s := latt a (traceDualIdeal E J)) (show (0 : Fin a → Af E) ∈ latt a (traceDualIdeal E J) from
      fun i => (idealFiniteAdeles (traceDualIdeal E J)).zero_mem) _
  rw [h0, h1, h2]
  simp [infFourier]

theorem setIntegral_mul_right {μ : Measure (GA E a)} [μ.IsHaarMeasure] {𝓕 : Set (GA E a)}
    (h𝓕 : IsFundamentalDomain (latticeGL E a) 𝓕 μ) {f : GA E a → ℂ}
    (hf : ∀ γ ∈ latticeGL E a, ∀ g, f (γ * g) = f g) (h : GA E a) :
    ∫ g in 𝓕, f (g * h) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  haveI := GlobalTheory.CovolGL.isMulRightInvariant E a μ
  have hmp : MeasurePreserving (fun g => g * h) μ μ := measurePreserving_mul_right μ h
  have e1 := hmp.setIntegral_preimage_emb (measurableEmbedding_mulRight h) f ((fun g => g * h⁻¹) ⁻¹' 𝓕)
  have e2 : (fun g => g * h) ⁻¹' ((fun g => g * h⁻¹) ⁻¹' 𝓕) = 𝓕 := by ext; simp
  rw [e2] at e1
  rw [e1]
  have h2 : IsFundamentalDomain (latticeGL E a) ((fun g => g * h⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ h⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  haveI : DiscreteTopology (latticeGL E a) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  have hI : GlobalTheory.AutomorphicL2Unitary.LeftInv (latticeGL E a) f := hf
  have A := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h2 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  have B := (GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕 (GlobalTheory.AutomorphicL2Unitary.descend (latticeGL E a) f)).trans
    (integral_congr_ae (Eventually.of_forall hI.descend_mk))
  exact A.symm.trans B

end GlobalTheory.RSResidue
