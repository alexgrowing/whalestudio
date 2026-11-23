import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualFor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsSelfDualOfHasConductor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierTransformInversionLocalFieldPi
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.WeylFour

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {F : Type} [Field F] [NumberField F]

theorem exists_circle_conductor (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    ∃ (χ : AddChar (Fv F v) Circle) (c : (Fv F v)ˣ), GlobalTheory.SplitWeil.HasConductor χ c ∧
      ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := by
  have hc : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ v
  let χ : AddChar (Fv F v) Circle :=
    { toFun := fun x => ⟨GlobalTheory.LatVac.psiAt ψ v x, mem_sphere_zero_iff_norm.2 (GlobalTheory.norm_addChar_nonarch _ hc x)⟩
      map_zero_eq_one' := Circle.ext (by simp)
      map_add_eq_mul' := fun a b => Circle.ext (AddChar.map_add_eq_mul _ a b) }
  have hχ : ∀ x, (χ x : ℂ) = GlobalTheory.LatVac.psiAt ψ v x := fun _ => rfl
  have hχc : Continuous χ := continuous_induced_rng.2 hc
  have hχ1 : χ ≠ 1 := fun h => by
    obtain ⟨x, hx⟩ := h1
    refine hx ?_
    rw [← GlobalTheory.LatVac.psiAt_apply, ← hχ, h]
    simp
  obtain ⟨c, hc0⟩ := GlobalTheory.SplitWeil.exists_hasConductor_of_continuous χ hχc hχ1
  exact ⟨χ, c, hc0, hχ⟩

theorem isSelfDualFor_measV (ψ : AddChar (AF F) ℂ) (hψ : Continuous ψ) (v : Pl F) (h1 : ∃ x, psiLoc ψ v x ≠ 1) :
    IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) (measV ψ v) := by
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ v h1
  have h : ∃ ν, IsSelfDualFor (GlobalTheory.LatVac.psiAt ψ v) ν := by
    haveI : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitWeil.exists_isSelfDual_of_hasConductor hc
    refine ⟨ν, hν.1, fun f hf => ?_⟩
    simpa only [hχ] using hν.2 f hf
  rw [measV, dif_pos h]
  exact h.choose_spec

theorem fourV_sb : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F, (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ],
    (∀ φ ∈ SB (κ → Fv F v), fourV ψ v φ ∈ SB (κ → Fv F v)) ∧
    (∀ φ ∈ SB (κ → Fv F v), ∀ χ ∈ SB (κ → Fv F v), fourV ψ v (φ + χ) = fourV ψ v φ + fourV ψ v χ) ∧
    ∀ (w : (κ → Fv F v) × (κ → Fv F v)), ∀ φ ∈ SB (κ → Fv F v), schr (GlobalTheory.LatVac.psiAt ψ v) w φ ∈ SB (κ → Fv F v) := by
  intro F _ _ ψ hψ v h1 κ _
  classical
  have hcont : Continuous (GlobalTheory.LatVac.psiAt ψ v) := GlobalTheory.VacAny.continuous_psiV hψ.1 v
  obtain ⟨χ, c, hc, hχ⟩ := exists_circle_conductor ψ hψ.1 v h1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI : SecondCountableTopology (Fv F v) := GlobalTheory.SplitWeil.secondCountable _
  haveI := (isSelfDualFor_measV ψ hψ.1 v h1).1
  refine ⟨fun φ hφ => ?_, fun φ hφ φ' hφ' => ?_, fun w φ hφ => GlobalTheory.SchrSBFin.schr_mem_SB v _ hcont w φ hφ⟩
  · have h := GlobalTheory.SplitWeil.FourierPi.fourier_mem_SB (Measure.pi fun _ : κ => measV ψ v) hc hφ
    simp only [hχ] at h
    exact h
  · have hint : ∀ f ∈ SB (κ → Fv F v), ∀ y : κ → Fv F v,
        Integrable (fun x => f x * GlobalTheory.LatVac.psiAt ψ v (x ⬝ᵥ y)) (Measure.pi fun _ : κ => measV ψ v) := fun f hf y =>
      Continuous.integrable_of_hasCompactSupport
        (hf.1.continuous.mul (hcont.comp (continuous_id.dotProduct continuous_const))) hf.2.mul_right
    funext y
    simp only [fourV, Pi.add_apply, add_mul]
    exact integral_add (hint φ hφ y) (hint φ' hφ' y)

end GlobalTheory.WeylFour

end
