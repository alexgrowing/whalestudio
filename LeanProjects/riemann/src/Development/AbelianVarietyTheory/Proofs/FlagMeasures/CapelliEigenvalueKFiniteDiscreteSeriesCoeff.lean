import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CapelliEigenvalues.Smooth
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliTransportUnitaryConjStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorOnUnitaryCoefficientEqDerivedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CapelliOperatorUnitaryGroupLocalStatement

open Matrix PI.UpqRep

namespace GlobalTheory.CapelliEigenvalue

open PI.UnitaryGroupMassFormula.CapelliEig

theorem coefSm_of (hT : CapTransport) (hF : FunAct) (hD : PI.DSInfCharCap.DSInfCharCap) : CoefSm := by
  intro k r ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hlam hds P Q hQ Y g hg
  obtain ⟨P₀, hcayU, hDS⟩ := hds
  obtain ⟨⟨hunit, hcay⟩, hPu⟩ := hcayU
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hleft : P₀⁻¹ * P₀ = 1 := Matrix.nonsing_inv_mul _ hdet
  have hright : P₀ * P₀⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm

  obtain ⟨hvec, hsm⟩ := smooth_translation k r ε Hs σ Wp Wq P₀ ⟨⟨hunit, hcay⟩, hPu⟩ P Q hQ

  have hgJ : Formalism.REAL.inUJ ε (P₀ * g * P₀⁻¹) := by
    have hg0 : gᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * g = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := by
      rw [← hH]; exact hg
    show (P₀ * g * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * g * P₀⁻¹) = Formalism.REAL.Jm ε
    calc (P₀ * g * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * g * P₀⁻¹)
        = (P₀⁻¹)ᴴ * (gᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * g) * P₀⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (P₀⁻¹)ᴴ * (P₀ᴴ * Formalism.REAL.Jm ε * P₀) * P₀⁻¹ := by rw [hg0]
      _ = (P₀ * P₀⁻¹)ᴴ * Formalism.REAL.Jm ε * (P₀ * P₀⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by
          rw [hright, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hback : P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = g := by
    calc P₀⁻¹ * (P₀ * g * P₀⁻¹) * P₀ = (P₀⁻¹ * P₀) * g * (P₀⁻¹ * P₀) := by
          simp only [Matrix.mul_assoc]
      _ = g := by rw [hleft, Matrix.one_mul, Matrix.mul_one]

  have hu : Y + (((2 * r + k : ℕ) : ℂ)) / 2 = Y + (((2 * r + k + 1 : ℕ) : ℂ) - 1) / 2 := by
    push_cast; ring

  have htr : Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
      (fun x => P.comp ((σ x).comp Q)) g =
      Formalism.QuantumDeterminants.capelli ε (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
        (fun x => P.comp ((σ (P₀⁻¹ * x * P₀)).comp Q)) (P₀ * g * P₀⁻¹) :=
    hT (2 * r + k + 1) ε (Wq →L[ℂ] Wp) (Formalism.QuantumDeterminants.Hpk k r) P₀ P₀⁻¹
      (fun x => P.comp ((σ x).comp Q)) _ g hleft hright hH hsm hg
  show Formalism.QuantumDeterminants.capelliH (Formalism.QuantumDeterminants.Hpk k r) (Y + (((2 * r + k : ℕ) : ℂ)) / 2)
      (fun x => P.comp ((σ x).comp Q)) g = _
  rw [htr]
  ext w
  rw [hF (2 * r + k + 1) ε lam Hs (fun x => σ (P₀⁻¹ * x * P₀)) Wp Wq hDS P Q hvec _ _ hgJ w]
  simp only [hback]
  rw [hu, hD (2 * r + k + 1) ε lam Hs (fun x => σ (P₀⁻¹ * x * P₀)) hlam hDS (Q w) (hvec w) Y]
  simp only [map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply]

theorem capEig_of_coefSm (hL : Loc) (hC : CoefSm) (hK : PI.KFinSmooth) : PI.CapelliEig.CapEig := by
  intro k r ε lam Hs _ _ _ σ Wp Wq _ _ _ _ _ _ hlam hds f hf Y g hg
  obtain ⟨a, ha, b, hb, P, Q, hQ, -, hfab⟩ := hf
  obtain ⟨hau, hainv, -⟩ := unitary_Hecke_group k r a ha
  obtain ⟨hbu, hbinv, -⟩ := unitary_Hecke_group k r b hb
  have hM := Hecke_multiplication k r ε lam Hs σ hds

  have hrep : ∀ x, Formalism.QuantumDeterminants.inUH (Formalism.QuantumDeterminants.Hpk k r) x →
      f x = (P.comp (σ a⁻¹)).comp ((σ x).comp ((σ b⁻¹).comp Q)) := by
    intro x hx
    have hxm : x ∈ UH (Hpk k r) := hx
    have hax : a⁻¹ * x ∈ UH (Hpk k r) := (unitary_Hecke_group k r a⁻¹ hainv).2.2 x hxm
    have hexp : a * (a⁻¹ * x * b⁻¹) * b = x := by
      calc a * (a⁻¹ * x * b⁻¹) * b = (a * a⁻¹) * x * (b⁻¹ * b) := by
            simp only [Matrix.mul_assoc]
        _ = x := by
            rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hau),
              Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hbu),
              Matrix.one_mul, Matrix.mul_one]
    have h1 : f (a * (a⁻¹ * x * b⁻¹) * b) = P.comp ((σ (a⁻¹ * x * b⁻¹)).comp Q) := hfab _
    rw [hexp, hM _ hax _ hbinv, hM _ hainv _ hxm] at h1
    rw [h1]
    ext v
    simp only [ContinuousLinearMap.comp_apply]

  have hQ' : ∀ w, ((σ b⁻¹).comp Q) w ∈ smoothVecs (k := k) (r := r) σ := fun w =>
    smooth_right_action k r ε lam Hs σ hds (Q w) (hK k r ε lam Hs σ hlam hds (Q w) (hQ w)) b⁻¹ hbinv
  obtain ⟨P₀, ⟨⟨hunit, hcay⟩, -⟩, -⟩ := id hds
  have hdet : IsUnit P₀.det := (Matrix.isUnit_iff_isUnit_det _).mp hunit
  have hH : Formalism.QuantumDeterminants.Hpk k r = P₀ᴴ * Formalism.REAL.Jm ε * P₀ := hcay.symm
  calc PI.CapelliEig.capC (k := k) (r := r) Y f g
      = PI.CapelliEig.capC (k := k) (r := r) Y
          (fun x => (P.comp (σ a⁻¹)).comp ((σ x).comp ((σ b⁻¹).comp Q))) g :=
        hL (2 * r + k + 1) ε (Wq →L[ℂ] Wp) (Formalism.QuantumDeterminants.Hpk k r) P₀ P₀⁻¹ f _
          (Y + (((2 * r + k : ℕ) : ℂ)) / 2) g (Matrix.nonsing_inv_mul _ hdet)
          (Matrix.mul_nonsing_inv _ hdet) hH hrep hg
    _ = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y •
          (P.comp (σ a⁻¹)).comp ((σ g).comp ((σ b⁻¹).comp Q)) :=
        hC k r ε lam Hs σ Wp Wq hlam hds (P.comp (σ a⁻¹)) ((σ b⁻¹).comp Q) hQ' Y g hg
    _ = Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y • f g := by rw [hrep g hg]

theorem capEig (hK : PI.KFinSmooth) (hD : PI.DSInfCharCap.DSInfCharCap) : PI.CapelliEig.CapEig := by
  have hCoef : CoefSm := coefSm_of GlobalTheory.T.capelli_transport_unitary_conj GlobalTheory.T.capelli_operator_on_unitary_coefficient_eq_derived hD
  exact capEig_of_coefSm GlobalTheory.T.capelli_operator_unitaryGroup_local hCoef hK

end GlobalTheory.CapelliEigenvalue
