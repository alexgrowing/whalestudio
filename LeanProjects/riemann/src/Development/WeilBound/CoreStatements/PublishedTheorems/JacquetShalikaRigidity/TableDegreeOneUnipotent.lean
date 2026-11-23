import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsGenericOfIsLocComp

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace tableDegreeOneUnipotent

theorem mul_le_sq_add (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ _ := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ _ := le_self_add

theorem integ {X : Type} [MeasurableSpace X] {ν : Measure X} {f φ : X → ℂ}
    (hf : AEStronglyMeasurable f ν) (hφ : AEStronglyMeasurable φ ν)
    (h1 : ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν < ∞) (h2 : ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun g => f g * conj (φ g)) ν := by
  refine ⟨hf.mul (Complex.continuous_conj.comp_aestronglyMeasurable hφ), ?_⟩
  show ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν < ∞
  calc ∫⁻ g, ‖f g * conj (φ g)‖ₑ ∂ν ≤ ∫⁻ g, (‖f g‖ₑ ^ 2 + ‖φ g‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun g => ?_
        have hc : ‖conj (φ g)‖ₑ = ‖φ g‖ₑ := by simp [enorm_eq_nnnorm]
        rw [enorm_mul, hc]
        exact mul_le_sq_add _ _
    _ = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν + ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂ν := lintegral_add_left' (hf.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨h1, h2⟩

theorem pre_of_good {E : Type} [Field E] [NumberField E] {k : ℕ} {ψ : AddChar (Ad E) ℂ} {m : ℕ}
    {f : GA E k → ℂ} (h : Good ψ m f) : Pre ψ m f :=
  ⟨h.cont, h.left, h.law⟩

theorem main (hU1 : U1) (hP1 : P1) (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (k : ℕ)
    (μ : Measure (GA E k)) [μ.IsHaarMeasure] (ψ : AddChar (Ad E) ℂ) (hψ : StdPsi ψ) :
    ∀ m, m < k → ∀ β, IsWt (nuP E k m) β → ∃ β', IsWt (nuP E k 0) β' ∧
      ∀ f φ, Pre ψ m f → Good ψ m φ → ∫⁻ g, ‖f g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        ∫⁻ g, ‖φ g‖ₑ ^ 2 ∂μ.withDensity β < ∞ →
        Integrable (fun g => whit ψ m f g * conj (whit ψ m φ g)) (μ.withDensity β') ∧
        ∫ g, f g * conj (φ g) ∂μ.withDensity β = ∫ g, whit ψ m f g * conj (whit ψ m φ g) ∂μ.withDensity β' := by
  intro m
  induction m with
  | zero =>
    intro _ β hβ
    refine ⟨β, hβ, fun f φ hf hφ h1 h2 => ⟨?_, rfl⟩⟩
    exact integ hf.cont.aestronglyMeasurable (pre_of_good hφ).cont.aestronglyMeasurable h1 h2
  | succ m ih =>
    intro hm β hβ
    obtain ⟨β1, hβ1, hL2, hip⟩ := hU1 E k μ ψ hψ (m + 1) (by omega) hm β hβ
    obtain ⟨β', hβ', h⟩ := ih (by omega) β1 hβ1
    refine ⟨β', hβ', fun f φ hf hφ h1 h2 => ?_⟩
    have hf' : Pre ψ m (colT ψ (m + 1) f) := (hP1 E k ψ hψ (m + 1) (by omega) hm f hf).1
    have hφ' : Good ψ m (colT ψ (m + 1) φ) := GlobalTheory.CuspRep.Generic.good_colT hψ hm hφ
    obtain ⟨hi, he⟩ := h _ _ hf' hφ' ((hL2 f hf).trans_lt h1) ((hL2 φ (pre_of_good hφ)).trans_lt h2)
    exact ⟨hi, (hip f φ hf hφ h1 h2).trans he⟩

end tableDegreeOneUnipotent

theorem unitaryGroupGeometricSide_of_quotient_identities : U1 → P1 → U2 := by
  intro hU1 hP1 E _ _ _ k μ _ ψ hψ
  exact tableDegreeOneUnipotent.main hU1 hP1 E k μ ψ hψ

end PositivityTheory.AdelicQuotientData

end
