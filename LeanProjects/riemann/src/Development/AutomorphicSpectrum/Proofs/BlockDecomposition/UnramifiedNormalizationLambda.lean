import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.REALTH
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GluePlaces
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th ComplexConjugate
open GroundTheory.Automorphic.GodementSection (localChar)
open scoped NumberField.AdeleRing ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.LamUnr

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem continuous_of_isUnramifiedChar {μ : Fˣ →* ℂˣ} (hu : IsUnramifiedChar μ) : Continuous μ := by
  refine continuous_of_continuousAt_one μ ?_
  have hop : (unitFiltrationUnits F 0 : Set Fˣ) ∈ nhds (1 : Fˣ) :=
    (isOpen_unitFiltrationUnits 0).mem_nhds (Subgroup.one_mem _)
  refine ContinuousAt.congr (f := fun _ => (1 : ℂˣ)) continuousAt_const ?_
  filter_upwards [hop] with x hx
  rw [show μ x = 1 from hu hx]

theorem unit_mem_of_ord_eq_zero {u : Fˣ} (h : ord (u : F) = 0) : (u : F) ∈ 𝒪[F] := by
  rw [← mem_valBall_zero_iff, mem_valBall_iff_le_ord u.ne_zero, h]

theorem inv_mem_of_ord_eq_zero {u : Fˣ} (h : ord (u : F) = 0) : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
  have h1 : ord (((u⁻¹ : Fˣ)) : F) = 0 := by
    have := ord_mul (K := F) u.ne_zero (u⁻¹).ne_zero
    simp only [Units.mul_inv, ord_one, h, zero_add] at this
    exact this.symm
  exact unit_mem_of_ord_eq_zero h1

end

theorem lamU : Ad3.K.QuadraticBaseChangeGL3.Th.NORMU → Ad3.K.QuadraticBaseChangeGL3.Th.LAMU := by
  intro hN F _ _ _ _ _ _ _ χ hχ hχ1 E _ _ _ _ _ _ _ hd hc σ hσ η hη h0 hres
  have hnorm := hN F χ hχ hχ1 E hd hc σ hσ η hη hres
  have hsq : ∀ a, η a * η a = 1 := by
    intro a
    apply Units.ext
    rw [Units.val_mul, hη a, Units.val_one]
    unfold GL2LocalData.nsg
    split_ifs <;> simp
  have hun : IsUnramifiedChar η := by
    rw [isUnramifiedChar_iff]
    intro u hu
    apply Units.ext
    rw [hη u, Units.val_one]
    unfold GL2LocalData.nsg
    exact if_pos (hnorm u (unit_mem_of_ord_eq_zero hu) (inv_mem_of_ord_eq_zero hu))
  have hnm : ‖((η (unifUnit F) : ℂˣ) : ℂ)‖ = 1 := by
    rw [hη]
    unfold GL2LocalData.nsg
    split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · rw [GlobalTheory.CompanionTheory.GlueSign.lamE_eq (continuous_of_isUnramifiedChar hun) hnm hsq,
      localEpsilon_of_isUnramified hun, h0]
    simp
  · unfold GL2LocalData.nsg
    refine if_pos (hnorm (-1) (by simp) ?_)
    simp

end GlobalTheory.CompanionTheory.LamUnr
