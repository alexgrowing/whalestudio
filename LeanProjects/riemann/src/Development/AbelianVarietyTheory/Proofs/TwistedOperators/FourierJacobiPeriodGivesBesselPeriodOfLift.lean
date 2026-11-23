import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapIntertwinesCoreHeisenbergOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameFunctionalVacuumIrreducibilityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PeriodAllDataProductsEqFourierJacobiPeriodStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPeriodAllDataIsTameThetaFunctionalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VanishingDescendsBesselToFourierJacobiStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.UpBessel

theorem upBF : ∀ D : D7, UpBF D := by
  intro D ψ ρ B J s 𝒮 Γ₀ K hL L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G hφ hG hK Ξ₁ Ξ₂ hΞ₁ hΞ₂ hbox hJ
  by_contra hnone
  push_neg at hnone

  have hstd : IsStdChar D ψ (-1) := s.weil.std
  have hℓ : Tame ψ B.V₀ J.W₀ (J.perAll ψ B s.om₀ φ G) :=
    GlobalTheory.T.fourierJacobiPeriod_all_data_isTameThetaFunctional D ψ ρ ρ B J s.χV s.χW s.om₀ s.weil₀ φ G hφ hG

  have hkill : ∀ Φ ∈ 𝒮, J.perAll ψ B s.om₀ φ G (flBF s Φ) = 0 :=
    GlobalTheory.T.vanishing_descends_bessel_to_fourierJacobi D ψ ρ B J s 𝒮 Γ₀ K hL φ G hφ hG hK hnone
  obtain ⟨Φ₁, hΦ₁, hΦ₁ne⟩ := hL.ne

  have hall : ∀ f, VacG ψ B.V₀ J.W₀ Γ₀ f → J.perAll ψ B s.om₀ φ G f = 0 := by
    refine GlobalTheory.T.tame_functional_vacuum_irreducibility D ψ hstd B.V₀ J.W₀ Γ₀ _ hℓ (flBF s Φ₁) (hL.vac Φ₁ hΦ₁) hΦ₁ne ?_
    intro w hw
    have hcomm := (GlobalTheory.FlatHeis.flatAt_heisO D ψ hstd B.V B.V₀ J.W J.W₀ ρ ρ B.d J.d s.vS s.vT s.vU
      (xZero J.d) (yZero B.V₀ ρ (vecB B.o B.ζ)) Φ₁ (hL.theta Φ₁ hΦ₁)).2.1 w
    have hflat : flBF s (heisO ψ B.V J.W (B.d.ext0 J.W (J.d.inc0 B.V₀ w)) Φ₁) =
        heisO ψ B.V₀ J.W₀ w (flBF s Φ₁) := hcomm
    rw [← hflat]
    exact hkill _ (hL.core Φ₁ hΦ₁ w hw)

  have h0 := hall _ hbox
  rw [GlobalTheory.T.periodAllData_products_eq_fourierJacobiPeriod D ψ ρ B J s L' ζ' hζ' l χA χz χ' oma omz hχ hWa hWz φ G Ξ₁ Ξ₂ hΞ₁ hΞ₂] at h0
  exact hJ h0

end GlobalTheory.UpBessel
