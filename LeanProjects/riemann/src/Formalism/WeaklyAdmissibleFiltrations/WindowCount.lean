import Formalism.WeaklyAdmissibleFiltrations.Statement

noncomputable section

namespace Formalism.WeaklyAdmissibleFiltrations

open Module

def WindowCount : Prop :=
  ∀ (G : Type) [Group G] (Qp K₀ K : Type) [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    (B BdR : Type) [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B]
    [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR]
    [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR) (LL : Type) [Field LL] [Algebra Qp LL]
    (V : Type) [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (lo hi : ℤ), lo ≤ hi →
    ∑ a ∈ Finset.Ico lo hi, multV PD ρ τ a =
      (finrank LL ↥(FildR PD ρ τ lo) : ℤ) - finrank LL ↥(FildR PD ρ τ hi)

end Formalism.WeaklyAdmissibleFiltrations
