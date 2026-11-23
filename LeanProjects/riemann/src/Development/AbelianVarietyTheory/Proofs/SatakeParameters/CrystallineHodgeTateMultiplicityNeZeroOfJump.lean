import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodCoefficientRingIntegersPadicFiniteExtensionStatement

open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_succ_le (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := PD.Fil_anti a
  have hc : (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil a).restrictScalars Qp).subtype).comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle)) =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        ((PD.Fil (a + 1)).restrictScalars Qp).subtype := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    rfl
  exact ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y,
    LinearMap.congr_fun hc y⟩

theorem fildR_succ_le (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_DdR (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a ≤ DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero_of_jump (ρ : Representation LL G V) [Module.Finite LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) : multV PD ρ τ a ≠ 0 := by
  intro h0
  apply h
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_DdR PD ρ τ a)
  refine Submodule.eq_of_le_of_finrank_eq (fildR_succ_le PD ρ τ a) ?_
  unfold multV at h0
  omega

end General

theorem jump_multV_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL),
    Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  intro l _ P K LL T hF τ u hJ
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T.V, ρ := T.ρ, cont := T.cont }
  obtain ⟨-, ⟨hfin, -⟩, -⟩ := hF ↥LL.1 ↥(OL LL) (GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL) A
  haveI : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) := hfin
  exact multV_ne_zero_of_jump (P.PD K) T.ρ τ u hJ

end GlobalTheory.HTW.Rec
