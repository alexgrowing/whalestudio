import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsBis

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

variable (W : LocWach PD LL O v n)

theorem gamma_pi0_eq_pi0_mul_one_add_unit_mul_q (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    ∃ κ ∈ W.AΔ, IsUnit κ ∧ W.γA W.gam W.π₀ = W.π₀ * (1 + κ * qA W) := by
  obtain ⟨w, hw, h⟩ := GS.gamma_pi0_eq_pi0_mul_unit (GS.ringData_of_caseA_of_p9 W hcase hP9)
  exact ⟨w, hw, w.isUnit, h⟩

theorem gamma_sub_self_mem_pi0_q (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (f : LetA O n) (hf : f ∈ W.AΔ) :
    ∃ g ∈ W.AΔ, W.γA W.gam f - f = W.π₀ * qA W * g :=
  GS.gam_A_core (GS.ringData_of_caseA_of_p9 W hcase hP9) hf

theorem gamma_level_eq_mul (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (s : ℕ) (hs : 1 ≤ s) :
    ∃ g ∈ W.AΔ, W.γA W.gam (ps W s) = ps W s * (1 + W.π₀ * qA W * g) :=
  GS.gam_ps_core (GS.ringData_of_caseA_of_p9 W hcase hP9) s hs

theorem gamma_fraction_in_ideal (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (a : ZMod n) (e : ℕ) (α : ℕ → ℤ)
    (f : W.EE) (hf : InId W a e α f) :
    InId W a e α (W.γE W.gam f) ∧
      InFr W a (W.π₀ * ∏ s ∈ Finset.range e, ps W s ^ (α s).toNat)
        (∏ s ∈ Finset.range e, ps W s ^ (-(α s)).toNat) (W.γE W.gam f - f) :=
  GS.gam_frac_core (GS.ringData_of_caseA_of_p9 W hcase hP9) a e α f hf

theorem saturation_fraction_module (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hSat : SATcore W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ)
    (f₁ f₂ f' : LetA O n) (h₁ : f₁ ∈ PiPs W) (h₂ : f₂ ∈ PiPs W) (h' : f' ∈ PiPs W) (x : W.DD T)
    (hx : f' • x ∈ W.NΔ T) (hk : ∃ k : ℕ, InFN W T f₁ (lA W ^ k • (f₂ • x))) :
    InFN W T f₁ (f₂ • x) := by
  have hx' : f' • (f₂ • x) ∈ W.NΔ T := by
    rw [smul_smul, mul_comm, ← smul_smul]
    exact GS.smul_mem_NΔ W T (GS.piPs_mem W h₂) hx
  exact hSat hcase T f₁ f' hT h₁ h' (f₂ • x) hx' hk

theorem saturation_fraction_ring [IsDomain O] [IsDiscreteValuationRing O] (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hinj : Function.Injective (algebraMap O LL)) (f₁ f₂ f' : LetA O n) (h₁ : f₁ ∈ PiPs W) (h₂ : f₂ ∈ PiPs W)
    (h' : f' ∈ PiPs W) (x : LetA O n) (hx : f' * x ∈ W.AΔ)
    (hk : ∃ (k : ℕ) (y : LetA O n), y ∈ W.AΔ ∧ lA W ^ k * (f₂ * x) = f₁ * y) :
    ∃ y ∈ W.AΔ, f₂ * x = f₁ * y := by
  obtain ⟨k, y, hy, hky⟩ := hk
  exact GS.sat_A_core (GS.ringData_of_caseA_of_p9 W hcase hP9) (GS.p_ne_zero W) h₁ hy k hky

end Formalism.MainNotions.N.FrobeniusPowerSeries
