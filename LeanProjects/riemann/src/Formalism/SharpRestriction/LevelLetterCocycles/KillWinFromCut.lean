import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction

namespace Formalism.MainNotions.UnusedSlot80.CutU

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.WachCoordinates.Br

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

def RATCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (A : ArcP n) (a : ZMod n) (e : ℕ) (E₀ : ℕ) (E : ℕ → ℤ), E₀ ≤ 1 →
    (∀ s < e, -(A.Hs a e s : ℤ) ≤ E s ∧ E s ≤ A.Hs a e s) →
    ∀ f : W.EE, InFr W a 1 (abelian₂ W A a e) f →
      (∀ s < e, ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a (ps W s ^ (E s).toNat)
          (ps W s ^ (-(E s)).toNat * ∏ t ∈ (Finset.range e).erase s, ps W t ^ A.Hs a e t) f₁ ∧
        InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) →
      (E₀ = 1 → ∃ κ : ℕ, ∃ f₁ f₂ : W.EE, lE W κ * f = f₁ + f₂ ∧
        InFr W a W.π₀ (abelian₂ W A a e) f₁ ∧ InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂) →
      ∃ f₁ f₂ : W.EE, f = f₁ + f₂ ∧
        InFr W a (W.π₀ ^ E₀ * ∏ s ∈ Finset.range e, ps W s ^ (E s).toNat)
          (∏ s ∈ Finset.range e, ps W s ^ (-(E s)).toNat) f₁ ∧
        InFr W a (W.π₀ * abelian₂ W A a e) 1 f₂

def InvLevCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ (a : ZMod n) (s : ℕ) (T : Finset ℕ) (e : ℕ → ℕ), s ∉ T →
    ∀ f : W.EE, InFr W a 1 (∏ t ∈ T, ps W t ^ e t) f →
    (∃ κ : ℕ, InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t) (lE W κ * (W.γE W.gam f - f))) →
    ∃ (κ : ℕ) (x : O), InFr W a (ps W s) (∏ t ∈ T, ps W t ^ e t)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE a) * algebraMap O W.EE x)

def KillWinFromCut [IsDomain O] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W → KillerLevCore W → Formalism.MainNotions.UnusedSlot80.KL.PsStable W → W.π₀ ∈ W.AΔ → RATCore W → InvLevCore W →
    Formalism.MainNotions.UnusedSlot80.UnivF.KillWinCore W

end Core

end Formalism.MainNotions.UnusedSlot80.CutU
