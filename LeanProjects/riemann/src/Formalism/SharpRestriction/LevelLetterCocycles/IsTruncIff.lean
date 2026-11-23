import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineLiftingInputs

noncomputable section

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN eY IsRem fMX pullJ IsSer IsTrunc TCase)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def IsSerZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (ζ : W.DD T)
    (c : ℕ → W.DD T) : Prop :=
  c 0 = 0 ∧ (∀ y, DL W T i (c y) ∧ c y ∈ W.N T) ∧
    ∀ K : ℕ, ∃ j : ℕ, InPN W T K (((PD.p : ℕ) : O) ^ j •
      (((PD.p : ℕ) : O) ^ eY PD.p K • ζ -
        ∑ y ∈ Finset.range K, ((PD.p : ℕ) : O) ^ (eY PD.p K - eY PD.p y) •
          (W.γ T (W.π₀ ^ y • c y) - W.π₀ ^ y • c y)))

def IsTrZ (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (ζ t : W.DD T) : Prop :=
  ∃ (c : ℕ → W.DD T) (r s : ℕ → LetA O n), IsSerZ W T i ζ c ∧
    (∀ y, IsRem W j M X y (r y) ∧
      ((PD.p : ℕ) : LetA O n) ^ eY PD.p y * s y = ((PD.p : ℕ) : LetA O n) ^ σ * r y) ∧
    t = ∑ y ∈ Finset.range (max M X + 1), s y • ((W.φD T) ^ j) (c y)

theorem isTrunc_iff (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (i : ZMod n) (j M X σ : ℕ)
    (w z : W.DD T) :
    IsTrunc W T i j M X σ w z ↔ ∃ t, IsTrZ W T i j M X σ (W.γ T w - w) t ∧
      z = ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w - t := by
  constructor
  · rintro ⟨c, r, s, hc, hr, rfl⟩
    exact ⟨_, ⟨c, r, s, hc, hr, rfl⟩, rfl⟩
  · rintro ⟨t, ⟨c, r, s, hc, hr, rfl⟩, rfl⟩
    exact ⟨c, r, s, hc, hr, rfl⟩

def TTool2Z [NeZero n] (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 11 ≤ PD.p → ∀ (j M X σ : ℕ), TCase PD.p j M X σ →
  ∀ (T : LocLat G Qp LL O), IsCrys PD T.ρ → ∀ (i : ZMod n),
    (∀ ζ, DL W T i ζ → InPN W T 1 ζ → ∃ t, IsTrZ W T i j M X σ ζ t) ∧
    (∀ ζ t, DL W T i ζ → InPN W T 1 ζ → IsTrZ W T i j M X σ ζ t →
      DL W T (i + (j : ZMod n)) t ∧ t ∈ pullJ W T i j ∧
      ∃ p ∈ pullJ W T i j,
        ((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) ζ - (W.γ T t - t) = fMX W M X • p) ∧
    (∀ (a a' : O) (ζ ζ' t t' t'' : W.DD T), DL W T i ζ → InPN W T 1 ζ → DL W T i ζ' →
      InPN W T 1 ζ' → IsTrZ W T i j M X σ ζ t → IsTrZ W T i j M X σ ζ' t' →
      IsTrZ W T i j M X σ (a • ζ + a' • ζ') t'' →
      ∃ p ∈ pullJ W T i j, t'' - (a • t + a' • t') = fMX W M X • p) ∧
    (∀ ζ t, DL W T i ζ → InPN W T M ζ → j = 1 → X ≤ (PD.p - 1) * M →
      IsTrZ W T i j M X σ ζ t → ∃ p ∈ pullJ W T i j, t = fMX W M X • p)

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
