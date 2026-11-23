import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup

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

def InFF (W : LocWach PD LL O v n) (A : ArcP n) (c : ZMod n) (f : W.EE) : Prop :=
  InFr W c 1 (nnDen W A c) f ∧
  ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.down bs →
    ∃ (κ : ℕ) (x : O), InFr W c (ps W s ^ (bs + A.S)) (nnDen W A c)
      (lE W κ * f - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE x)

def InLpp (W : LocWach PD LL O v n) (A : ArcP n) (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ}
    (b : Fin d → W.DD T) (k₀ : Fin d) : Prop :=
  ∀ s < A.len c, ∀ bs, A.ty (c - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
    dv W T (A.len c) b (Pi.single k₀ 1) ∈ FilS W T c s bs

def LiftsAt (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d) (f : W.EE)
    (e : ℕ) : Prop :=
  ∃ (w₁ : W.DD T₁) (z : W.DD T₂), InI W T₁ c w₁ ∧ (∃ Λ' ∈ Ps W, InFNc W T₁ c 1 (Λ' • w₁)) ∧
    InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • W.map F w₁) ∧
    InFNc W T₂ c W.π₀ z ∧
    RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
      (W.map F w₁ - z) (fun k => if k = k₀ then lE W e * f else 0)

def ArcSecMapCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ c ∈ A.cuts, ∀ e : ℕ, A.j ≤ e → e ≤ A.len c →
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L), Win W A T₁ → Win W A T₂ →
  ∀ (d₁ : ℕ) (b₁ : Fin d₁ → W.DD T₁) (sol₁ : Fin d₁ → ℕ → Fin d₁ → LL), IsHor W T₁ (c - ((A.len c : ℕ) : ZMod n)) b₁ sol₁ →
  ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL), IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol →
    (∀ x, InFP W T₁ (c - ((A.len c : ℕ) : ZMod n)) e 1 x → InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) e 1 (W.map F x)) ∧
    ∃ μ : Fin d₁ → Fin d → O,
      (∀ m, Formalism.MainNotions.TruncatedSeriesCountingBounds.crisMap B F.f (dv W T₁ e b₁ (Pi.single m 1)) = dvO W T₂ e b (μ m)) ∧
      ∀ (x : W.DD T₁) (g : Fin d₁ → W.EE), InFP W T₁ (c - ((A.len c : ℕ) : ZMod n)) e 1 ((abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) • x) →
        (∀ m, InFr W (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) 1 (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) (g m)) →
        RepVV W T₁ (c - ((A.len c : ℕ) : ZMod n)) e (A.M PD.p) (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b₁ sol₁ x g →
        RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) e (A.M PD.p) (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b sol (W.map F x)
          (fun k => ∑ m, g m * algebraMap O W.EE (μ m k))

def ArcGamLiftCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ c ∈ A.cuts, ∀ e : ℕ, A.j ≤ e → e ≤ A.len c →
  ∀ T : LocLat G Qp LL O, Win W A T →
  ∀ (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL), IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol →
  ∀ g : Fin d → W.EE, (∀ k, InFr W (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) 1 (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) (g k)) →
    (∃ h : Fin d → W.EE, (∀ k, W.γE W.gam (g k) - g k = algebraMap (LetA O n) W.EE W.π₀ * h k) ∧
      (∀ k, InFr W (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) 1 (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) (h k)) ∧
      ∀ s < e, ∃ κ : ℕ, SecIn W (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e
        (fun α c₀ => dvO W T e b c₀ ∈ FilS W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) s (-(α s))) (fun k => lE W κ * h k)) →
    ∃ v, InI W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) v ∧ InFP W T (c - ((A.len c : ℕ) : ZMod n)) e 1 ((abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) • v) ∧
      RepVV W T (c - ((A.len c : ℕ) : ZMod n)) e (A.M PD.p) (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b sol v (fun k => lE W (A.σ PD.p) * g k)

def ArcFilLowCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ c ∈ A.cuts, ∀ e : ℕ, A.j ≤ e → e ≤ A.len c →
  ∀ T : LocLat G Qp LL O, Win W A T →
  ∀ (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL), IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol →
  ∀ c₀ : Fin d → O, ∀ s < e,
    (∀ u : ℤ, (∀ a ∈ (A.ty ((c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) - (s : ZMod n))).win A.G₀ A.S A.η, u ≤ a) →
      dvO W T e b c₀ ∈ FilS W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) s u) ∧
    (∀ bs : ℕ, A.ty ((c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) - (s : ZMod n)) = Formalism.MainNotions.LocalTheoryWindows.LT.up bs →
      dvO W T e b c₀ ∈ FilS W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) s ((A.η : ℤ) + 1) → dvO W T e b c₀ ∈ FilS W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) s bs)

def HorFrameCore (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ T : LocLat G Qp LL O, Win W A T → ∀ c : ZMod n,
    ∃ (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL), IsHor W T c b sol

variable (W : LocWach PD LL O v n) (A : ArcP n) {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (c : ZMod n) {d : ℕ} (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL) (k₀ : Fin d)

end Formalism.MainNotions.N.FrobeniusPowerSeries
