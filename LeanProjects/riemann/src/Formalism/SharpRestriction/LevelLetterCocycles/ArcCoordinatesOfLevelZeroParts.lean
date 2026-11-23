import Formalism.SharpRestriction.LevelLetterCocycles.MembershipCriterionOfLevelZero
import Formalism.SharpRestriction.LevelLetterCocycles.SplittingOfExactnessAndData

noncomputable section

open Classical

namespace Formalism.MainNotions.UnusedSlot80.LevC

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} {W : LocWach PD LL O v n}

def LevelZeroModP (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ (x : W.DD T) (k : ℕ) (f : Fin d → W.EE),
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x) →
    RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol (lA W ^ k • x) f →
    (∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * LamUp W A c' e)
      (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) (f m)) →
    InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x →
    ∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
      (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m

def LevelZeroModPRefined (A : ArcP n) (c' : ZMod n) (e : ℕ) (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T)
    (sol : Fin d → ℕ → Fin d → LL) : Prop :=
  ∀ (x : W.DD T) (k : ℕ) (f : Fin d → W.EE),
    InFP W T c' (e + 1) 1 (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) • x) →
    RepVV W T c' (e + 1) (A.M PD.p) (abelian₂ W A (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)) b sol (lA W ^ k • x) f →
    (∀ m, InFr W (c' + ((e + 1 : ℕ) : ZMod n)) (W.π₀ * LamUp W A c' e)
      (ps W 0 ^ A.Hs (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) 0) (f m)) →
    (∃ κ : ℕ, SecIn W (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1)
      (condNN W T (c' + ((e + 1 : ℕ) : ZMod n)) (e + 1) b) fun m => lE W κ * f m) →
    InFNc W T (c' + ((e + 1 : ℕ) : ZMod n)) 1 x

theorem secCrit0_of_pieces [IsDomain O] [NeZero n] (A : ArcP n) (c' : ZMod n) (e : ℕ)
    (T : LocLat G Qp LL O) {d : ℕ} (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (h1 : LevelZeroModP A c' e T b sol) (h2 : LevelZeroModPRefined A c' e T b sol) : SecCrit0 A c' e T b sol :=
  fun x k f hx hr hf => ⟨h1 x k f hx hr hf, h2 x k f hx hr hf⟩

def DivLev (a : ZMod n) (ζ : LL) : Prop :=
  ∀ g ∈ W.AΔ, ∀ k : ℕ, (∀ j < k, PowerSeries.coeff j (W.lev a ζ g) = 0) →
    ∃ h ∈ W.AΔ, letE a * g = ps W 0 ^ k * h

def condPolar (T : LocLat G Qp LL O) (c : ZMod n) (e : ℕ) {d : ℕ} (b : Fin d → W.DD T) (α : ℕ → ℤ)
    (c₀ : Fin d → O) : Prop :=
  ∀ s < e, 0 ≤ α s ∨ dvO W T e b c₀ ∈ FilS W T c s (-(α s))

end Formalism.MainNotions.UnusedSlot80.LevC

namespace Formalism.MainNotions.UnusedSlot80

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br

def LevelZeroModPLocal (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
    ∀ (A : Formalism.MainNotions.ArcLiftingSetup.ArcP (Module.finrank ℚ_[l] ↥(K0 K))), A.OK → ∀ c' ∈ A.cuts,
      ∀ T, Formalism.MainNotions.ArcLiftingSetup.Win ((HW l).W K 1 LL hG) A T → ∀ (d : ℕ) (b : Fin d → ((HW l).W K 1 LL hG).DD T)
        (sol : Fin d → ℕ → Fin d → ↥LL.1), Formalism.MainNotions.ArcLiftingSetup.IsHor ((HW l).W K 1 LL hG) T c' b sol →
          ∀ e : ℕ, LevC.LevelZeroModP (W := (HW l).W K 1 LL hG) A c' e T b sol

def LevelZeroModPRefinedLocal (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hG : Good K 1 LL), CaseA K LL → 5 ≤ l →
    ∀ (A : Formalism.MainNotions.ArcLiftingSetup.ArcP (Module.finrank ℚ_[l] ↥(K0 K))), A.OK → ∀ c' ∈ A.cuts,
      ∀ T, Formalism.MainNotions.ArcLiftingSetup.Win ((HW l).W K 1 LL hG) A T → ∀ (d : ℕ) (b : Fin d → ((HW l).W K 1 LL hG).DD T)
        (sol : Fin d → ℕ → Fin d → ↥LL.1), Formalism.MainNotions.ArcLiftingSetup.IsHor ((HW l).W K 1 LL hG) T c' b sol →
          ∀ e : ℕ, LevC.LevelZeroModPRefined (W := (HW l).W K 1 LL hG) A c' e T b sol

theorem secCrit0L_of_pieces (D : D7) (HW : HWOf D.loc) (h1 : LevelZeroModPLocal D HW) (h2 : LevelZeroModPRefinedLocal D HW) :
    SecCrit0L D HW := by
  intro l _ K LL hG hCA h5l A hA c' hc' T hT d b sol hb e
  have := neZero_finrank_max_unramified K
  exact LevC.secCrit0_of_pieces A c' e T b sol (h1 l K LL hG hCA h5l A hA c' hc' T hT d b sol hb e)
    (h2 l K LL hG hCA h5l A hA c' hc' T hT d b sol hb e)

theorem arc_coordinates_of_level_zero_parts (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) (h1 : LevelZeroModPLocal D HW) (h2 : LevelZeroModPRefinedLocal D HW) : ArcCoordinatesTheorem D HW F Cm :=
  arc_coordinates_of_level_zero D HW F Cm (secCrit0L_of_pieces D HW h1 h2)

end Formalism.MainNotions.UnusedSlot80

namespace Formalism.MainNotions.UnusedSlot80.Split

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.WachCoordinates.Br Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

def SplitPolar : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK →
  ∀ (T₂ Y : LocLat G Qp LL O) (ι : LatHom T₂.L Y.L) (π : LatHom Y.L W.one.L),
    Win W A T₂ → IsCrys PD Y.ρ → IsSESLat (Qp := Qp) ι π → ∀ c ∈ A.cuts, ∀ w : W.DD T₂,
    InI W T₂ c w →
    InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) 1 (abelian₂ W A c (A.len c) • w) →
    (∃ p ∈ Pp W Y (c - ((A.len c : ℕ) : ZMod n)) (A.len c), ∃ x ∈ W.Nl Y c, W.map ι w = p - x) →
    ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol →
      ∃ (κ : ℕ) (f : Fin d → W.EE),
        RepVV W T₂ (c - ((A.len c : ℕ) : ZMod n)) (A.len c) (A.M PD.p) (abelian₂ W A c (A.len c)) b sol
          (lA W ^ κ • w) f ∧
        SecIn W c (A.len c) (Formalism.MainNotions.UnusedSlot80.LevC.condPolar (W := W) T₂ c (A.len c) b) f

def PolarToPole : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → 5 ≤ PD.p → ∀ A : ArcP n, A.OK → ∀ T₂ : LocLat G Qp LL O, Win W A T₂ →
    ∀ c ∈ A.cuts, ∀ (d : ℕ) (b : Fin d → W.DD T₂) (sol : Fin d → ℕ → Fin d → LL),
      IsHor W T₂ (c - ((A.len c : ℕ) : ZMod n)) b sol → ∀ f : Fin d → W.EE,
        SecIn W c (A.len c) (Formalism.MainNotions.UnusedSlot80.LevC.condPolar (W := W) T₂ c (A.len c) b) f →
        SecIn W c (A.len c) (condPole W A T₂ c b) f

theorem splitShape_of_pieces (h1 : SplitPolar W) (h2 : PolarToPole W) : SplitShape W := by
  intro hCA h5 A hA T₂ Y ι π hT₂ hY hses c hc w hI hP hpx d b sol hb
  obtain ⟨κ, f, hrep, hS⟩ := h1 hCA h5 A hA T₂ Y ι π hT₂ hY hses c hc w hI hP hpx d b sol hb
  exact ⟨κ, f, hrep, h2 hCA h5 A hA T₂ hT₂ c hc d b sol hb f hS⟩

def SplitPolarL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => SplitPolar ((HW l).W K 1 LL hG)

def PolarToPoleL (D : D7) (HW : HWOf D.loc) : Prop :=
  AtCaseA fun l _ K LL hG => PolarToPole ((HW l).W K 1 LL hG)

theorem splitShapeL_of_pieces (D : D7) (HW : HWOf D.loc) (h1 : SplitPolarL D HW) (h2 : PolarToPoleL D HW) :
    SplitShapeL D HW := fun l _ K LL hG hA h5 =>
  splitShape_of_pieces _ (h1 l K LL hG hA h5) (h2 l K LL hG hA h5)

end Formalism.MainNotions.UnusedSlot80.Split
