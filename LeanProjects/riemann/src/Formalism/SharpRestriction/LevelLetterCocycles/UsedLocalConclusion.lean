import Formalism.SharpRestriction.LevelLetterCocycles.GammaSemisimpleLocalOfConsequences

noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

def DeltaInvariantNormBound (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  WachLatticeFreeGlobal D HW F ∧ P2 D HW F ∧ P3 D HW F C ∧ P4 D HW F C ∧ P5 D HW F ∧ P6 D HW F ∧ P7 D HW F ∧
    P8 D HW F ∧ P9 D HW F ∧ WachCharacterisation D HW F ∧ gammaSemisimpleQuotientGlobal D HW F ∧ Pr2a D HW F ∧ Pr2b D HW F ∧ Pr2c D HW F ∧
    Pr2d D HW F ∧ lem3 D HW F ∧ ConclusionE D HW F

def DeltaInvariantLatticeCriterion {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) : Prop :=
  WachLatticeFree W ∧ P2W W ∧ P3W W ∧ P4W W Pt ∧ P5W W ∧ WachSaturationExactness W ∧ WachCrystallineExtension W ∧ WachMaxJumpBound W ∧ P9W W ∧ WachCharacterisationLattice W

def deltaInvariantLatticeLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (F : FonOf LT AI HW) (_C : CmpOf LT AI HW F) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    DeltaInvariantLatticeCriterion ((HW l).W K s LL h) (ptK LT HW h)

def deltaInvariantLatticeGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  deltaInvariantLatticeLocal D.loc HW D.locA F C

theorem thm1used_of {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    {C : CmpOf D.loc D.locA HW F} (h : thm1 D HW F C) : deltaInvariantLatticeGlobal D HW F C :=
  fun l _ K s LL g => ⟨(h l K s LL g).1.1, (h l K s LL g).2.1, (h l K s LL g).2.2.1,
    (h l K s LL g).2.2.2.1, (h l K s LL g).2.2.2.2.1, (h l K s LL g).2.2.2.2.2.1,
    (h l K s LL g).2.2.2.2.2.2.1, (h l K s LL g).2.2.2.2.2.2.2.1, (h l K s LL g).2.2.2.2.2.2.2.2.1,
    (h l K s LL g).2.2.2.2.2.2.2.2.2.1⟩

def UsedLocalConclusion (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (C : CmpOf D.loc D.locA HW F) :
    Prop :=
  deltaInvariantLatticeGlobal D HW F C ∧ gammaSemisimpleQuotientGlobal D HW F ∧ prop2 D HW F ∧ lem3 D HW F

section Guard

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

def ClKNatG (W : LocWach PD LL O v n) : Prop := (PD.p = 2 → ∃ i : K, i ^ 2 = -1) → W.ClKNat

end Guard

def ClKNatGL (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    ClKNatG ((HW l).W K s LL h)

end Formalism.MainNotions.DeltaInvariantLattices
