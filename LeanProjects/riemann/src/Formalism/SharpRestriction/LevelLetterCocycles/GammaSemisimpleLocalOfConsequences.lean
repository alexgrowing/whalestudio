import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices

noncomputable section

namespace Formalism.MainNotions.DeltaInvariantLattices

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations

section Local

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

variable (W : LocWach PD LL O v n)

def WachLatticeFree : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → wachFree W T

def WachLatticeDualClosed : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (P : T.V →ₗ[LL] T'.V →ₗ[LL] LL), IsCrys PD T.ρ → IsCrys PD T'.ρ →
    wachDual W T T' P

def WachLatticeTensorClosed : Prop :=
  ∀ (T T' T'' : LocLat G Qp LL O) (b : T.V →ₗ[LL] T'.V →ₗ[LL] T''.V),
    IsCrys PD T.ρ → IsCrys PD T'.ρ → IsCrys PD T''.ρ → wachTensor W T T' T'' b

def WachLatticeMonoidal : Prop := WachLatticeDualClosed W ∧ WachLatticeTensorClosed W

def WachCharacterisationLattice : Prop := ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → p10 W T

def WachTwistLattice : Prop :=
  ∀ (T T' : LocLat G Qp LL O) (j : ℤ), IsCrys PD T.ρ → IsCrys PD T'.ρ → wachTwistIso W T T' j

def GammaSemisimpleQuotient : Prop :=
  ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
    ∀ y : ℕ, 1 ≤ y → SSEig W T (invN W T (W.Q ^ y)) (W.N T)
      {c | ∃ a ∈ Jumps (PD := PD) T, ∃ j : ℕ, 1 ≤ j ∧ j ≤ y ∧ c = (uU W) ^ (-(a + j))}

theorem gamma_semisimple_of_consequences (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (h : ConsW W Pt) : GammaSemisimpleQuotient W :=
  fun T hT => (h T hT).2.1

theorem wach_first_lattice_iff : WachFreeDualTensor W ↔ WachLatticeFree W ∧ WachLatticeMonoidal W := Iff.rfl

theorem wach_tenth_iff : WachTwistCharacterisation W ↔ WachCharacterisationLattice W ∧ WachTwistLattice W := Iff.rfl

theorem P1freeW_of (h : WachFreeDualTensor W) : WachLatticeFree W := h.1

theorem wach_characterisation_lattice_of (h : WachTwistCharacterisation W) : WachCharacterisationLattice W := h.1

end Local

section Theory

def wachLatticeFreeLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachLatticeFree ((HW l).W K s LL h)

def wachLatticeMonoidalLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachLatticeMonoidal ((HW l).W K s LL h)

def wachCharacterisationLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachCharacterisationLattice ((HW l).W K s LL h)

def wachTwistLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    WachTwistLattice ((HW l).W K s LL h)

def gammaSemisimpleLocal (LT : LocTheory) (HW : HWOf LT) (AI : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (LT l))
    (_F : FonOf LT AI HW) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
    GammaSemisimpleQuotient ((HW l).W K s LL h)

end Theory

section Design

def WachLatticeFreeGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachLatticeFreeLocal D.loc HW D.locA F

def WachLatticeMonoidalGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachLatticeMonoidalLocal D.loc HW D.locA F

def WachCharacterisation (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachCharacterisationLocal D.loc HW D.locA F

def WachTwistLocalTheory (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  wachTwistLocal D.loc HW D.locA F

def gammaSemisimpleQuotientGlobal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) : Prop :=
  gammaSemisimpleLocal D.loc HW D.locA F

theorem gamma_semisimple_local_of_consequences {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : cons D HW F) : gammaSemisimpleQuotientGlobal D HW F :=
  fun l _ K s LL g => gamma_semisimple_of_consequences _ _ (h l K s LL g)

theorem wach_first_iff_free_monoidal (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    P1 D HW F ↔ WachLatticeFreeGlobal D HW F ∧ WachLatticeMonoidalGlobal D HW F := by
  constructor
  · intro h
    exact ⟨fun l _ K s LL g => (h l K s LL g).1, fun l _ K s LL g => (h l K s LL g).2⟩
  · rintro ⟨a, b⟩ l _ K s LL g
    exact ⟨a l K s LL g, b l K s LL g⟩

theorem product_first_zeroth_parts_iff_wach_and_twist (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) :
    product_first_zeroth_parts D HW F ↔ WachCharacterisation D HW F ∧ WachTwistLocalTheory D HW F := by
  constructor
  · intro h
    exact ⟨fun l _ K s LL g => (h l K s LL g).1, fun l _ K s LL g => (h l K s LL g).2⟩
  · rintro ⟨a, b⟩ l _ K s LL g
    exact ⟨a l K s LL g, b l K s LL g⟩

theorem wach_free_of_properties {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : P1 D HW F) : WachLatticeFreeGlobal D HW F := ((wach_first_iff_free_monoidal D HW F).1 h).1

theorem wach_characterisation_of_tenth {D : Formalism.BasicNotions.D7} {HW : HWOf D.loc} {F : FonOf D.loc D.locA HW}
    (h : product_first_zeroth_parts D HW F) : WachCharacterisation D HW F := ((product_first_zeroth_parts_iff_wach_and_twist D HW F).1 h).1

theorem wach_theorem_iff_refined (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (C : CmpOf D.loc D.locA HW F) :
    thm1 D HW F C ↔ (WachLatticeFreeGlobal D HW F ∧ WachLatticeMonoidalGlobal D HW F) ∧ P2 D HW F ∧ P3 D HW F C ∧ P4 D HW F C ∧
      P5 D HW F ∧ P6 D HW F ∧ P7 D HW F ∧ P8 D HW F ∧ P9 D HW F ∧ (WachCharacterisation D HW F ∧ WachTwistLocalTheory D HW F) := by
  rw [wach_theorem_iff_properties, wach_first_iff_free_monoidal, product_first_zeroth_parts_iff_wach_and_twist]

end Design

end Formalism.MainNotions.DeltaInvariantLattices
