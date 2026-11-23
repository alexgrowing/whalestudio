import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.KappaEndpoints
import Formalism.FlagUnipotentLattices.GlobalAssemblyDoubled

noncomputable section

open scoped Classical
open ValuativeRel

namespace Formalism.L2.SG.NGDict

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG Formalism.MainNotions.BridgeLemma Formalism.MainNotions.KappaEndpoints

section Obj

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable (H : HermSp M V) {r : ℕ}

def thE (M : Model F E) : E := algebraMap F E (theta M)

def InThO (M : Model F E) (c : E) : Prop := ∃ d ∈ M.L.O, c = thE M * d

def InRR (M : Model F E) (a a' : E) : Prop := a' ∈ M.L.O ∧ InThO M (a + a')

def MM (t : Term V M r) : Submodule M.L.O V := Submodule.span M.L.O (Set.range (H.MMfam t))

def ME (t : Term V M r) : Submodule E V := Submodule.span E (Set.range (H.MMfam t))

def satM (t : Term V M r) : Submodule M.L.O V := t.abelian₂ ⊓ (ME H t).restrictScalars M.L.O

abbrev BB (t : Term V M r) : Type := ↥(satM H t) ⧸ (MM H t).comap (satM H t).subtype

def be (t : Term V M r) : ℕ := Nat.card (BB H t)

def OutAt (t : Term V M r) (y : V) (i : Fin (r + 1)) : Prop :=
  ∃ al al' : Fin (r + 1) → E, thE M • y = ∑ j, al j • t.f j + ∑ j, al' j • t.f' j ∧ ¬ InRR M (al i) (al' i)

def lev (t : Term V M r) (y : V) : ℕ := sSup {n | ∃ i : Fin (r + 1), n = i.val + 1 ∧ OutAt t y i}

def levC (t : Term V M r) (c : BB H t) : ℕ :=
  sSup {n | ∃ y : satM H t, Submodule.Quotient.mk y = c ∧ n = lev t y}

def Jmax (t : Term V M r) : ℕ := sSup (Set.range (levC H t))

def beJ (t : Term V M r) : ℕ := Nat.card {c : BB H t // levC H t c = Jmax H t}

def IsTypeBe (t : Term V M r) : Prop :=
  BBne (H := H) t ∧ (∀ y ∈ satM H t, ¬ OutAt t y (Fin.last r)) ∧
    ∀ x₁ x₁' x₂ x₂' : V, x₁ ∈ H.X t.f → x₁' ∈ H.X t.f' → x₂ ∈ H.X t.f → x₂' ∈ H.X t.f' →
      x₁ + x₁' ∈ H.smulLat (thE M) t.abelian₂ → x₂ + x₂' ∈ H.smulLat (thE M) t.abelian₂ → InThO M (H.h x₁ x₂')

def Iset (t : Term V M r) : Set (BB H t) :=
  {c | ∃ (y : satM H t) (w la la' : V), c = Submodule.Quotient.mk y ∧ w ∈ H.W0 t.f t.f' ∧ la ∈ H.X t.f ∧
    la' ∈ H.X t.f' ∧ w + la ∈ t.abelian₂ ∧ w + la' ∈ t.abelian₂ ∧ thE M • (y : V) = la' - la}

def Icard (t : Term V M r) : ℕ := Nat.card (Iset H t)

structure TyV where
  kindBe : Bool
  be : ℕ
  J : ℕ
  beJ : ℕ

def typOf (t : Term V M r) : TyV :=
  if IsTypeBe H t then ⟨true, be H t, Jmax H t, beJ H t⟩ else ⟨false, be H t, 0, 0⟩

end Obj

section Steps

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]
variable {H : HermSp M V} {r : ℕ}

def A0 (P : FPair H r) : ℝ := P.Hp ^ (9 * (r + 1) ^ 2 + 12 * (r + 1))

def A1 (P : FPair H r) : ℝ := 4 * P.Hp ^ (4 * (r + 1))

def massE {P : FPair H r} (R : Reps P) (d : Datum P) (S : Term V M r → Prop) : ENNReal :=
  ∑' t : {t // t ∈ R.RT d ∧ S t}, ENNReal.ofReal (mu P t.1)

def FF (H : HermSp M V) (β J βJ : ℕ) (t : Term V M r) : Prop :=
  IsTypeBe H t ∧ be H t = β ∧ Jmax H t = J ∧ beJ H t = βJ

def StepFin {P : FPair H r} (R : Reps P) : Prop :=
  (∃ Ds : Finset R.RD, ∀ d : R.RD, d ∉ Ds → R.RT d.1 = ∅) ∧ ∀ d : R.RD, Summable (fun t : R.RT d.1 => mu P t.1)

def StepBB (P : FPair H r) : Prop :=
  ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t →
    Finite (BB H t) ∧ (be H t : ℝ) ≤ P.Hp ∧ (∃ i : ℕ, be H t = qF F ^ i) ∧ ∃ i : ℕ, Icard H t = qF F ^ i

def MassBoundIndexSets (k : ℕ) {P : FPair H r} (R : Reps P) : Prop :=
  ∀ (d : Datum P) (j : ℕ), massE R d (fun t => Icard H t = j) ≤ ENNReal.ofReal (A0 P * (j : ℝ) ^ (k - 1))

def MassBoundLevelSets (k : ℕ) {P : FPair H r} (R : Reps P) (d0 : Datum P) : Prop :=
  ∀ β : ℕ, 1 ≤ β →
    ∑' d : R.RD, ENNReal.ofReal (Datum.wt d0 d.1) * massE R d.1 (fun t => be H t = β) ≤
      ENNReal.ofReal (A1 P * ((β : ℝ) ^ (k - 1))⁻¹) * nn R d0

def StepAl (P : FPair H r) : Prop :=
  ∀ (d : Datum P) (t : Term V M r), IsTermOver P d t → BBne (H := H) t → ¬ IsTypeBe H t →
    (Icard H t : ℝ) ≤ (be H t : ℝ) / (qF F : ℝ)

def StepE (k : ℕ) {P : FPair H r} (R : Reps P) : Prop :=
  ∀ (d : Datum P) (β J βJ : ℕ), 2 ≤ β → 1 ≤ J → J ≤ r → 1 ≤ βJ → massE R d (FF H β J βJ) ≠ ⊤ →
    ‖amp R d (FF H β J βJ)‖ ≤ 7 * (qF F : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) * massS R d (FF H β J βJ)

def StepTypes (P : FPair H r) : Prop :=
  {x : TyV | ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t ∧ BBne (H := H) t ∧ typOf H t = x}.Finite ∧
    ({x : TyV | ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t ∧ BBne (H := H) t ∧ typOf H t = x}.ncard : ℝ) ≤
      P.Hp ^ (r + 2)

def StepHp (P : FPair H r) : Prop := (qF F : ℝ) ≤ P.Hp

def Steps (k : ℕ) {P : FPair H r} (R : Reps P) (d0 : Datum P) : Prop :=
  StepFin R ∧ StepBB P ∧ MassBoundIndexSets k R ∧ MassBoundLevelSets k R d0 ∧ StepAl P ∧ StepE k R ∧ StepTypes P

end Steps

def DictAll (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → ¬ P.PrimeTo →
        StepHp P ∧ ∀ (R : Reps P) (d0 : Datum P), Steps k R d0

def Glue (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → StepHp P →
        ∀ (R : Reps P) (d0 : Datum P), Steps k R d0 →
          Nonempty (NGCore1 k R d0 22 7) ∧ Nonempty (NGCore2 k R d0 22 (fun t => ¬ BBne (H := H) t)) ∧
            Nonempty (NGCore2 k R d0 22 (fun _ => True))

def AssemblyConstantThirtyNine (k r : ℕ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : HermSp M V),
      Module.finrank E V = k + 2 * r + 1 → 4 * r + 7 ≤ k →
      ∀ P : FPair H r, P.RelG (theta M) → (∃ (d : Datum P) (t : Term V M r), IsTermOver P d t) → StepHp P →
        ∀ (R : Reps P) (d0 : Datum P), Steps k R d0 →
          sumSq R d0 (BBne (H := H)) ≤ ENNReal.ofReal (P.Hp ^ ((39 : ℝ) * ((r : ℝ) + 1) ^ 2) *
              (qF F : ℝ) ^ (-((k : ℝ) - 2 * r - 5))) * nn R d0 ∧
          sumSq R d0 (fun t => ¬ BBne (H := H) t) ≤ ENNReal.ofReal (P.Hp ^ ((39 : ℝ) * ((r : ℝ) + 1) ^ 2)) * nn R d0 ∧
          sumSq R d0 (fun _ => True) ≤ ENNReal.ofReal (P.Hp ^ ((39 : ℝ) * ((r : ℝ) + 1) ^ 2)) * nn R d0

theorem NGLeft_of_dict (k r : ℕ) (hk : 4 * r + 7 ≤ k) (hG : Glue k r) (hD : DictAll k r) : NGLeft k r 22 7 := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hV P hR hT
  refine ⟨fun hP => ⟨NGOrbit0_of hP hR, NGUnimod_of hOK hR.1⟩, fun hP R d0 => ?_⟩
  obtain ⟨hHp, hS⟩ := hD F E M hOK V H hV hk P hR hT hP
  exact hG F E M hOK V H hV hk P hR hT hHp R d0 (hS R d0)

theorem local_counting_bound_of_dictionary (k r : ℕ) (C : ℝ) (hk : 4 * r + 7 ≤ k) (hC1 : (gainBoundConstant 22 7 : ℝ) ≤ C) (hC2 : (nongenericConstantNoGain 22 : ℝ) ≤ C)
    (hG : Glue k r) (hD : DictAll k r) : Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r C :=
  nongeneric_local_of_remainder k r 22 7 C hk hC1 hC2 (NGLeft_of_dict k r hk hG hD)

theorem local_counting_bound_thirty_nine (k r : ℕ) (hk : 4 * r + 7 ≤ k) (hG : AssemblyConstantThirtyNine k r) (hD : DictAll k r) :
    Formalism.MainNotions.NonGenericAndKTwoTheorems.NonGenericLocalBound k r 39 := by
  intro F _ _ _ E _ _ _ _ M hOK V _ _ H hV P hR
  by_cases hP : P.PrimeTo
  · exact NGAt_of_good hOK k 39 hP hR
  by_cases hT : ∃ (d : Datum P) (t : Term V M r), IsTermOver P d t
  · obtain ⟨hHp, hS⟩ := hD F E M hOK V H hV hk P hR hT hP
    exact NGAt_of hOK k 39 (fun R d0 => hG F E M hOK V H hV hk P hR hT hHp R d0 (hS R d0))
      (fun h => absurd h hP)
  · refine NGAt_of_noTerms hOK k 39 (fun R d => ?_)
    ext t
    simp only [Set.mem_empty_iff_false, iff_false]
    exact fun ht => hT ⟨d, t, (R.hRT d).1 ht⟩

end Formalism.L2.SG.NGDict
