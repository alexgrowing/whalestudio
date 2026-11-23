import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.LocalRingCardinality.DataAmbForm
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate

noncomputable section

namespace GlobalTheory.EX.DQ

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB NumberField

def TupUsedAt (D : D7) : Prop := ∀ μ : D.what₂.Tup, DV.Used D μ

def GoodAllAt (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → I.Ok (C.twI w) ∧
    ∀ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (C.twI w)) → TwGoodOne D I (C.twI w) (C.sd w) (C.Q w) (C.k' w) (C.psi' w ^ a)

def TwAllAt (D : D7) (C : NChoice D) (T : ThData D) : Prop :=
  TwConjAt D C ∧ ∃ (N0 : D.ntw.Tw → ℕ) (S : ∀ (i' : D.ntw.Tw) (j : ℕ) (b : Bool), Finset (D.nexp.Dat i' j b)),
    GoodAllAt D C ⟨twEOf T, N0, S⟩

def MtStableAt (D : D7) : Prop :=
  ∀ (μ : D.what₂.Tup) (a : 𝓞 D.what₂.LL), ∀ y ∈ (D.what₂.Mtilde μ).carrier,
    D.what₂.embLL (a : D.what₂.LL) • y ∈ (D.what₂.Mtilde μ).carrier

def QD (D : D7) (O : Obj D) : Prop := TupUsedAt D ∧ TwAllAt D O.nch O.xd ∧ MtStableAt D

def withQD (QO : ∀ D : D7, Obj D → Prop) : ∀ D : D7, Obj D → Prop := fun D O => QO D O ∧ QD D O

def TupUsedF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x (_ : Fm.x1 < x), x0 ≤ x → ∀ (i : Fm.Ix x), ∀ μ : (Fm.D x i).what₂.Tup, DV.Used (Fm.D x i) μ

def TwAllF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x),
    TwConjAt (Fm.D x i) (Fm.ex x hx i).nch ∧
      ∃ (N0 : (Fm.D x i).ntw.Tw → ℕ) (S : ∀ (i' : (Fm.D x i).ntw.Tw) (j : ℕ) (b : Bool), Finset ((Fm.D x i).nexp.Dat i' j b)),
        GoodAllAt (Fm.D x i) (Fm.ex x hx i).nch ⟨twE Fm x hx i, N0, S⟩

def MtStableF {eps : ℝ} (Fm : FamP eps) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) (μ : (Fm.D x i).what₂.Tup) (a : 𝓞 (Fm.D x i).what₂.LL),
    ∀ y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier,
      (Fm.D x i).what₂.embLL (a : (Fm.D x i).what₂.LL) • y ∈ ((Fm.D x i).what₂.Mtilde μ).carrier

def Duty7 {eps : ℝ} (Fm : FamP eps) : Prop :=
  DC.PageFix Fm ∧ DC.PageWin Fm ∧ DC.globalTwisting_fact Fm ∧ DC.TameDistinctF Fm ∧ DC.WallAll Fm ∧ TupUsedF Fm ∧ TwAllF Fm

def cls7 (QO : ∀ D : D7, Obj D → Prop) : FamClass := DC.cls (ptO (withQD QO))

theorem familyClass_sevenDuties_and_stableLattices (QO : ∀ D : D7, Obj D → Prop) {eps : ℝ} (Fm : FamP eps) (h : cls7 QO Fm) : Duty7 Fm ∧ MtStableF Fm := by
  obtain ⟨a, b, c, d, e⟩ := DC.duty_of_cls _ Fm h
  have hq := DC.classOf_of_cls _ Fm h
  exact ⟨⟨a, b, c, d, e, ⟨Fm.x1, fun x hx _ i => (hq x hx i).2.1⟩, ⟨Fm.x1, fun x _ hx i => (hq x hx i).2.2.1⟩⟩,
    ⟨Fm.x1 + 1, fun x hx i => (hq x (by linarith) i).2.2.2⟩⟩

theorem familyClass_points_satisfy_objectProperty (QO : ∀ D : D7, Obj D → Prop) {eps : ℝ} (Fm : FamP eps) (h : cls7 QO Fm) : classOf (ptO QO) Fm :=
  fun x hx i => (DC.classOf_of_cls _ Fm h x hx i).1

theorem TwAllAt.twAt {D : D7} {C : NChoice D} {T : ThData D} (h : TwAllAt D C T) : LocalQuadraticParts.TWAt D C T := by
  obtain ⟨hc, N0, S, hS⟩ := h
  refine ⟨hc, N0, S, fun w hw => ⟨(hS w hw).1, ?_⟩⟩
  have := (hS w hw).2 1 (by simp)
  rwa [zpow_one] at this

theorem twAllAt_of_untwisted {D : D7} (C : NChoice D) (T : ThData D) (h : ∀ w, D.what₂.muAt w = D.what₂.mu0) : TwAllAt D C T :=
  ⟨fun w hw => absurd (h w) hw, fun _ => 0, fun _ _ _ => ∅, fun w hw => absurd (h w) hw⟩

end GlobalTheory.EX.DQ

end
