import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThPDatumEq
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointFrameMatrixAddIntegralReduction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

variable {D : D7}

def liftI (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) : Ideal (𝓞 D.host.E) :=
  ∏ PP ∈ Pg ∪ Q, conjI PP.asIdeal

theorem frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) :
    frMapAdj S T βS βT 0 = 0 := by
  unfold frMapAdj
  simp

theorem isIntM_zero {b a : ℕ} : IsIntM (0 : Matrix (Fin b) (Fin a) (EAf D)) := fun _ _ => zero_mem _

theorem redM_frMapAdj_zero (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (PP : Formalism.L2.DIV.Pl D.host.E) : redM PP (frMapAdj S T βS βT 0) = 0 := by
  have h0 : IsIntM (frMapAdj S T βS βT 0) := by rw [frMapAdj_zero]; exact isIntM_zero
  have h := (GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT 0 0 h0 h0).2 PP
  rw [add_zero] at h
  exact (left_eq_add.mp h)

def liftL (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D) : AddSubgroup (WO S T) where
  carrier := {x | IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x) ∧
    ∀ PP ∈ Pg ∪ Q, redM PP (frMapAdj S T βS βT x) = 0}
  zero_mem' := by
    refine ⟨fun i j => by simp, ?_, fun PP _ => ?_⟩
    · rw [frMapAdj_zero]; exact isIntM_zero
    · exact redM_frMapAdj_zero S T βS βT PP
  add_mem' := by
    rintro x y ⟨hx1, hx2, hx3⟩ ⟨hy1, hy2, hy3⟩
    obtain ⟨h1, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x y hx2 hy2
    refine ⟨fun i j => ?_, h1, fun PP hPP => ?_⟩
    · simp only [Matrix.add_apply, mul_add, hx1 i j, hy1 i j]
    · rw [h2, hx3 PP hPP, hy3 PP hPP, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2, hx3⟩
    have hneg : frMapAdj S T βS βT (-x) = -frMapAdj S T βS βT x := by
      unfold frMapAdj
      simp [Matrix.map_neg, Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul]
    have hI : IsIntM (frMapAdj S T βS βT (-x)) := fun i j => by
      rw [hneg, Matrix.neg_apply]; exact neg_mem (hx2 i j)
    obtain ⟨-, h2⟩ := GlobalTheory.FrameAdjAdd.frMapAdj_add_isIntM_redM S T βS βT x (-x) hx2 hI
    refine ⟨fun i j => ?_, hI, fun PP hPP => ?_⟩
    · simp only [Matrix.neg_apply, mul_neg, hx1 i j]
    · have := h2 PP
      rw [add_neg_cancel, redM_frMapAdj_zero, hx3 PP hPP, zero_add] at this
      exact this.symm

def adjA (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (a : AE D) (x : WO S T) :
    Matrix (Fin S.rank) (Fin T.rank) (EAf D) :=
  toEAf D a • HMul.hMul βS.val (frMapAdj S T βS βT x)

def IsMover (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (e a : AE D)
    (k₀ : GA D S) : Prop :=
  k₀ ∈ GfC S ∧ (∀ x : WO S T, IsHalf (1 - e - cA D e) x → actO S T k₀ 1 x = x) ∧
    ∀ x : WO S T, IsHalf (cA D e) x →
      frMapAdj S T βS βT (actO S T k₀ 1 x) = adjA S T βS βT a x

def IsGen {S T : HSp D} (C : Ctx S T) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (Pg Q : Finset (Formalism.L2.DIV.Pl D.host.E)) (e a : AE D) : Prop :=
  ∀ x : WO S T, IsHalf (cA D e) x →
    (IsIntM (adjA S T βS βT a x) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) C.X.Λ)) ∧
    ((IsIntM (adjA S T βS βT a x) ∧
      ∀ PP ∈ Pg ∪ Q, redM PP (adjA S T βS βT a x) = 0) ↔
      x ∈ hatA S T (tens (stdL D.host.E S.rank) (liftI Pg Q • C.X.Λ)))

end GlobalTheory.LiftLevel

end
