import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OppositeColumnLifts
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlipPath

variable {D : D7}

section Local

variable (e : AE D) (I : Ideal (𝓞 D.host.E)) (ν : (AE D)ˣ →* Circle)

def IsPlaces : Prop := I ≠ ⊥ ∧ ∃ P : Finset (Pl D.host.E), IsIdemSum e P ∧ ∀ w ∈ P, I ≤ w.asIdeal

def TrivMod : Prop := ∀ z : (AE D)ˣ, e * ((z : AE D) - 1) = (z : AE D) - 1 → InI I (toEAf D ((z : AE D) - 1)) → ν z = 1

def OwnDepth {p q : ℕ} (φ : Matrix (Fin p) (Fin q) (Datum.EAf D) → ℂ) : Prop :=
  ∀ y, InHalf e y → (φ y ≠ 0 → IsIntM y) ∧ ∀ u, InHalf e u → (∀ i j, InI I (u i j)) → φ (y + u) = φ y

def DualDepth {p q : ℕ} (φ : Matrix (Fin p) (Fin q) (Datum.EAf D) → ℂ) : Prop :=
  ∀ y, InHalf e y → (φ y ≠ 0 → ∀ i j, InIinv I (y i j)) ∧ ∀ u, InHalf e u → IsIntM u → φ (y + u) = φ y

def ColDepth {a d₁ d₂ : ℕ} (Φ : Matrix (Fin d₁) (Fin a) (Datum.EAf D) → Matrix (Fin d₂) (Fin a) (Datum.EAf D) → ℂ) : Prop :=
  ∀ x₁ x₂, InHalf e x₁ → InHalf e x₂ →
    (Φ x₁ x₂ ≠ 0 → IsIntM x₁ ∧ ∀ i j, InIinv I (x₂ i j)) ∧
    ∀ u₁ u₂, InHalf e u₁ → InHalf e u₂ → (∀ i j, InI I (u₁ i j)) → IsIntM u₂ → Φ (x₁ + u₁) (x₂ + u₂) = Φ x₁ x₂

def IsCosetReps {n : ℕ} (Rp : Set (GL (Fin n) (AE D))) : Prop :=
  (∀ r ∈ Rp, AtE e r) ∧ ∀ g, AtE e g → ∃! r, r ∈ Rp ∧ InK e I (g * r⁻¹)

variable {e I}

end Local

theorem isSelfDualC_sgn (ε : Bool) {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : IsSelfDualC S Λ) :
    IsSelfDualC (sgn ε S) Λ := by
  cases ε
  · exact h
  · refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
    have e : ∑ i, ∑ j, star (x i) * (neg S).gram i j * y j = -∑ i, ∑ j, star (x i) * S.gram i j * y j := by
      simp [neg_gram, Finset.sum_neg_distrib]
    refine ⟨fun ⟨b, hb⟩ => ⟨-b, ?_⟩, fun ⟨b, hb⟩ => ⟨-b, ?_⟩⟩
    · refine Eq.trans ?_ e.symm
      rw [← hb]; simp
    · have := hb.trans e
      rw [← neg_eq_iff_eq_neg] at this
      rw [← this]; simp

section Fin

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : Node D} {e : AE D} {P : Finset (Pl D.host.E)} {f₀ f : WO S.V T.V → ℂ}

theorem isFinVec_of_own {ε : Bool} (hv : IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    {φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ} (h : IsDatOwn ψ ε S T e f₀ φ f) : IsFinVec ψ θ ε S T f := by
  obtain ⟨hSB, ⟨Tm, hTm⟩, hall⟩ := h
  rw [hall Tm hTm]
  exact finVec_of_mem_span (S := sgn ε S.V) hv (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 (isSelfDualC_sgn ε hS) hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm hSB).1

end Fin

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

def GoodX (t : T) (e : AE D) (i j : ℕ) (f : DX G i j) : Prop :=
  ∃ φ, OwnDepth e (depth G t) φ ∧ IsDatOwn R.ψ true (G.V (i + 1) j) (G.V i j) e (G.X i j).vac φ f

def GoodT (t : T) (e : AE D) (i j : ℕ) (f : DT G i j) : Prop :=
  ∃ φ, DualDepth e (depth G t) φ ∧ IsDatDual R.ψ (G.V i j) (G.V i (j + 1)) e (G.th t i j).vac φ f

end GlobalTheory.FlipPath

end
