import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj

namespace GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def SizeOK (D : D7) : Prop :=
  1800 < D.R.r ∧ ∀ (τ : D.what₂.Tau) (j : Fin D.R.m) (h : j.1 + 1 < D.R.m),
    (D.R.t : ℚ) + 2 * (bigN D : ℚ) ^ 3 < (D.hc τ).b ⟨j.1 + 1, h⟩ - (D.hc τ).b j

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def HaarAt (M : Vol G) (X : Node) : Prop :=
  (M.ν X).IsHaarMeasure ∧ IsFundamentalDomain (GQ (G.V X)) (M.fd X) (M.ν X)

def IsDatum (W : G.Weil) (a : Arrow T) (f : Sch G a) : Prop := IsThetaFunO W.ψ (G.pS a.pair) (G.pT a.pair) f

def OrderAt (W : G.Weil) (M : Vol G) (a : Arrow T) : Prop :=
  ∀ F : Fn G a.src, GlobalTheory.Mem.Th.IsCuspForm W.θ (G.V a.src) F → G.IsListed W.θ a.src F →
    ∀ f : Sch G a, IsDatum W a f →
      LiftConv W M a f F ∧ GlobalTheory.Mem.Th.IsCuspForm W.θ (G.V a.tgt) (liftA W M a f F) ∧
        (liftA W M a f F = 0 ∨ G.IsListed W.θ a.tgt (liftA W M a f F))

def Order : Prop :=
  ∀ (D : D7), SizeOK D → ∀ (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 → ∀ (sc : Consts) (G : GridData L sc) (W : G.Weil)
    (M : Vol G) (a : Arrow T), a.pair.InRange D.R.m → HaarAt M a.src → OrderAt W M a

example (t : T) (m i j : ℕ) : ((Arrow.right i j : Arrow T).pair.InRange m ↔ i + 1 ≤ m ∧ j ≤ m) ∧
    ((Arrow.down t i j).pair.InRange m ↔ i ≤ m ∧ j + 1 ≤ m) ∧ ((Arrow.coreUp i : Arrow T).pair.InRange m ↔ i + 1 ≤ m) ∧
    ((Arrow.coreDown i : Arrow T).pair.InRange m ↔ i + 1 ≤ m) ∧ ((Arrow.col t j).pair.InRange m ↔ j + 1 ≤ m) :=
  ⟨Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl, Iff.rfl⟩

example (θ : InfFam D) (i j : ℕ) (φ : Fn G (.grid i j)) (φ' : Fn G (.core i)) :
    (G.IsListed θ (.grid i j) φ ↔ ∀ τ, IsTypeAt θ _ τ (parV D sc.cGap i j τ) fun g => star (φ g)) ∧
    (G.IsListed θ (.core i) φ' ↔ ∀ τ, IsTypeAt θ _ τ ((num D sc.cGap τ).parPi i) φ') := ⟨Iff.rfl, Iff.rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.HaarEquallySpacedConditions

end
