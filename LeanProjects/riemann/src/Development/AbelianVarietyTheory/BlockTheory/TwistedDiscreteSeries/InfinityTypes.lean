import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx

namespace GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Arith

variable (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau)

abbrev pS : ℕ := ((Wc D i).sig (tauE D τ)).1

abbrev qS : ℕ := ((Wc D i).sig (tauE D τ)).2

abbrev eS : ℚ := (D.hc τ).e i

abbrev aP (a : ℕ) : ℕ := aPl D i (pS D i τ) τ a

abbrev aM (a : ℕ) : ℕ := aMi D i (pS D i τ) (qS D i τ) τ a

def centred (a : ℕ) : ℚ := Formalism.L2.NTheta.lamAt (D.hc τ) a + eS D i τ

def aPlusQ (a : ℕ) : ℚ := centred D i τ a - ((pS D i τ : ℚ) - ((a : ℚ) + 1)) - ((D.R.t : ℚ) + 1) / 2

def dRowQ (c : ℕ) : ℚ := centred D i τ (pS D i τ + c) + ((c : ℚ) + 1) + ((D.R.t : ℚ) - 1) / 2

def dShift : ℚ := ((pS D i τ : ℚ) - (qS D i τ : ℚ)) / 2 - eS D i τ - 1 / 2

def thetaWt (a : ℕ) : ℤ :=
  if a < pS D i τ then (aP D i τ a : ℤ)
  else if a < pS D i τ + D.R.t then 0
  else -(aM D i τ (qS D i τ - 1 - (a - (pS D i τ + D.R.t))) : ℤ)

def IsDataOf (w : IndefiniteWeightData.WeightData) : Prop :=
  w.k = D.R.k ∧ w.m = D.R.m ∧ w.t = D.R.t ∧ w.j = (i : ℕ) + 1 ∧ (w.e : ℚ) = eS D i τ ∧
    (∀ a : Fin (D.R.k - 1), (w.v (a + 2) : ℚ) = (D.hc τ).v a) ∧ ∀ a : Fin D.R.m, (w.b (a + 1) : ℚ) = (D.hc τ).b a

structure ArithAt : Prop where

  sig : pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1)

  rank : pS D i τ + qS D i τ = D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t

  aP_eq_rat : ∀ a < pS D i τ, (aP D i τ a : ℚ) = aPlusQ D i τ a

  aM_eq : ∀ c < qS D i τ, (aM D i τ (qS D i τ - 1 - c) : ℚ) = -dRowQ D i τ c

  aPlus_antitone : ∀ a b, a ≤ b → b < pS D i τ → aP D i τ b ≤ aP D i τ a

  aM_anti : ∀ a b, a ≤ b → b < qS D i τ → aM D i τ b ≤ aM D i τ a

  aPlus_pos : ∀ a < pS D i τ, 1 ≤ aP D i τ a

  aM_pos : ∀ a < qS D i τ, 1 ≤ aM D i τ a

  kap_plus : ∀ a : Fin (pS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl a) : ℚ) =
      (aP D i τ a : ℚ) + ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  kap_minus : ∀ c : Fin (qS D i τ),
    (Formalism.L2.NTheta.kapW (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) : ℚ) =
      -(aM D i τ (qS D i τ - 1 - c) : ℚ) - ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ

  d_int : ∃ z : ℤ, dShift D i τ = z

  lamPrime_eq : ∀ w : IndefiniteWeightData.WeightData, IsDataOf D i τ w → ∀ a < D.R.r + D.R.t,
    w.lamPrime (a + 1) = (thetaWt D i τ a : ℚ) + dShift D i τ

  coef_isLamPrime : Bridge.IsLamPrime (D := D) (Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ) ((i : ℕ) + 1) τ

  coef_eq : ∀ a : Fin (Vc D i).rank,
    ((Bridge.lamLdef (D := D) (Vc D i).rank ((i : ℕ) + 1) τ).w a : ℚ) = (thetaWt D i τ a : ℚ) + dShift D i τ

end Arith

structure InfTypesAt {D : D7} {T : Type} (L : LevCh D T) (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau) : Prop where

  mu : HasInfExp D (L.mu t ((i : ℕ) + 1)) τ (-eS D i τ)

  eta : HasInfExp D L.eta τ (1 / 2)

  chiV : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).1 τ (-eS D i τ)

  chiW : HasInfExp D (Lift.chrTh (L.mu t) L.eta ((i : ℕ) + 1)).2 τ (-eS D i τ - 1 / 2)

def WeightsMatch : Prop :=
  (∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ) ∧
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), InfTypesAt R.toLevCh i t τ

def WeightsMatchLev : Prop :=
  (∀ (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau), ArithAt D i τ) ∧
  ∀ (D : D7) (T : Type) (L : LevCh D T) (μ0 : T), L.Is μ0 →
    ∀ (i : Fin D.R.m) (t : T) (τ : D.what₂.Tau), InfTypesAt L i t τ

example (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) (h : pS D i τ + qS D i τ = D.R.r) :
    (∀ a : Fin (pS D i τ), Formalism.L2.NTheta.kapQ (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inl a) =
      aPlusQ D i τ a + ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ) ∧
    ∀ c : Fin (qS D i τ), Formalism.L2.NTheta.kapQ (D.hc τ) (pS D i τ) (qS D i τ) (Sum.inr c) =
      dRowQ D i τ c - ((D.R.r : ℚ) + D.R.t) / 2 - eS D i τ := by
  have h' : (D.R.r : ℚ) = (pS D i τ : ℚ) + (qS D i τ : ℚ) := by exact_mod_cast h.symm
  refine ⟨fun a => ?_, fun c => ?_⟩
  · simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inl, aPlusQ, centred, h']; ring
  · simp only [Formalism.L2.NTheta.kapQ, Sum.elim_inr, dRowQ, centred, h']; ring

example (D : D7) (i : Fin D.R.m) (τ : D.what₂.Tau) :
    (pS D i τ = D.R.k + i ∧ qS D i τ = D.R.m - ((i : ℕ) + 1)) ∧ (Vc D i).rank = D.R.r + D.R.t := by
  have h := D.sp.W_sigval ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2 (tauE D τ)
  refine ⟨⟨?_, ?_⟩, D.sp.V_rank _ (Nat.le_add_left _ _) i.2⟩
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).1 = _
    rw [h]; simp [Ranks.sigW]
  · show ((D.sp.W ((i : ℕ) + 1)).sig (tauE D τ)).2 = _
    rw [h]; rfl

end GlobalTheory.IndefiniteRowSideFullHecke.InfinityTypes

end
