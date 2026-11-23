import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ToPairMul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries

namespace GlobalTheory.RowReal

variable {D : D7}

theorem GQ_negGA_mem (V : HSp D) {γ : GA D V} (hγ : γ ∈ GQ V) : negGA V γ ∈ GQ (negSp V) := by
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hγ)
  refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨x, ?_, e⟩)
  have hx' : Formalism.UG.cT _ (x : Matrix _ _ _) * V.gram * (x : Matrix _ _ _) = V.gram := hx
  show Formalism.UG.cT _ (x : Matrix _ _ _) * (-V.gram) * (x : Matrix _ _ _) = -V.gram
  rw [Matrix.mul_neg, Matrix.neg_mul, hx']

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem toPair_GQ (p : Pair T) {γ : GA D (G.V p.small)} {γ' : GA D (G.V p.big)} (hγ : γ ∈ GQ (G.V p.small))
    (hγ' : γ' ∈ GQ (G.V p.big)) : (G.toPair p γ γ').1 ∈ GQ (G.pS p) ∧ (G.toPair p γ γ').2 ∈ GQ (G.pT p) := by
  cases p with
  | chi i j => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | mu t i j => exact ⟨hγ, hγ'⟩
  | core i => exact ⟨GQ_negGA_mem _ hγ', hγ⟩
  | top t j => exact ⟨hγ, hγ'⟩

theorem ker_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T),
    p.InRange D.R.m →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ (G.pS p) (G.pT p) f → ∀ γ ∈ GQ (G.V p.small), ∀ γ' ∈ GQ (G.V p.big),
    ∀ g h, W.ker p f (γ * g) (γ' * h) = W.ker p f g h := by
  intro D T L sc G W p hp f hf γ hγ γ' hγ' g h
  have hw := W.om_is p hp
  obtain ⟨h1, h2⟩ := toPair_GQ p hγ hγ'
  have e : W.ker p f (γ * g) (γ' * h) =
      W.om p (G.toPair p γ γ') (W.om p (G.toPair p g h) f) 0 := by
    simp only [GridData.Weil.ker, thetaKO, toPair_mul, Prod.mk.eta, map_mul, Module.End.mul_apply]
  rw [e]
  have := hw.om_aut _ h1 _ h2 (W.om p (G.toPair p g h) f) (hw.om_pres (G.toPair p g h) f hf)
  rw [Prod.mk.eta] at this
  rw [this]
  simp only [GridData.Weil.ker, thetaKO, Prod.mk.eta]

end GlobalTheory.RowReal
