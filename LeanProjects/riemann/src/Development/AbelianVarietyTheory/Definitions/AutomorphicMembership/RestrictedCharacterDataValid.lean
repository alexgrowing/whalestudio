import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FieldValuesMemFixedField
import Formalism.LocalToGlobal.Divisibility.ColumnFamilyPlaceCharacterComap
import Formalism.LocalToGlobal.Divisibility.TiedLemmas
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRangeFamily
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OrZeroOf

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.Mem.R3.Res

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T T' : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (f : T' → T) (μ : T')

def dat3 (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : RealDat3 D (A3.comap f μ) Ks where
  toRealDat := dat2 (A := A3.A) f μ R.toRealDat mu tw
  plI := R.plI
  SF := R.SF
  phs := R.phs
  lam3 i t := R.lam3 i (f t)

def bare3 (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G)
    (ψ1 : P1 →* D.what₂.LLˣ) : Face3 D A3 where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc _ := ⟨PEmpty, fun u => u.elim, fun u => u.elim, fun u => u.elim⟩
  Sp _ := ⟨ℂ, inferInstance, inferInstance, fun u => u.elim, ⊥⟩
  Zsc _ := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

variable {f μ} {R : RealDat3 D (A3.comap id (f μ)) Ks} (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
  (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) {P0 : Subgroup G} {ψ0 : P0 →* D.what₂.LLˣ} {P1 : Subgroup G} {ψ1 : P1 →* D.what₂.LLˣ}

set_option maxHeartbeats 2000000 in

theorem isInert (h : R.IsInert) : (dat3 f μ R mu tw).IsInert := by
  exact ⟨⟨h.tie.plI_inj, fun t Q => h.tie.okI (f t) Q⟩, h.onto, fun t => h.hR (f t), fun i t => h.hL i (f t), h.SF⟩

set_option maxHeartbeats 2000000 in

theorem pThmB (h : R.PThmB) : (dat3 f μ R mu tw).PThmB := by
  intro t p x hx
  exact h (f t) p x hx

set_option maxHeartbeats 2000000 in

theorem isScal (h : R.IsScal (bare3 _ P0 ψ0 P1 ψ1)) (hB : R.PThmB) : (dat3 f μ R mu tw).IsScal (bare3 _ P0 ψ0 P1 ψ1) where
  lam0 i t := h.lam0 i (f t)
  kap κ hκ hne := by
    obtain ⟨t, p, hp, hl⟩ := hne
    exact Lift.IsKap.unique (pThmB mu tw hB) hκ t p hp hl
  off := h.off
  abs0 i t := h.abs0 i (f t)
  abs := h.abs
  tup i t := h.tup i (f t)

structure NewTup (R : RealDat3 D (A3.comap id (f μ)) Ks) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T')
    (tw : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop where

  sub : tw ⊆ R.twPl

  conj : ∀ w, Formalism.DivisionValues.conjPl w ∈ tw ↔ w ∈ tw

  on : ∀ w ∈ tw, f (mu w) = R.mu w

  off : ∀ w, w ∉ tw → mu w = μ

  used : ∀ t, t = μ ∨ ∃ w, mu w = t

variable {mu tw} in

theorem isTup (hf : Function.Injective f) (h : R.IsTup) (n : NewTup R mu tw) : (dat3 f μ R mu tw).IsTup where
  mu_off := n.off
  mu_used := n.used
  mu_ne w hw heq := by
    change mu w = μ at heq
    apply h.mu_ne w (n.sub hw)
    rw [← n.on w hw, heq]
    rfl
  mu_conj w := by
    change mu (Formalism.DivisionValues.conjPl w) = mu w
    by_cases hw : w ∈ tw
    · apply hf
      have hc : Formalism.DivisionValues.conjPl w ∈ tw := (n.conj w).2 hw
      rw [n.on _ hc, n.on w hw]
      exact h.mu_conj w
    · have hc : Formalism.DivisionValues.conjPl w ∉ tw := fun hc => hw ((n.conj w).1 hc)
      rw [n.off _ hc, n.off w hw]
  mu_on w hw := by
    obtain ⟨ψw, Qw, h1, h2⟩ := h.mu_on w (n.sub hw)
    refine ⟨ψw, Qw, h1, ?_⟩
    change R.xiH (f (mu w)) = R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw
    rw [n.on w hw]
    exact h2

variable {mu tw} in
set_option maxHeartbeats 2000000 in

theorem restricted_character_data_valid (hf : Function.Injective f) (h : R.WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1)) (e : R.toRealDat.ExAt) (hB : R.PThmB)
    (n : NewTup R mu tw) : (dat3 f μ R mu tw).WeakCharacterisation (bare3 _ P0 ψ0 P1 ψ1) where
  base := baseW mu tw hf h.base e
  inert := isInert mu tw h.inert
  fullY t := h.fullY (f t)
  fullX t := h.fullX (f t)
  fullP i t := h.fullP i (f t)
  scal := isScal mu tw h.scal hB
  tup := isTup hf h.tup n
  phase := h.phase
  allPl := h.allPl

set_option maxHeartbeats 2000000 in

theorem keep {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Keep (A3 := A3.comap id (f μ)) R.toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG) :
    Keep (A3 := A3.comap f μ) (dat3 f μ R mu tw).toRealDat (bare3 _ P0 ψ0 P1 ψ1).lv2 cG where
  std := h.std
  signs := h.signs
  frames := h.frames
  beta := h.beta
  prX := h.prX
  grp := h.grp
  psi := h.psi
  guard := ⟨fun t => h.guard.1 (f t), fun t => h.guard.2 (f t)⟩
  valKs := h.valKs
  frameKs := h.frameKs
  levKs := h.levKs

variable {mu tw} in
set_option maxHeartbeats 2000000 in

theorem pins (hf : Function.Injective f) {cG : G0 R.Pg D.R.r ≃* G0g D.nd} (h : Pins R (bare3 _ P0 ψ0 P1 ψ1) cG)
    (e : R.toRealDat.ExAt) (hB : R.PThmB) (n : NewTup R mu tw) : Pins (dat3 f μ R mu tw) (bare3 _ P0 ψ0 P1 ψ1) cG where
  char := restricted_character_data_valid hf h.char e hB n
  keep := keep mu tw h.keep
  phs := h.phs
  trSem := h.trSem

end GlobalTheory.Mem.R3.Res

end
