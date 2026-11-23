import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemHalfCosetSelf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull

namespace GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure HidaSetting (large₂ : SizeData₂ D) (R : RealDat D A Ks) (F : Face D A) : Prop where

  size : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂

  eser : GlobalTheory.GLq.ESerTie D

  host : HostHyp D

  hF : D.host.F = maximalRealSubfield D.host.E

  core : GlobalTheory.Hk3.Core R F

  mu_off : R.tup_mu_off

  mu_used : R.tup_mu_used

  mu_ne : R.tup_mu_ne

  mu_conj : R.tup_mu_conj

  mu_on : R.tup_mu_on

  grp : R.grp_record

  guard : Formalism.IndefR.FWT.QGuard R

  fin : Finite T

  fullY : ∀ t k, k + 1 < D.R.m → IsWeilFull R.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta (k + 1)).2 (R.ωY t k)

  fullX : ∀ t, IsWeilFull R.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).1
    (Lift.chrStep (R.toLevCh.mu t) R.eta D.R.m).2 (R.ωX t)

  std : IsStdChar D R.ψ (-1)

  stdX : (∀ a b, D.sp.X'.hT (D.sp.X'.frame a) (D.sp.X'.frame b) = if a = b then 1 else 0) ∧
    D.sp.X'.L0 = Submodule.span (𝓞 D.host.E) (Set.range D.sp.X'.frame)

  betaX : R.βX = 1

end

abbrev ChP := ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}, Choice R → Prop

def Big (Q : ChP) : Prop :=
  ∃ CF0 : ℝ, ∀ ε CF : ℝ, CF0 ≤ CF → ∃ x₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D), large₂.sc.eps = ε → x₀ ≤ large₂.sc.x →
    ∀ (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
      (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
      ∀ ch : Choice R, ch.Is → ch.AtScale CF large₂.sc.b → Q ch

def LinK : Prop := Big fun ch => ∀ a u, ConvK ch a u

def InjK : Prop := Big fun ch => ∀ u, (∀ a, psiK ch a u = 0) → u = 0

def ConstK : Prop := Big fun ch => ∀ i j t, SquareNonzero ch.W ch.S.B ch.rm t i j ∧ ch.c i j t ≠ 0

def SumOKK : Prop := Big fun ch => ∀ t a, ch.S.SumOK t (ch.Phi a)

def FormulaAt {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (κ : ℂ)
    (ze : T → D.what₂.LL) : Prop :=
  (∀ t, ∃ n : ℕ, 0 < n ∧ ze t ^ n = 1) ∧ ∀ t (x : A.fam.amb.FR t), x ∈ (A.fam.R t).goodF A.fam.X → ∀ a,
    D.what₂.embLL (ze t) * cTot ch t * psiK ch a (R.Th t (R.jX t x)) = κ * vK ch t x a

def Formula2K : Prop := Big fun ch => ch.FieldOK → ∃ κ ze, FormulaAt ch κ ze

def SumRatK : Prop := Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ch.FieldOK → ∀ t x a, vK ch t x a ∈ Set.range D.what₂.embLL

def RatioK : Prop := Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ch.FieldOK → ∀ i j t, sqRatio ch i j t ∈ Set.range D.what₂.embLL

set_option maxHeartbeats 1600000 in

theorem FormulaAt.ne_zero {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {ch : Choice R} {κ : ℂ} {ze : T → D.what₂.LL}
    (h : FormulaAt ch κ ze) {t : T} (hc : cTot ch t ≠ 0) {x : A.fam.amb.FR t}
    (hx : x ∈ (A.fam.R t).goodF A.fam.X) {a : Fin ch.n} (h0 : psiK ch a (R.Th t (R.jX t x)) ≠ 0) : κ ≠ 0 := by
  intro hκ
  obtain ⟨n, hn, hpow⟩ := h.1 t

  have hz : D.what₂.embLL (ze t) ≠ 0 := by
    intro hz0
    have e1 := congrArg D.what₂.embLL hpow
    rw [map_pow, map_one, hz0, zero_pow hn.ne'] at e1
    exact zero_ne_one e1

  have e := h.2 t x hx a
  rw [hκ, zero_mul] at e
  exact mul_ne_zero (mul_ne_zero hz hc) h0 e

theorem Big.and {Q Q' : ChP} (h : Big Q) (h' : Big Q') : Big fun ch => Q ch ∧ Q' ch := by
  unfold Big at h h' ⊢
  obtain ⟨C₁, h₁⟩ := h
  obtain ⟨C₂, h₂⟩ := h'

  refine ⟨max C₁ C₂, fun ε CF hCF => ?_⟩
  obtain ⟨y₁, k₁⟩ := h₁ ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨y₂, k₂⟩ := h₂ ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max y₁ y₂, ?_⟩
  intro D large₂ hε hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc
  exact ⟨k₁ D large₂ hε (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc,
    k₂ D large₂ hε (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS ch hch hsc⟩

end GlobalTheory.RowClaim

end
