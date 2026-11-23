import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXLeb
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundT

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.MainNotions.S

attribute [local instance] Formalism.BasicNotions.Host.cmStar

abbrev CBlk (r : ℕ) : Type := (LsNc5.LtPair r ⊕ Fin r) ⊕ (LsNc5.LtPair r ⊕ Fin r)

def CSpc (ι : Type) (k : ℕ) {r : ℕ} : CBlk r → Type
  | Sum.inl (Sum.inl _) => ι → ℂ
  | Sum.inl (Sum.inr _) => ι → Fin (k + 1) → ℂ
  | Sum.inr (Sum.inl _) => ι → ℂ
  | Sum.inr (Sum.inr _) => ι → ℝ

section Inst

variable (ι : Type) [Fintype ι] (k : ℕ) {r : ℕ}

instance instAddCommGroupCSpc : ∀ p : CBlk r, AddCommGroup (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (AddCommGroup (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (AddCommGroup (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (AddCommGroup (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (AddCommGroup (ι → ℝ))

instance instMeasurableSpaceCSpc : ∀ p : CBlk r, MeasurableSpace (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (MeasurableSpace (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (MeasurableSpace (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (MeasurableSpace (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (MeasurableSpace (ι → ℝ))

instance instMeasurableAdd₂CSpc : ∀ p : CBlk r, MeasurableAdd₂ (CSpc ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (MeasurableAdd₂ (ι → ℂ))
  | Sum.inl (Sum.inr _) => inferInstanceAs (MeasurableAdd₂ (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => inferInstanceAs (MeasurableAdd₂ (ι → ℂ))
  | Sum.inr (Sum.inr _) => inferInstanceAs (MeasurableAdd₂ (ι → ℝ))

def cMeas : ∀ p : CBlk r, Measure (CSpc ι k p)
  | Sum.inl (Sum.inl _) => (volume : Measure (ι → ℂ))
  | Sum.inl (Sum.inr _) => (volume : Measure (ι → Fin (k + 1) → ℂ))
  | Sum.inr (Sum.inl _) => (volume : Measure (ι → ℂ))
  | Sum.inr (Sum.inr _) => (volume : Measure (ι → ℝ))

instance instSigmaFiniteCMeas : ∀ p : CBlk r, SigmaFinite (cMeas ι k p)
  | Sum.inl (Sum.inl _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℂ)))
  | Sum.inl (Sum.inr _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → Fin (k + 1) → ℂ)))
  | Sum.inr (Sum.inl _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℂ)))
  | Sum.inr (Sum.inr _) => inferInstanceAs (SigmaFinite (volume : Measure (ι → ℝ)))

instance instRightInvCMeas : ∀ p : CBlk r, (cMeas ι k p).IsAddRightInvariant
  | Sum.inl (Sum.inl _) => inferInstanceAs ((volume : Measure (ι → ℂ)).IsAddRightInvariant)
  | Sum.inl (Sum.inr _) => inferInstanceAs ((volume : Measure (ι → Fin (k + 1) → ℂ)).IsAddRightInvariant)
  | Sum.inr (Sum.inl _) => inferInstanceAs ((volume : Measure (ι → ℂ)).IsAddRightInvariant)
  | Sum.inr (Sum.inr _) => inferInstanceAs ((volume : Measure (ι → ℝ)).IsAddRightInvariant)

end Inst

def cHgt {r : ℕ} : CBlk r → ℕ
  | Sum.inl (Sum.inl p) => p.1.2.val - p.1.1.val
  | Sum.inl (Sum.inr b) => r + (r - b.val)
  | Sum.inr (Sum.inl p) => 2 * r + 1 + (2 * r - (p.1.1.val + p.1.2.val))
  | Sum.inr (Sum.inr a) => 2 * r + 1 + (2 * r - 2 * a.val)

section HidaSetting

variable {D : D7} (X : HidaSetting D)

def blk (u : D.what₂.Word) (s : X.B.I.Ginf) :
    ∀ p : CBlk D.R.rS, CSpc (InfinitePlace X.B.I.F) D.R.k p
  | Sum.inl (Sum.inl p) => fun v => LsNc5.xMat X v s p.1.1 p.1.2
  | Sum.inl (Sum.inr b) => fun v j =>
      if h : j.val < D.R.k then LsNc5.phiMat X u v s b ⟨j.val, h⟩ else LsNc5.yVec X u v s b
  | Sum.inr (Sum.inl p) => fun v => (LsNc5.mMat X v s p.1.1 p.1.2 - star (LsNc5.mMat X v s p.1.2 p.1.1)) / 2
  | Sum.inr (Sum.inr a) => fun v => (LsNc5.mMat X v s a a).im

def embV (t : D.host.E) : InfinitePlace X.B.I.F → ℂ := fun v => embS D (X.pl v) t

def rowV (u : D.what₂.Word) (x : (VS D).V) : InfinitePlace X.B.I.F → Fin (D.R.k + 1) → ℂ := fun v j =>
  if h : j.val < D.R.k then hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (X.wfr u v ⟨j.val, h⟩)
  else hJ (X.B.I.ε v) (rv X.B.I v (X.crd x)) (rv X.B.I v (X.zR u))

def aaLb (b : Fin D.R.rS) : Set (VS D).V :=
  (Submodule.span (𝓞 D.host.E) {y | ∃ c ∈ (aaD D b : Set D.host.E), ∃ l ∈ X.Lb, y = c • l} : Set (VS D).V)

def cLat (u : D.what₂.Word) : ∀ p : CBlk D.R.rS, AddSubgroup (CSpc (InfinitePlace X.B.I.F) D.R.k p)
  | Sum.inl (Sum.inl p) => AddSubgroup.closure (embV X '' ((aaD D p.1.1 * (aaD D p.1.2)⁻¹ :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))
  | Sum.inl (Sum.inr b) => AddSubgroup.closure (rowV X u '' aaLb X b)
  | Sum.inr (Sum.inl p) => AddSubgroup.closure (embV X '' ((aaD D p.1.1 * aaD D p.1.2 :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E))
  | Sum.inr (Sum.inr a) => AddSubgroup.closure ((fun t v => (embS D (X.pl v) t).im) ''
      {t | t ∈ ((aaD D a * aaD D a : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Set D.host.E) ∧
        D.host.conj t = -t})

def cVal (u : D.what₂.Word) : CBlk D.R.rS → ℝ
  | Sum.inl (Sum.inl p) => (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((p.1.2 : ℕ) - (p.1.1 : ℕ) : ℝ))
  | Sum.inl (Sum.inr b) => Tw u ^ Fintype.card (InfinitePlace X.B.I.F) *
      (2 : ℝ)⁻¹ ^ (Fintype.card (InfinitePlace X.B.I.F) * (D.R.k + 1)) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ (((D.R.k : ℝ) + 1) * (1 - 2 * ((D.R.rS : ℝ) - (b : ℕ))))
  | Sum.inr (Sum.inl p) => (2 : ℝ)⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) *
      |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 : ℝ) - 2 * ((D.R.rS : ℝ) - (p.1.1 : ℕ)) - 2 * ((D.R.rS : ℝ) - (p.1.2 : ℕ)))
  | Sum.inr (Sum.inr a) => |(NumberField.discr X.B.I.F : ℝ)| ^ ((1 / 2 : ℝ) - 2 * ((D.R.rS : ℝ) - (a : ℕ)))

end HidaSetting

def KapLaw : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∃ B : ∀ p : CBlk D.R.rS,
      (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) →
        CSpc (InfinitePlace X.B.I.F) D.R.k p,
    (∀ p, Measurable (fun z : (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) ×
      (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) => B p z.1 z.2)) ∧
    (∀ p (x x' y y' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q),
      (∀ q, cHgt q < cHgt p → x q = x' q ∧ y q = y' q) → B p x y = B p x' y') ∧
    (∀ p (x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), B p x 0 = 0) ∧
    ∀ s ∈ X.NinfU u, ∀ s' ∈ X.NinfU u, blk X u (s * s') = Formalism.L2.SG.NGCut.SplitEmbedding.mlaw B (blk X u s) (blk X u s')

def KapSurj : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word), ∃ σ : (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → X.B.I.Ginf,
    Measurable σ ∧ ∀ t, σ t ∈ X.NinfU u ∧ blk X u (σ t) = t

def NOfib : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ⊆ X.NinfU u ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, ∀ δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u,
      δ * δ' ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    (∀ δ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u, δ⁻¹ ∈ Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) ∧
    ∃ τ : ∀ p : CBlk D.R.rS, (∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q) → CSpc (InfinitePlace X.B.I.F) D.R.k p,
      (∀ p (x x' : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q), (∀ q, cHgt q < cHgt p → x q = x' q) → τ p x = τ p x') ∧
      ∀ x : ∀ q, CSpc (InfinitePlace X.B.I.F) D.R.k q,
        x ∈ blk X u '' Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u ↔ ∀ p, x p - τ p x ∈ cLat X u p

def BlockCovol : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (p : CBlk D.R.rS),
    Countable (cLat X u p) ∧
    (∃ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F ∧
      ∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F) ∧
    ∀ F : Set (CSpc (InfinitePlace X.B.I.F) D.R.k p), MeasurableSet F →
      (∀ v, ∃! a : cLat X u p, (a : CSpc (InfinitePlace X.B.I.F) D.R.k p) + v ∈ F) →
        cMeas (InfinitePlace X.B.I.F) D.R.k p F = ENNReal.ofReal (cVal X u p)

end Formalism.L2.SG.Pf.NcReal.JX
