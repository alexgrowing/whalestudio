import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolPinAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundX
import Formalism.SharpRestriction.CuspSpanNormBounds.OscillatoryIntegralBounds

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.NGCut.SplitEmbedding

namespace Formalism.L2.SG.NGCut.StabilizerCovolume

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def ht {D : D7} {w : Point D.host.E (D.R.rS + 1)} (p : Formalism.L2.SG.RealObj.FreeE w) : ℕ := p.1.2.val - p.1.1.val

def ChartC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∃ BX : Formalism.L2.SG.RealObj.FreeE w → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → (Formalism.L2.SG.RealObj.FreeE w → ℂ) → ℂ,
        (∀ p, Measurable (fun z : (Formalism.L2.SG.RealObj.FreeE w → ℂ) × (Formalism.L2.SG.RealObj.FreeE w → ℂ) => BX p z.1 z.2)) ∧
        (∀ p (x x' y y' : Formalism.L2.SG.RealObj.FreeE w → ℂ), (∀ q, ht q < ht p → x q = x' q ∧ y q = y' q) →
          BX p x y = BX p x' y') ∧
        (∀ p (x : Formalism.L2.SG.RealObj.FreeE w → ℂ), BX p x 0 = 0) ∧
        Measurable (Formalism.L2.SG.RealObj.stCoord X u' w γw) ∧
        MeasurableSet (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        Set.InjOn (Formalism.L2.SG.RealObj.stCoord X u' w γw) (Formalism.L2.SG.RealObj.StInf X u u' γw) ∧
        (∀ x, ∃ z ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, Formalism.L2.SG.RealObj.stCoord X u' w γw z = x) ∧
        (∀ z₁ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw, ∀ z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw,
          z₁ * z₂ ∈ Formalism.L2.SG.RealObj.StInf X u u' γw ∧
          Formalism.L2.SG.RealObj.stCoord X u' w γw (z₁ * z₂) =
            lawX BX (Formalism.L2.SG.RealObj.stCoord X u' w γw z₁) (Formalism.L2.SG.RealObj.stCoord X u' w γw z₂)) ∧
        (∀ r ∈ Formalism.L2.SG.TermOp.Vanish.Rset t, s⁻¹ * r * s ∈ Formalism.L2.SG.RealObj.StInf X u u' γw)

def LatC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) (t : TT Y u u'), t.relevant → t.G ≠ 0 →
    ∀ w, t.toTerm.atPt w → ∀ (F' : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (L U : Formalism.L2.SG.PairVal.MatR D),
      Formalism.L2.SG.PairVal.NormRep t.toTerm w F' L U → ∀ (γw s s' : X.B.I.Ginf),
      Formalism.L2.SG.RealObj.IsPtRep X u u' w γw → s ∈ X.SinfU u → s' ∈ X.SinfU u' → t.pt.1 = s * γw * s'⁻¹ →
      ∀ (c : X.B.I.Ginf) (Φ : Formalism.L2.SG.Pf.VolPinAsm.StG w →* X.B.I.Ginf),
        Formalism.L2.SG.Pf.VolPinAsm.DictProps t w F' L γw s c Φ →
      ∃ (σ : Formalism.L2.SG.RealObj.FreeE w → ℂ) (h' : Formalism.L2.SG.RealObj.FreeE w → ℕ) (I : Formalism.L2.SG.RealObj.FreeE w → (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)ˣ)
        (Λ : Formalism.L2.SG.RealObj.FreeE w → AddSubgroup D.host.E) (k : Formalism.L2.SG.RealObj.FreeE w → ℕ)
        (τ : Formalism.L2.SG.RealObj.FreeE w → (InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ) → (InfinitePlace X.B.I.F → ℂ))
        (σι : InfinitePlace X.B.I.F ≃ {w : InfinitePlace D.host.E // w.IsComplex}),
        (∀ p q, ht q < ht p → h' q < h' p) ∧
        (∀ v, Formalism.L2.SG.Pf.VolPinAsm.phiV X v = (σι v).1.embedding ∨
          Formalism.L2.SG.Pf.VolPinAsm.phiV X v = ComplexEmbedding.conjugate (σι v).1.embedding) ∧
        (∀ p, ∀ a ∈ Λ p, a ∈ (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ∧
        (∀ p, (Λ p).relIndex
          (((I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : Submodule (𝓞 D.host.E) D.host.E).toAddSubgroup) = k p) ∧
        (∀ p, k p ≠ 0) ∧ (∀ p, σ p ≠ 0) ∧
        (∀ p (x x' : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ),
          (∀ q, h' q < h' p → ∀ v, x v q = x' v q) → τ p x = τ p x') ∧
        (∀ x : InfinitePlace X.B.I.F → Formalism.L2.SG.RealObj.FreeE w → ℂ,
          (∃ β : Formalism.L2.SG.Pf.VolPinAsm.StG w, (β : Formalism.L2.SG.PairVal.GLR D) ∈ Formalism.L2.SG.PairVal.stabInt D u u' Y.δ Y.M w ∧
            x = Formalism.L2.SG.RealObj.stCoord X u' w γw (s⁻¹ * (c⁻¹ * Φ β * c) * s)) ↔
          ∀ p, (fun v => x v p) - τ p x ∈ (Λ p).map (embS (Formalism.L2.SG.Pf.VolPinAsm.phiV X) (σ p))) ∧
        0 ≤ D.host.ka / (X.B.g : ℝ) / Real.pi ∧
        ∏ p, ((D.host.ka / (X.B.g : ℝ) / Real.pi) ^ Fintype.card (InfinitePlace X.B.I.F) * k p *
          (FractionalIdeal.absNorm (I p : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) : ℝ) *
          2⁻¹ ^ Fintype.card (InfinitePlace X.B.I.F) * √|(discr D.host.E : ℝ)| *
          ‖σ p‖ ^ (2 * Fintype.card (InfinitePlace X.B.I.F))) = 1

end Formalism.L2.SG.NGCut.StabilizerCovolume
