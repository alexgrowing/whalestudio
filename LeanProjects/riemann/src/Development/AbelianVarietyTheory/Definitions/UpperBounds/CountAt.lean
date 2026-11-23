import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic

noncomputable section

namespace GlobalTheory.UpTie

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def domSpan (X : Data E r) (A : Set (Frame X.Ψ r → ℂ)) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  Submodule.span ℂ ((fun f => X.dom.indicator f) '' A)

def deepM (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Submodule ℂ (Frame X.Ψ r → ℂ) :=
  domSpan X {P | ∃ (α : Fin (nd X) → ℕ) (g : Frame X.Ψ r → ℂ), ∑ i, α i = Xa.T - nd X ∧
    g ∈ X.SS (Xa.Fp + nd X • Xa.L) ∧ P = fun x => monoM X Fl.s α x * g x}

def JetInj (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) : Prop :=
  ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L), VanS X Fl.xs Fl.s (Xa.T + nd X + 7) f → ∀ x ∈ X.dom, f x = 0

end Model

section Record

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def SpanTh (h : LawsP T) (j : ℕ) (hj : InR D j) (S : Scal (recB h.toLawsCore)) (u : WeightFamilies.Wt D j) : Prop :=
  ∀ P : ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ,
    (∀ k, P k ∈ ((T.U j T.σ₀).X k).SS (laU (T.U j T.σ₀) (wtA u) u.n k)) →
    (∀ k, ∀ x ∉ ((T.U j T.σ₀).X k).dom, P k x = 0) →
    P ∈ Submodule.span ℂ ((fun F => (fun k => rdR h j F k : ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) ''
      ((recPlus h j hj).Thc S.s0 u : Set ((recB h.toLawsCore).Cusp j u)))

def Vc (h : LawsP T) (j : ℕ) (u : WeightFamilies.Wt D j) : Submodule ℂ (∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  Submodule.span ℂ (Set.range fun F : (recB h.toLawsCore).Cusp j u =>
    (fun k => rdR h j F k : ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ))

def Wc (h : LawsP T) (j : ℕ) (u : WeightFamilies.Wt D j) (c1 : ℝ) :
    Submodule ℂ (∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  Submodule.span ℂ {P | P ∈ Vc h j u ∧ ∀ k, P k ∈ ((T.U j T.σ₀).X k).SSgt (laU (T.U j T.σ₀) (wtA u) u.n k) c1}

def DescSt (h : LawsP T) (j : ℕ) (CR : ℝ) (TT : ℕ) (c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  Wc h j ka (WeightFamilies.c1 D CR TT c j) ≤ Submodule.span ℂ ((fun F : (recB h.toLawsCore).Cusp j ka =>
    (fun k => rdR h j F k : ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ)) ''
    (WeightFamilies.MggK (recB h.toLawsCore) CR TT c j ka : Set ((recB h.toLawsCore).Cusp j ka)))

def mono (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (io : KT T j G.N →+* ℂ) (α : Fin (WeightFamilies.dimY D j) → ℕ) (e : ℕ) (k : (T.U j T.σ₀).Comp)
    (x : Frame ((T.U j T.σ₀).X k).Ψ D.R.r) : ℂ :=
  (∏ i, rdSec h j hj G io i.succ k x ^ α i) * rdSec h j hj G io 0 k x ^ e

structure Gen (h : LawsP T) (j : ℕ) where
  u : WeightFamilies.Wt D j
  α : Fin (WeightFamilies.dimY D j) → ℕ
  e : ℕ
  θ : (recB h.toLawsCore).Cusp j u

def Gen.OfWt {h : LawsP T} {j : ℕ} (g : Gen h j) (wL ka : WeightFamilies.Wt D j) : Prop :=
  addL g.u wL (∑ i, g.α i + g.e) = ka

def rp (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g : Gen h j) :
    Rp (recPlus h j hj) la G.N :=
  secPow (recPlus h j hj) la G.w g.α * sec (recPlus h j hj) la G.w 0 ^ g.e *
    emb (recPlus h j hj) la G.N ((recPlus h j hj).inc g.u g.θ)

def rd (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (io : KT T j G.N →+* ℂ) (g : Gen h j) :
    ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ :=
  fun k x => mono h j hj G io g.α g.e k x * rdR h j g.θ k x

def RpDesc (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (u₀ : WeightFamilies.Wt D j) : Prop :=
  ∀ (m : ℕ) (gs : Fin m → Gen h j) (g0 : Gen h j) (io : KT T j G.N →+* ℂ), IsIoExt j io →
    (∀ i, (gs i).OfWt wL u₀) → g0.OfWt wL u₀ →
    (∃ c : Fin m → ℂ, ∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom,
      rd h j hj G io g0 k x = ∑ i, c i * rd h j hj G io (gs i) k x) →
    rp h j hj G la g0 ∈ Submodule.span (Kp (recPlus h j hj) la G.N) (Set.range (rp h j hj G la ∘ gs))

def RpRank (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (u₀ : WeightFamilies.Wt D j) : Prop :=
  ∀ (m : ℕ) (gs : Fin m → Gen h j) (io : KT T j G.N →+* ℂ), IsIoExt j io → (∀ i, (gs i).OfWt wL u₀) →
    Module.finrank (Kp (recPlus h j hj) la G.N)
        (Submodule.span (Kp (recPlus h j hj) la G.N) (Set.range (rp h j hj G la ∘ gs))) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range (rd h j hj G io ∘ gs)))

def Zc (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (io : KT T j G.N →+* ℂ) (S : Scal (recB h.toLawsCore)) (TT : ℕ) :
    Submodule ℂ (∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ) :=
  Submodule.span ℂ {P : ∀ k, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ |
      ∃ (α : Fin (WeightFamilies.dimY D j) → ℕ) (θ : (recB h.toLawsCore).Cusp j ((recPlus h j hj).wF0 wL wF)),
        ∑ i, α i = a0 D j TT ∧ θ ∈ (recPlus h j hj).Thc S.s0 ((recPlus h j hj).wF0 wL wF) ∧
        P = fun k x => mono h j hj G io α 0 k x * rdR h j θ k x}

def CountAt (h : LawsP T) (j : ℕ) (hj : InR D j) {ka wL wF : WeightFamilies.Wt D j}
    (G : GlobalFamilyData (recPlus h j hj) ka wL wF) (io : KT T j G.N →+* ℂ) (S : Scal (recB h.toLawsCore)) (TT d : ℕ) : Prop :=
  (Module.finrank ℂ (Zc h j hj G io S TT) : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / TT

def CountP (h : LawsP T) (j : ℕ) (ka : WeightFamilies.Wt D j) (c1 : ℝ) (TT d : ℕ) : Prop :=
  (Module.finrank ℂ (Vc h j ka) : ℝ) - Module.finrank ℂ (Wc h j ka c1) ≤
    (WeightFamilies.dimY D j : ℝ) * (WeightFamilies.dimY D j + 6) * d / TT

end Record

end GlobalTheory.UpTie
