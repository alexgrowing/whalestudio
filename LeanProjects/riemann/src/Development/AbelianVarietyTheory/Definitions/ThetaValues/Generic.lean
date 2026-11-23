import Mathlib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpolationModelInequalities
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf

noncomputable section

namespace GlobalTheory.Shares

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps

section Abstract

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

structure Rdg (X : PJ D B P j) where
  Y : Type
  σ : B.KO →+* ℂ
  ev : X.Forms →+* (Y → ℂ)
  ev_smul : ∀ (a : B.KO) (F : X.Forms), ev (a • F) = σ a • ev F
  indep : ∀ (u : WeightFamilies.Wt D j) (m : ℕ) (F : Fin m → B.Cusp j u), LinearIndependent B.KO F →
    LinearIndependent ℂ fun i => ev (X.inc u (F i))

variable {X : PJ D B P j} (R : Rdg X)

def Rdg.sp (u : WeightFamilies.Wt D j) (s : Set (B.Cusp j u)) : Submodule ℂ (R.Y → ℂ) :=
  Submodule.span ℂ ((fun F => R.ev (X.inc u F)) '' s)

def Rdg.Generic {ι : Type} (t : ι → ℂ) : Prop :=
  ∀ Q : MvPolynomial ι B.KO, Q ≠ 0 → MvPolynomial.eval₂ R.σ t Q ≠ 0

def toRp (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) :
    MvPolynomial (Idx D j N) X.Forms →+* Rp X la N :=
  MvPolynomial.eval₂Hom (emb X la N) fun p => algebraMap (Op X la N) (Rp X la N) (Tv X la N p)

def Rdg.toFn {N : ℕ} (t : Idx D j N → ℂ) : MvPolynomial (Idx D j N) X.Forms →+* (R.Y → ℂ) :=
  MvPolynomial.eval₂Hom R.ev fun p _ => t p

def OfWt (X : PJ D B P j) {ι : Type} (u : WeightFamilies.Wt D j) (p : MvPolynomial ι X.Forms) : Prop :=
  ∀ m, p.coeff m ∈ LinearMap.range (X.inc u)

variable {N : ℕ} {wL : WeightFamilies.Wt D j}

def Rdg.s (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ) (i : Fin (WeightFamilies.dimY D j + 1)) : R.Y → ℂ :=
  ∑ k, t (i, k) • R.ev (X.inc wL (w k))

def Rdg.mon (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ) (α : Fin (WeightFamilies.dimY D j) → ℕ) : R.Y → ℂ :=
  ∏ i, R.s w t i.succ ^ α i

def Rdg.deep (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ) (u : WeightFamilies.Wt D j) (a : ℕ) : Submodule ℂ (R.Y → ℂ) :=
  Submodule.span ℂ {g | ∃ (α : Fin (WeightFamilies.dimY D j) → ℕ) (f : R.Y → ℂ), ∑ i, α i = a ∧ f ∈ R.sp u Set.univ ∧
    g = R.mon w t α * f}

def Rdg.lead (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ) (T a : ℕ) {n : ℕ} (θ : Fin n → R.Y → ℂ)
    (p : {α : Fin (WeightFamilies.dimY D j) → ℕ // ∑ i, α i < a} × Fin n) : R.Y → ℂ :=
  R.mon w t p.1.1 * R.s w t 0 ^ (T - ∑ i, p.1.1 i) * θ p.2

def vals {Y : Type} {δ n : ℕ} (xs : Fin δ → Y) (θ : Fin n → Y → ℂ) : Fin n → Fin δ → ℂ := fun i q => θ i (xs q)

structure AnFacts (w : Fin N → B.Cusp j wL) (t : Idx D j N → ℂ) (ka wF : WeightFamilies.Wt D j) (T : ℕ)
    (Mg : Submodule B.KO (B.Cusp j ka)) {δ : ℕ} (xs : Fin δ → R.Y) : Prop where
  zero : ∀ q, R.s w t 0 (xs q) ≠ 0 ∧ ∀ i : Fin (WeightFamilies.dimY D j), R.s w t i.succ (xs q) = 0
  interp : ∀ v : Fin δ → ℂ, ∃ f ∈ R.sp wF Set.univ, ∀ q, f (xs q) = v q
  vandiv : ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) →
    ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1
  indep : ∀ (n : ℕ) (θ : Fin n → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → LinearIndependent ℂ (vals xs θ) →
    LinearIndependent ℂ (R.lead w t T (a0 D j T) θ) ∧
      Disjoint (Submodule.span ℂ (Set.range (R.lead w t T (a0 D j T) θ))) (R.deep w t (X.wF0 wL wF) (a0 D j T))
  upper : Module.finrank ℂ (R.sp ka Set.univ) ≤ δ * (T + 2 * WeightFamilies.dimY D j + 6).choose (WeightFamilies.dimY D j)
  lower : δ * (T + WeightFamilies.dimY D j).choose (WeightFamilies.dimY D j) ≤ Module.finrank ℂ (R.sp ka Mg)
  contain : ∀ (n : ℕ) (θ : Fin n → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) →
    Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ →
    R.sp ka Mg ≤ Submodule.span ℂ (Set.range (R.lead w t T (a0 D j T) θ)) ⊔ R.deep w t (X.wF0 wL wF) (a0 D j T)

end Abstract

section Model

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {K : Type} [Field K]

def HomRel (σ : K →+* ℂ) (X : Data E r) {n : ℕ} (u : Fin n → Frame X.Ψ r → ℂ) : Prop :=
  ∃ (Q : MvPolynomial (Fin n) K) (d : ℕ), Q ≠ 0 ∧ Q.IsHomogeneous d ∧
    ∀ x ∈ X.dom, MvPolynomial.eval₂ σ (fun i => u i x) Q = 0

def RelIn (σ : K →+* ℂ) (X : Data E r) (Xa : ArchInM X) : Prop :=
  (∀ jj : Fin (nd X + 2) → Fin Xa.N, HomRel σ X fun a => Xa.w (jj a)) ∧
  ∀ jj : Fin (nd X + 1) → Fin Xa.N, HomRel σ X
    (Fin.cons (fun x => Xa.et x * Xa.th1 x ^ (Xa.i * (Xa.g0 / 2))) fun a x => Xa.w (jj a) x ^ (2 * (Xa.i * (Xa.g0 / 2))) :
      Fin (nd X + 2) → Frame X.Ψ r → ℂ)

def Margins (X : Data E r) (Xa : ArchInM X) : Prop :=
  (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧ bb < m ∧
    ∀ τ ∈ ({0, 1 + Xa.c1 / Xa.a1} : Set ℝ), ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ + τ * leviO X x0 Xa.ps0 z ξ) ∧
  (∃ bb m : ℝ, 4 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb ∧
    bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m ∧
    ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ) ∧
  (∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ, 0 ≤ leviO X x0 (phla X Xa.L) z ξ) ∧
  (∃ C : ℝ, ∀ x ∈ X.dom, Xa.ps0 x ≤ C) ∧
  ∀ (k : ℕ) P, X.IsBddSec (Xa.Fp + k • Xa.L) P → P ∈ X.SS (Xa.Fp + k • Xa.L)

end Model

section Record

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ)

abbrev laR (T : Top D) (j : ℕ) (u : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp) : Wt ((T.U j T.σ₀).X k).Ψ D.R.r :=
  laU (T.U j T.σ₀) (wtA u) u.n k

def OntoBy (u : WeightFamilies.Wt D j) (A : ∀ k : (T.U j T.σ₀).Comp, Set (Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ))
    (s : Set ((recB h.toLawsCore).Cusp j u)) : Prop :=
  ∀ f : ∀ k : (T.U j T.σ₀).Comp, Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ, (∀ k, f k ∈ A k) →
    ∃ (m : ℕ) (a : Fin m → ℂ) (F : Fin m → (recB h.toLawsCore).Cusp j u), (∀ i, F i ∈ s) ∧
      ∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f k x = ∑ i, a i * rdR h j (F i) k x

def RdOnto (u : WeightFamilies.Wt D j) : Prop :=
  OntoBy h j u (fun k => ((T.U j T.σ₀).X k).SS (laR T j u k)) Set.univ

def MggOnto (CR Tt c : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  OntoBy h j ka (fun k => ((T.U j T.σ₀).X k).SSgt (laR T j ka k) (WeightFamilies.c1 D CR Tt c j))
    (WeightFamilies.MggK (recB h.toLawsCore) CR Tt c j ka)

structure ArchAt {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → (recB h.toLawsCore).Cusp j wL) (wF : WeightFamilies.Wt D j) (Tn : ℕ)
    (c1 : ℝ) where
  Xa : ∀ k : (T.U j T.σ₀).Comp, ArchInM ((T.U j T.σ₀).X k)
  dim : ∀ k, nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j
  hN : ∀ k, (Xa k).N = N
  hL : ∀ k, (Xa k).L = laR T j wL k
  hF : ∀ k, (Xa k).Fp = laR T j wF k
  hT : ∀ k, (Xa k).T = Tn
  hc : ∀ k, (Xa k).c1 = c1
  hw : ∀ k i, (Xa k).w i = rdR h j (w (Fin.cast (hN k) i)) k
  rel : ∀ k, RelIn T.σ₀ ((T.U j T.σ₀).X k) (Xa k)
  mar : ∀ k, Margins ((T.U j T.σ₀).X k) (Xa k)

structure FlatAt {N : ℕ} {wL wF : WeightFamilies.Wt D j} {w : Fin N → (recB h.toLawsCore).Cusp j wL} {Tn : ℕ} {c1 : ℝ}
    (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) where
  Fl : ∀ k, FlatM ((T.U j T.σ₀).X k) (A.Xa k)
  h0 : ∀ k x, (Fl k).w0 x = ∑ i, t (0, i) * rdR h j (w i) k x
  hs : ∀ k a x, (Fl k).s a x = ∑ i, t ((Fin.cast (A.dim k) a).succ, i) * rdR h j (w i) k x

abbrev DomPt (T : Top D) (j : ℕ) : Type := Σ k : (T.U j T.σ₀).Comp, ((T.U j T.σ₀).X k).dom

def IsRdgU (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j) : Prop :=
  (∀ a : T.Q.c.F, R.σ a = T.σ₀ a) ∧
    ∀ (u : WeightFamilies.Wt D j) (F : (recB h.toLawsCore).Cusp j u) (y : R.Y),
      R.ev ((recPlusN h j hj n).inc u F) y = rdR h j F (e y).1 (e y).2.1

end Record

end GlobalTheory.Shares
