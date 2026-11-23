import Mathlib
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTieSat
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ContentZeroAtSmallPrimes
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
import Formalism.DropLevelBounds.ThBounds

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunDepth

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree

variable {D : D7}

def plOf (D : D7) (z : RPl D.R) : D.what₂.Tau :=
  D.eTau.symm (if z.1 then ⟨D.R.tau2 z.2, rfl⟩ else ⟨D.R.tau1 z.2, rfl⟩)

def numOf (D : D7) (L : SizeData₂ D) : NumDatum where
  R := D.R
  sc := L.sc
  H := D.host.toHostAx
  g := D.host.g
  g_prime := D.host.g_prime
  TT := D.host.TT
  Del := ⌊(D.s.Del : ℝ)⌋₊
  h0 := ⌊LevelStarExponents.h0 L⌋₊
  hc := fun z => D.hc (plOf D z)

def vdOf (D : D7) (p : ℕ) : ℝ := if p ∈ D.host.small then (padicValNat p D.host.QS : ℝ) else 1 / 2

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem TO_pos (Tp : ParamsT D L Pm) : 0 < Tp.TO := lt_of_lt_of_le (by omega) Tp.TO_40

def depOf (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) : DepData D.host.E :=
  depRun T EX ⟨Tp.TO, TO_pos Tp⟩ (vdOf D) (lR Tp hK) (fR Tp hK) (kaR Tp hK)

structure RunTie (T : Core D) (EX : ErrX D) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) [StarRing (𝓞 D.host.E)]
    {K : Type} [Field K] [NumberField K] [StarRing K] [Algebra (𝓞 T.Q.c.F) (𝓞 K)]
    [Algebra.IsIntegral (𝓞 T.Q.c.F) (𝓞 K)] [Algebra (𝓞 D.host.E) K]
    {Bs : DefBase K} {Df : DefSide Bs} {S : IndefData Df} {P : Type} [Group P] [Finite P] {oc : OnConst}
    (O : OnObj S P oc) (ι : Bs.J → ℕ) : Prop where
  inR : ∀ j, InR D (ι j)
  star_eq : ∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a
  conj : ∀ a : 𝓞 D.host.E, star (algebraMap (𝓞 D.host.E) K a) = algebraMap (𝓞 D.host.E) K (T.Q.H.bar a)
  E_eq : ∀ v j, O.E v j = EAt (Xo := T.Q.Xo (ι j)) (c := T.Q.c) (LL := K) (depOf T EX Tp hK) v (ι j)
  σ_eq : ∀ v j, O.σ v j = sigAt (Dw := T.Q.Dw (ι j)) (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
  nn_eq : ∀ j, O.nnK j = nnKAt (H := T.Q.H) (LL := K) (depOf T EX Tp hK) (ι j)
  T_eq : O.T = (Tp.TO : ℝ)
  jets_eq_fact : O.g1 = D.host.g 0
  g2_eq : O.g2 = D.host.g 1
  cmQuadraticForm_eq_alternatingForm : O.q1 = D.host.q
  dd_eq : O.dd = D.host.d
  sm_eq : O.sm = D.host.small
  k_eq : O.k = (D.R.k : ℝ)
  m_eq : O.m = (D.R.m : ℝ)
  f_eq : O.f = (D.R.f : ℝ)
  x_eq : O.x = L.sc.x
  eps_eq : O.eps = L.sc.eps
  Sc_eq : O.Sc = L.Sc
  eta_eq : O.eta = L.etaSz
  bp_eq : O.bp = L.sc.b'
  depthNumbers_threshold_eq : O.X2 = L.sc.X'' D.R.n
  vd_eq : O.vd = vd2 D
  wt_eq : ∀ j, O.wt j = 2 * (D.R.f : ℝ) * L.sc.b
  th_eq : ∀ l, O.th l = Formalism.UnitaryBoundIntegral.thl D.R.k l
  ad_eq : ∀ l, O.ad l = 0
  DF_ge : ∀ j, (WeightAlgebra.DF (lR Tp hK (ι j)) : ℝ) ≤ O.DF

end GlobalTheory.RunDepth
