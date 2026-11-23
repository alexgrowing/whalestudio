import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.ExistsSecTieFOfTies
import Development.AbelianVarietyTheory.Definitions.ThetaValues.IsBlockProd
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.CombBound4Of
import Formalism.LocalToGlobal.ProjectiveLattices.SupNDataOfNonneg
import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.RegXInst

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RunJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7}

structure ParOK (T : Top D) (EX : ErrX D) (p j : ℕ) : Prop where
  sh : LawsSh T
  lvA : ∀ j, InR D j → ∀ n, (T.dδ j n).l₂.A = 1
  same : ∀ j, InR D j → ∀ k k', ((T.U j T.σ₀).X k).Gm = ((T.U j T.σ₀).X k').Gm ∧
    ((T.U j T.σ₀).X k).ξ0 = ((T.U j T.σ₀).X k').ξ0
  bad : 0 < badN D
  own : ∀ n, (T.dδ j n).pd = p
  orient : GlobalTheory.PtTie.Oriented T EX
  alg : FnAlgClosed (T.Q.Xo j) T.Q.c

section Abstract

variable {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

structure PageOK (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ)
    (h0 : ℝ) : Prop where
  hyp : FamilyHypotheses.HypPage large₂ X H C2 A2 7 CT ka wL wF Tn nP nW h0
  page : PageAt large₂ C2 A2
  tie : H.C1 = C2 ∧ H.A1 = A2 ∧ H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = 7 ∧ 12 ≤ A2
  p13 : flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2
  frd : (D.R.f : ℝ) ^ 2 ≤ D.host.rdE
  r8 : 8 ≤ D.R.r
  df : 3 ≤ DF wL
  ck : 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f

def gcR (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) : ℝ :=
  max 1 (max (Gc large₂ B (1009 * Zb D large₂) D.host.pde) (Gc large₂ B (1009 * Zb D large₂) D.host.pde'))

theorem growthConstantBound_gcR (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) : GrowthConstantBound large₂ B (gcR large₂ B) := by
  rintro po (rfl | rfl)
  · exact (le_max_left _ _).trans (le_max_right _ _)
  · exact (le_max_right _ _).trans (le_max_right _ _)

def prwR (large₂ : SizeData₂ D) : ℝ := 38 * large₂.sc.L + PO D large₂ + 1

def nbR (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j) : ℝ :=
  Real.log 2 + (D.R.f * D.R.r * w.n : ℕ) * (Real.log (D.host.g 0 * D.host.g 1 : ℕ) + Real.log (1 + DF w)) + PO D large₂

def p14R (w : WeightFamilies.Wt D j) : ℝ := max 1 (GlobalTheory.BlockTh.p14 D.host.E D.R.r w.n D.R.m)

def thR (w : WeightFamilies.Wt D j) : ℝ :=
  I2.th (E := D.host.E) (D.host.g 0 * D.host.g 1) (Real.sqrt (90 * (D.R.f * D.R.r + DF w)))

def lamR (large₂ : SizeData₂ D) (CL : ℝ) (w : WeightFamilies.Wt D j) : ℝ :=
  max 1 (WeightFamilies.PP0v D large₂ CL 2 * (1 + Real.log (8 * ((WeightFamilies.dimY D j : ℝ) + 2) ^ 3 * (2 + PO D large₂)) + 2 * nbR large₂ w +
    1041 * Zb D large₂ ^ 3 + Real.log w.size))

def phR (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (CL : ℝ) (w : WeightFamilies.Wt D j) : ℝ :=
  2 * (lamR large₂ CL w + max 1 (PN D large₂) + p14R w + 200000 * zBase large₂ ^ 2 +
    max 1 (PI4 D j (1009 * Zb D large₂) (81 * Zb D large₂ ^ 2)) + prwR large₂) + gcR large₂ B

def pdR (large₂ : SizeData₂ D) (ka : WeightFamilies.Wt D j) : ℝ := WeightFamilies.PPv D large₂ 1041 3 * (1 + Real.log ka.size)

def kR (CL : ℝ) : KAdm := ⟨1041, 3, 200000, 2, 1, 2, CL, 2, 7⟩

def SharesAt {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G₀ : GlobalFamilyData X ka wL wF) (S : Scal B) (Tn : ℕ) (c : ℝ)
    (Sh : Set (B.Cusp j wF)) : Prop :=
  ∃ (del : ℕ) (th' : Fin del → B.Cusp j wF), (∀ i, th' i ∈ Sh) ∧ ∀ rz alz th0 zc rq th iet et,
    (∀ la, InBasis (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la) ∧
    ShareRd (D := D) (j := j) Tn del (X.rk ka (B.Mlat j ka)) ∧
    ShareRhoR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) S Tn (X.rk ka (B.Mlat j ka)) ∧
    ShareRhoP (D := D) (j := j) Tn (WeightFamilies.rhoP B 7 Tn c j ka) (X.rk ka (B.Mlat j ka)) ∧
    ∀ la, InContainMR (FamilyHypotheses.refill G₀ del th' rz alz th0 zc rq th iet et) la S 7 Tn c

end Abstract

section Record

variable {T : Top D} (h : LawsP T) (j : ℕ)

def LowW {wL : WeightFamilies.Wt D j} {N : ℕ} (w : Fin N → (recB h.toLawsCore).Cusp j wL) (c : ℝ) : Prop :=
  ∀ σ, GoodEmb T.Q.c σ → ∀ (k : (T.U j σ).Comp) (x : FD.Frame ((T.U j σ).X k).Ψ D.R.r), x ∈ ((T.U j σ).X k).dom →
    -Real.log (Real.sqrt (∑ k', recNrm (T.U j σ) (xiR D) (wtA wL) wL.n (w k').1 k x ^ 2)) ≤
      p14R wL * (DF wL : ℝ) + c * I2.phiFD ((T.U j σ).X k) (thR wL) x

def EtaOK (hj : InR D j) (large₂ : SizeData₂ D) (wL : WeightFamilies.Wt D j) (i : ℕ) (et : (recB h.toLawsCore).Cusp j (etWt D j i)) : Prop :=
  0 < i ∧ EtCusp h j hj i et ∧ EtVal h j hj i et ∧ EtSup h j i et (WeightFamilies.PPv D large₂ 200000 2) ∧
    EtArch h (thR wL) (200000 * zBase large₂ ^ 2) j i et ∧ et ∈ (recB h.toLawsCore).Mlat j (etWt D j i)

def GenOK (hj : InR D j) (large₂ : SizeData₂ D) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPJ h j hj) ka wL wF)
    (S : Scal (recB h.toLawsCore)) (c : ℝ) : Prop :=
  G.TiedW S (gcR large₂ (recB h.toLawsCore)) (38 * large₂.sc.L + PO D large₂) ∧ 0 < G.N ∧ Real.log G.N ≤ nbR large₂ wL ∧
    NoCommonZero (T.Q.Xo j) T.Q.c (fun i => (G.w i).1) ∧ LowW h j G.w c

abbrev nusR (w : WeightFamilies.Wt D j) : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ :=
  nusOf (recB h.toLawsCore) w (GlobalTheory.PtTie.nuWt T w)

end Record

def SharesDefSt : Prop :=
  ∀ (D : D7) (T : Top D) (h : LawsP T) (EX : ErrX D) (p : ℕ) (hj : InR D D.R.m) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ)
    (ka wL wF : WeightFamilies.Wt D D.R.m) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore))
    (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ),
    ParOK T EX p D.R.m → PageOK large₂ (recPJ h D.R.m hj) H C2 A2 CT ka wL wF Tn nP nW h0 →
    HypC large₂ (recPJ h D.R.m hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → LatAt (recB h.toLawsCore) D.R.m ka →
    ∀ G₀ : GlobalFamilyData (recPJ h D.R.m hj) ka wL wF, NoCommonZero (T.Q.Xo D.R.m) T.Q.c (fun i => (G₀.w i).1) →
    ∀ Sh : Set ((recB h.toLawsCore).Cusp D.R.m wF), Submodule.span (recB h.toLawsCore).KO Sh = ⊤ →
      SharesAt G₀ S Tn (cc D large₂ C2 A2 7 wL) Sh

end GlobalTheory.RunJoin
