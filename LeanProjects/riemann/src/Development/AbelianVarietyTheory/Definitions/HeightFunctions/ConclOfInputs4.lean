import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfRefinedInputs
import Formalism.LocalToGlobal.ProjectiveLattices.XPlusWireT

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.NetNorms Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn

variable {D : D7}

section Abstract

variable {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

structure PageRun (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ)
    (h0 : ℝ) : Prop where
  hyp : FamilyHypotheses.HypPage large₂ X H C2 A2 7 CT ka wL wF Tn nP nW h0
  page : PageAt large₂ C2 A2
  tie : H.C1 = C2 ∧ H.A1 = A2 ∧ H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = 7 ∧ 12 ≤ A2

def BaseIn (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ∧ LatAt B j ka ∧ LAMwAt large₂ B j ka K.CL K.AL ∧
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) ∧ DeepSubMul X

def FamIn (large₂ : SizeData₂ D) {X : PJ D B P j} (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR : ℝ) (S : Scal B)
    {ka wL wF : WeightFamilies.Wt D j} (T : ℕ) (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ) : Prop :=
  G.TiedW S Gc Prw ∧ G.TiedTh S Gc ∧ G.TiedEt large₂ K.Cf K.Af ∧ PageGd X ka large₂ K.CG K.AG Pd ∧ GrowthConstantBound large₂ B Gc ∧
    PageGq large₂ Gc Ch Ah ∧ ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) ∧
    ShareRhoR G S T (X.rk ka (B.Mlat j ka)) ∧
    ShareRhoP (D := D) (j := j) T (WeightFamilies.rhoP B K.CRm T (cc D large₂ C2 A2 CR wL) j ka) (X.rk ka (B.Mlat j ka)) ∧
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ∧ (∀ la, InBasis G la) ∧
    ∀ la, InContainMR G la S K.CRm T (cc D large₂ C2 A2 CR wL)

def PtIn {X : PJ D B P j} (S : Scal B) {ka wL wF : WeightFamilies.Wt D j} (T : ℕ) (G : GlobalFamilyData X ka wL wF) (c Gc PH Prw Pet : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  CombBound G S c nus ∧ ∃ Qf : ∀ la, LocalPointData G la, (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧
    (∀ la, (Qf la).InLiftC S Gc Prw T) ∧ Heights Qf Gc PH Prw Pet

def NetIn (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (K : KAdm) (Pd : ℝ) : Prop :=
  ∃ (Nt : NetData B j ka) (σ₀ : B.KO →+* ℂ), NetMax Nt ∧ NetLeSup Nt ∧ NetPageG Nt large₂ K.CG K.AG ∧ NetInj Nt σ₀ ∧
    Real.log (Fintype.card (Nt.NN σ₀) : ℝ) ≤ Pd

def InputsNet (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus ∧
    ∃ (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ), NetIn large₂ B j ka K Pd ∧
      FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S T G Gc PH Prw Pet Pd ∧ PtIn S T G (cc D large₂ C2 A2 CR wL) Gc PH Prw Pet nus

def InputsR (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  BaseIn large₂ X K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus ∧ SupBoundByL2AtWeight large₂ B j ka K.CG K.AG ∧ DeepHerm X ka ∧
    ∃ (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ), DeepLogD X ka Pd ∧
      FamIn large₂ K H Ch Ah Cq Aq C2 A2 CR S T G Gc PH Prw Pet Pd ∧ PtIn S T G (cc D large₂ C2 A2 CR wL) Gc PH Prw Pet nus

def Inputs4 (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ∧
    LatAt B j ka ∧ SupBoundByL2AtWeight large₂ B j ka K.CG K.AG ∧ LAMwAt large₂ B j ka K.CL K.AL ∧
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) ∧
    TieC K H Ch Ah Cq Aq C2 A2 CR ∧ PageAt large₂ C2 A2 ∧ PageSupp D large₂ B C2 A2 nW S wL ∧
    ∃ (G : GlobalFamilyData X ka wL wF) (Gc PH Prw Pet Pd : ℝ),
      G.TiedW S Gc Prw ∧ G.TiedTh S Gc ∧ G.TiedZ S T Gc ∧
      G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah ∧ G.TiedEt large₂ K.Cf K.Af ∧
      DeepHerm X ka ∧ DeepSubMul X ∧ DeepLogD X ka Pd ∧ PageGd4 X ka large₂ K.CG K.AG Pd ∧
      ShareRd (D := D) (j := j) T G.del (X.rk ka (B.Mlat j ka)) ∧
      ShareRhoT (D := D) (j := j) T G.rz G.rq (X.rk ka (B.Mlat j ka)) ∧
      ShareRhoP (D := D) (j := j) T G.rq (X.rk ka (B.Mlat j ka)) ∧
      PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ∧
      (∀ la, InContainZ G la S T) ∧ (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) ∧
      (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
        (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
        CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) ∧
      (D.R.m ≤ j → DepthAtM X S wL nus) ∧
      ConclAtM large₂ X S ka wL wF T nus ∧
      (D.R.m ≤ j → ∃ Qf : ∀ la, LocalPointData G la,
        (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
        Heights Qf Gc PH Prw Pet)

def k4 (large₂ : SizeData₂ D) (CL : ℝ) : KAdm := ⟨1041 * zBase large₂, 2, 200000, 2, 1, 2, CL, 2, 7⟩

end Abstract

theorem concl_of_inputs4 {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp)
    (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ)
    (h : Inputs4 large₂ (X j h1 h2) K H Ch Ah Cq Aq C2 A2 CR CT S ka wL wF T nP nW h0 nus) :
    Concl (X j h1 h2) S ka wL wF T nus ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2) := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, G, Gc, PH, Prw, Pet, Pd, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13,
    b14, b15, b16, b17, b18, -⟩ := h
  exact theorem_zero_of_refined_inputs large₂ X K H Ch Ah Cq Aq C2 A2 CR CT j h1 h2 S ka wL wF T nP nW h0 nus a1 a2 a3 a4 a5 a6 a7 a8 G Gc PH Prw
    Pet Pd b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18

def RunHolds (x₀ : ℝ → ℝ → ℝ) {T : Top D} (h : LawsP T) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) :
    Prop :=
  ∀ (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    PageRun large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x →
    (∃ (n : SecNorm (recB h.toLawsCore)) (K : KAdm) (Cq : ℝ),
      Inputs4 large₂ (recPlusN h j hj n) K H 1 4 Cq 4 C2 A2 7 CT (scalOfP n.base hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0
        (nusR h j wL) ∧
      Concl (recPlusN h j hj n) (scalOfP n.base hinj EX p ka wL wF Tn) ka wL wF Tn (nusR h j wL)
        ((recPlusN h j hj n).rk ka (n.base.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)) ∧
    HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0
      (nusR h j wL) ∧
    Concl (recPJ h j hj) (scalOfP (recB h.toLawsCore) hinj EX p ka wL wF Tn) ka wL wF Tn (nusR h j wL)
      ((recPJ h j hj).rk ka ((recB h.toLawsCore).Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end GlobalTheory.FinalJoin
