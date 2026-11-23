import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.ConclOfInputs4
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfInputs
import Formalism.LocalToGlobal.ProjectiveLattices.VolProofs

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinalJoin2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.NetNorms Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin GlobalTheory.RunIn GlobalTheory.FinalJoin

def VolW (D : D7) : Prop := ∀ j, InR D j → VolPairEx (D.sp.W j) ∧ FinVol (D.sp.W j)

structure FieldOK0 (D : D7) (p : ℕ) : Prop where
  own : p = D.host.pde ∨ p = D.host.pde'
  full : OFull D
  zetaM : OZeta D
  zetaP : zeta p ∈ FO D
  curve : GlobalTheory.CompRat.CurveOver (hostOfRecord D) (FO D) (D.host.g 0 * D.host.g 1 * p)
  kpsi : OKPsi D
  bad : 0 ∉ D.host.levelPrimes
  split : D.host.cls p = PrimeClass.splitK

theorem fieldOK_iff (D : D7) (p : ℕ) : FieldOK D p ↔ FieldOK0 D p ∧ Formalism.L2.Theta.VolTieG D :=
  ⟨fun h => ⟨⟨h.own, h.full, h.zetaM, h.zetaP, h.curve, h.kpsi, h.bad, h.split⟩, h.vol⟩,
    fun ⟨h, v⟩ => ⟨h.own, h.full, h.zetaM, h.zetaP, h.curve, h.kpsi, v, h.bad, h.split⟩⟩

def FieldSmall (D : D7) (large₂ : SizeData₂ D) : Prop :=
  letI : NumberField (FO D) := NumberField.mk
  Real.log (Module.finrank ℚ (FO D)) ≤ PO D large₂ ∧
    Real.log |((NumberField.discr (FO D) : ℤ) : ℝ)| / Module.finrank ℚ (FO D) ≤ PO D large₂

def NumOK (D : D7) (x : ℝ) : Prop :=
  ∃ (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm), DV.KapDef D ∧ SizesAt L ∧ Pm.CnW = 10 ∧
    (∀ i, Real.log (D.host.g i) ≤ 9 * L.sc.L + 1) ∧ 1000 ≤ Tp.CP ∧ Tp.CP ^ 20 ≤ zBase L ∧ x ≤ L.sc.x ∧ FieldSmall D L

structure RecOK (D : D7) (x : ℝ) : Prop where
  one : FieldOK0 D D.host.pde
  two : FieldOK0 D D.host.pde'
  xi1 : ∃ xi, XiOK D D.host.pde xi
  xi2 : ∃ xi, XiOK D D.host.pde' xi
  err : Nonempty (ErrX D)
  num : NumOK D x

def NormComparisonConstants (K : KAdm) (H : KHyp) (Ch Ah _Cq Aq C2 A2 CR : ℝ) : Prop :=
  H.C1 = C2 ∧ H.A1 = A2 ∧ H.Cc = C2 ∧ H.Ac = A2 ∧ H.CRc = 7 ∧ CR = 7 ∧ K.CRm = 7 ∧ 12 ≤ A2 ∧
    K.AG ≤ 3 ∧ K.Af ≤ 2 ∧ K.AW ≤ 2 ∧ K.AL ≤ 4 ∧ 1 ≤ Ch ∧ 4 ≤ Ah ∧ Aq ≤ 11

variable {D : D7}

def Inputs5 {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (large₂ : SizeData₂ D) (X : PJ D B P j) (K : KAdm) (H : KHyp)
    (Ch Ah Cq Aq C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ∧
    LatAt B j ka ∧ SupBoundByL2AtWeight large₂ B j ka K.CG K.AG ∧ LAMwAt large₂ B j ka K.CL K.AL ∧
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) ∧
    NormComparisonConstants K H Ch Ah Cq Aq C2 A2 CR ∧ PageAt large₂ C2 A2 ∧ PageSupp D large₂ B C2 A2 nW S wL ∧
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
      (D.R.m ≤ j → AtMInputs G S T Gc PH Prw Pet)

def RunInputs5 (x₀ : ℝ → ℝ → ℝ) (K : KAdm) (Cq : ℝ → ℝ → ℝ) {T : Top D} (h : LawsP T)
    (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) : Prop :=
  ∀ (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    PageRun large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → x₀ H.CA H.CK ≤ large₂.sc.x →
    ∃ n : SecNorm (recB h.toLawsCore),
      Inputs5 large₂ (recPlusN h j hj n) K H 1 4 (Cq H.CA H.CK) 4 C2 A2 7 CT (scalOfP n.base hinj EX p ka wL wF Tn) ka wL wF Tn nP nW h0
        (nusR h j wL)

def HasRuns (x₀ : ℝ → ℝ → ℝ) {T : Top D} (h : LawsP T) : Prop :=
  ∀ (j : ℕ) (hj : InR D j), ∃ (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ),
    PageRun large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 ∧ x₀ H.CA H.CK ≤ large₂.sc.x

end GlobalTheory.FinalJoin2
