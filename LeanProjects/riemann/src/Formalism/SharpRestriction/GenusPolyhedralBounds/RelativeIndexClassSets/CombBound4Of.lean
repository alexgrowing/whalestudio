import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def ShareRhoT (T rz rq d : ℕ) : Prop := (rz : ℝ) ≤ rq + 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def flipOneThree (D : D7) (nW : ℕ) : ℝ :=
  max (16200 * Real.pi * (nW : ℝ) * (D.R.m : ℝ) ^ 4 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4)
    (max ((2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 4 * (nW : ℝ) + 2 * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3)
      ((D.R.r : ℝ) * (2 * (D.R.f : ℝ) * (D.R.m : ℝ)) ^ 3))

def PageSupp (D : D7) (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) {j : ℕ} (C2 A2 : ℝ) (nW : ℕ) (S : Scal B) (wL : WeightFamilies.Wt D j) :
    Prop :=
  flipOneThree D nW ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  (∀ σ : B.KO →+* ℂ, (DF wL : ℝ) / 2 * Real.log ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤ Real.log ‖σ (S.sW : B.KO)‖) ∧
  (D.R.f : ℝ) ^ 2 ≤ D.host.rdE ∧ 8 ≤ D.R.r ∧ 3 ≤ DF wL

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def CombBound4 (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Prop :=
  ∀ la (ζ : PtsG G la),
    0 ≤ X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ∧ (X.vAt la ((Qf la).y ζ) (X.inc _ G.et) ≠ ⊤ →
      X.depth S.sW wL la ((Qf la).y ζ) ≤
        (((nus la : ℝ) + c / (2 * (G.iet : ℝ)) * (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal : ℝ) : EReal))

theorem combBound4_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : j < D.R.m) (h : CombBound G S c nus) (Qf : ∀ la, LocalPointData G la) : CombBound4 G Qf S c nus :=
  fun la ζ => (h la ((Qf la).y ζ)).1 hj

def DepthAtM (X : PJ D B P j) (S : Scal B) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ∀ la (y : X.Pt la), X.depth S.sW wL la y ≤ ((nus la : ℝ) : EReal)

theorem depthAtM_of {G : GlobalFamilyData X ka wL wF} {S : Scal B} {c : ℝ} {nus : HeightOneSpectrum (𝓞 B.KO) → ℝ}
    (hj : D.R.m ≤ j) (h : CombBound G S c nus) : DepthAtM X S wL nus :=
  fun la y => (h la y).2 hj

def ConclAtM (large₂ : SizeData₂ D) (X : PJ D B P j) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ)
    (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  D.R.m ≤ j → DepthAtM X S wL nus →
    Concl X S ka wL wF T nus (X.rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

def PageGd4 (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

theorem pageGd4_iff {X : PJ D B P j} {ka : WeightFamilies.Wt D j} {large₂ : SizeData₂ D} {CG AG Pd : ℝ} :
    PageGd4 X ka large₂ CG AG Pd ↔ PageGd X ka large₂ CG AG Pd := Iff.rfl

def PolyDom4 (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
    (Gc PH Prw Pet Pd : ℝ) (ka : WeightFamilies.Wt D j) : Prop :=
  2 ≤ K.CRm ∧ 0 ≤ CR ∧ 0 ≤ Gc ∧ 0 ≤ Prw ∧ 0 ≤ WeightFamilies.PP0v D large₂ K.CL K.AL ∧ WeightFamilies.Obound B large₂ Ch Ah ∧
  WeightFamilies.RRv D H.CRc * WeightFamilies.PPv D large₂ H.Cc H.Ac ≤ WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ∧
  WeightFamilies.RRv D K.CRm * D.host.rdE ^ 2 ≤ WeightFamilies.RRv D CR ^ 2 ∧
  2 ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 ∧ 4 * H.CK ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * D.R.f ∧
  (2 * Gc + 6 * PH + Prw) * 25 ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  Pet ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂) ≤ WeightFamilies.PPv D large₂ C2 A2 ∧
  60 * Gc + 180 * PH + 44 * (2 * Gc + Prw + WeightFamilies.PP0v D large₂ K.CL K.AL * (1 + Real.log ka.size) + 3 / 2 * (Pd + PO D large₂)) +
      22 * (2 * WeightFamilies.PPv D large₂ Cq Aq) ≤ WeightFamilies.PPv D large₂ C2 A2 ^ 2 * (WeightFamilies.dimY D j : ℝ) ∧
  1 / 2 ≤ Prw ∧ Prw ≤ PH ∧ 0 ≤ Pet ∧
  Prw ≤ WeightFamilies.PPv D large₂ C2 A2

theorem polyDom4_iff {B : WeightFamilies.Prov D} {large₂ : SizeData₂ D} {K : KAdm} {H : KHyp} {C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd : ℝ}
    {ka : WeightFamilies.Wt D j} :
    PolyDom4 D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka ↔ PolyDom D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka :=
  Iff.rfl

def Conclusion1OfComb4 : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    TieC K H Ch Ah Cq Aq C2 A2 CR → PageAt large₂ C2 A2 → PageSupp D large₂ B C2 A2 nW S wL →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd4 (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoT (D := D) (j := j) T G.rz G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom4 (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    (j < D.R.m → ∃ Qf : ∀ la, LocalPointData G la,
      (∀ la, InBasis G la) ∧ (∀ la, (Qf la).InCurve) ∧ (∀ la, (Qf la).InTie S) ∧ (∀ la, (Qf la).InLiftC S Gc Prw T) ∧
      CombBound4 G Qf S (cc D large₂ C2 A2 CR wL) nus ∧ Heights Qf Gc PH Prw Pet) →
    (D.R.m ≤ j → DepthAtM (X j h1 h2) S wL nus) →
    ConclAtM large₂ (X j h1 h2) S ka wL wF T nus →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
