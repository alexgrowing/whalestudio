import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def WeightedPrimeSumBoundAlt (large₂ : SizeData₂ D) (X : PJ D B P j) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  (∀ la, 0 ≤ nus la) ∧ (Function.support nus).Finite ∧ (∑ᶠ la, |nus la| * X.lN la) ≤ PN D large₂ * wL.size

def HypC (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
    WeightedPrimeSumBoundAlt large₂ X wL nus ∧ H2 X S ka wL wF ∧ H3 large₂ H C2 A2 CR Bx wL T ∧ H4 large₂ X H C2 A2 CR ka wL wF T nW ∧
    (T : ℝ) ≤ large₂.sc.x ^ CT

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def CombBound (G : GlobalFamilyData X ka wL wF) (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ∀ la (y : X.Pt la),
    (j < D.R.m → 0 ≤ X.vAt la y (X.inc _ G.et) ∧ (X.vAt la y (X.inc _ G.et) ≠ ⊤ →
      X.depth S.sW wL la y ≤ (((nus la : ℝ) + c / (2 * (G.iet : ℝ)) * (X.vAt la y (X.inc _ G.et)).toReal : ℝ) : EReal))) ∧
    (D.R.m ≤ j → X.depth S.sW wL la y ≤ ((nus la : ℝ) : EReal))

def LatAt (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) : Prop := Submodule.IsLattice B.KO (B.Mlat j ka)

def SupBoundByL2AtWeight (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CG AG : ℝ) : Prop :=
  ∀ (F : B.Cusp j ka) (σ : B.KO →+* ℂ),
    B.supN j ka σ F ^ 2 ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * B.l2NormAlt j ka σ F ^ 2

def LAMwAt (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (C A : ℝ) : Prop :=
  ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 →
    -(WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size) ≤ WeightFamilies.meanLogSup B F

def QAt (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ck Ch Ah Cc Ac T c : ℝ) : Prop :=
  0 ≤ CR → WeightFamilies.Obound B large₂ Ch Ah → ka.n = D.R.nV → ka.LastPos →
    ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < T → 0 < c → T * c ≤ 1 →
  ∃ be : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ, (∀ la, 0 ≤ be la) ∧
    (be.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size ∧
  ∀ th : Fin (WeightFamilies.rhoP B CR T c j ka) → B.Mlat j ka,
    Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔ WeightFamilies.MggK B CR T c j ka = ⊤ →
    (∀ i, WeightFamilies.meanLogSup B ((th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) →
  ∃ nn : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ,
    (∀ la, ∃ ℓ : ℕ,
      WeightFamilies.lenAt B la (WeightFamilies.Qm B CR T c j ka ⧸ Submodule.span (𝓞 B.KO)
        (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CR T c j ka))) = ℓ ∧
      (ℓ : ℝ) ≤ nn la + (WeightFamilies.rhoP B CR T c j ka : ℝ) * be la) ∧
    (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ (WeightFamilies.rhoP B CR T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cc Ac * ka.size

namespace GlobalFamilyData

variable (G : GlobalFamilyData X ka wL wF)

def TiedW (S : Scal B) (Gc Prw : ℝ) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL ∧ (∀ k, G.w k ∈ B.Mlat j wL) ∧
  Real.log G.N ≤ Prw * (wL.size - 1) ∧ (∀ σ k, Real.log (B.supN j wL σ (G.w k)) ≤ G.mx σ) ∧
  (∑ σ, G.mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ Gc * wL.size

def TiedTh (S : Scal B) (Gc : ℝ) : Prop :=
  ∀ i, G.th' i ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B (G.th' i) ≤ Gc * wF.size

def TiedZ (S : Scal B) (T : ℕ) (Gc : ℝ) : Prop :=
  (∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ G.th0 k ∈ B.Mlat j (X.wF0 wL wF) ∧
    WeightFamilies.meanLogSup B (G.th0 k) ≤ Gc * (X.wF0 wL wF).size ∧ ∑ i, G.alz k i = a0 D j T) ∧
  (∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β) ∧
  (∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)

def TiedQ (large₂ : SizeData₂ D) (S : Scal B) (CRm : ℝ) (T : ℕ) (c Ch Ah : ℝ) : Prop :=
  G.rq = WeightFamilies.rhoP B CRm T c j ka ∧ (∀ i, ((G.th i : B.Mlat j ka) : B.Cusp j ka) ∈ X.Thc S.sK ka) ∧
  Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka)) ⊔ WeightFamilies.MggK B CRm T c j ka = ⊤ ∧
  ∀ i, WeightFamilies.meanLogSup B ((G.th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size

def TiedEt (large₂ : SizeData₂ D) (Cf Af : ℝ) : Prop :=
  j < D.R.m → 0 < G.iet ∧ G.et ≠ 0 ∧ X.NonZeroComp _ G.et ∧
    ∀ σ, Real.log (B.supN j _ σ G.et) / G.iet ≤ WeightFamilies.PPv D large₂ Cf Af

end GlobalFamilyData

def DeepHerm (X : PJ D B P j) (ka : WeightFamilies.Wt D j) : Prop :=
  ∃ (dH : ℕ) (Hm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => B.l2NormAlt j ka σ) dH), Hm.Conj

def DeepSubMul (X : PJ D B P j) : Prop := Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul X

def DeepLogD (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (Pd : ℝ) : Prop := Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd

def PageGd (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

def ShareRd (T del d : ℕ) : Prop := (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ d

def ShareRho (T rz d : ℕ) : Prop := (rz : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def ShareRhoP (T rq d : ℕ) : Prop := (rq : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def LocalPointData.InLift {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (T : ℕ) : Prop :=
  ∀ a ∈ Q.A0, ∃ x : ↥(HK X la G.w wF), toA0K X la G.w wF x = a ∧ toWK X la G.w wF (a0 D j T) x ∈ Q.AA T

def LocalPointData.InLiftC {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (S : Scal B) (Gc Prw : ℝ) (T : ℕ) : Prop :=
  G.TiedW S Gc Prw → Q.InCurve → Q.InTie S → Q.InLift T

def InContainZ (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (T : ℕ) : Prop :=
  Submodule.span (Kp X la G.N)
      {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
          θ ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ v = secPow X la G.w al * emb X la G.N (X.inc _ θ)} ≤
    Submodule.span (Kp X la G.N) (Set.range (zK G la))

def InContainM (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ) : Prop :=
  Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc ka F)) '' (WeightFamilies.MggK B CRm T c j ka : Set (B.Cusp j ka))) ≤
    Submodule.span (Kp X la G.N)
      ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       Set.range (zK G la))

def Conclusion1OfComb : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ) (Qf : ∀ la, LocalPointData G la),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InBasis G la) → (∀ la, (Qf la).InCurve) → (∀ la, (Qf la).InTie S) → (∀ la, (Qf la).InLiftC S Gc Prw T) →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    Heights Qf Gc PH Prw Pet →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
