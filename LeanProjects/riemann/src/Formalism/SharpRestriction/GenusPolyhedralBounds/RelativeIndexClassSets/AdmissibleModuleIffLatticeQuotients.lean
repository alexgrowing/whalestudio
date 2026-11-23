import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.GlobalFamilyData
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Geo NumberField IsDedekindDomain

namespace Formalism.MainNotions.Gaps.FamilyHypotheses

def SupBoundPageRows (D : D7) (large₂ : SizeData₂ D) {j : ℕ} (ka : WeightFamilies.Wt D j) : Prop :=
  (∀ i, Real.log (D.host.g i) ≤ 9 * large₂.sc.L + 1) ∧
  lrd D ≤ 2 * large₂.sc.L ∧
  Real.log D.host.d ≤ 2 * large₂.sc.L ∧
  Real.log (Ideal.absNorm D.host.ccK) ≤ 2 * large₂.sc.L ∧
  Real.log D.R.f ≤ 2 * large₂.sc.L ∧
  Real.log D.host.pde ≤ large₂.sc.L ∧
  Real.log D.host.pde' ≤ large₂.sc.L ∧
  Real.log (1 + DF ka) ≤ 2 * large₂.sc.L ∧
  Real.log ka.n ≤ large₂.sc.L

def OwnPr (D : D7) (p : ℕ) : Prop := p = Formalism.MainNotions.DIV.Cons.po D ∨ p = Formalism.MainNotions.DIV.Cons.po2 D

theorem ownPr_iff (D : D7) (p : ℕ) : OwnPr D p ↔ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ) := Iff.rfl

theorem ownPr_po (D : D7) : OwnPr D (Formalism.MainNotions.DIV.Cons.po D) := Or.inl rfl

theorem isDistinguishedPrime_second (D : D7) : OwnPr D (Formalism.MainNotions.DIV.Cons.po2 D) := Or.inr rfl

theorem ownPr_forall (D : D7) (Q : ℕ → Prop) :
    (∀ p, OwnPr D p → Q p) ↔ Q (Formalism.MainNotions.DIV.Cons.po D) ∧ Q (Formalism.MainNotions.DIV.Cons.po2 D) :=
  ⟨fun h => ⟨h _ (ownPr_po D), h _ (isDistinguishedPrime_second D)⟩, fun h p hp => by rcases hp with rfl | rfl; exacts [h.1, h.2]⟩

section Split

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def FourthHypothesisSizes (large₂ : SizeData₂ D) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) : Prop :=
  large₂.sc.b ≤ ka.size ∧ (T : ℝ) * wL.size ≤ 2 * ka.size ∧
  wF.size ≤ ((WeightFamilies.dimY D j : ℝ) + 2) * wL.size + 5 * D.R.f * (D.R.r : ℝ) ^ 2 * T ∧
  WeightFamilies.PPv D large₂ C2 A2 ^ 3 * (T : ℝ) ^ 2 ≤ large₂.sc.b ∧
  WeightFamilies.RRv D CR * WeightFamilies.PPv D large₂ C2 A2 ≤ large₂.sc.b ∧
  (∀ i, 2 * DF ka + 2 < D.host.g i)

def I4 (large₂ : SizeData₂ D) (X : PJ D B P j) (wL wF : WeightFamilies.Wt D j) (nW : ℕ) : Prop :=
  ∃ PLam lNc : ℝ, PLam ≤ 1009 * Zb D large₂ ∧ lNc ≤ 81 * Zb D large₂ ^ 2 ∧
  (j < D.R.m → ∃ w1 : WeightFamilies.Wt D j, IsDoubledWeightWithShift wL w1 nW ∧ ∃ th ∈ B.Mlat j w1, X.NonZeroComp w1 th ∧
    ∀ σ, Real.log (B.supN j w1 σ th) ≤ 2 * PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size) ∧
  ∃ w2 : WeightFamilies.Wt D j, IsG2 wL wF w2 ∧ ∃ th ∈ B.Mlat j w2, X.NonZeroComp w2 th ∧
    ∀ σ, Real.log (B.supN j w2 σ th) ≤ PI4 D j PLam lNc * WeightFamilies.dimY D j * wL.size

theorem fourthHypothesis_iff_sizes_and_index (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nW : ℕ) :
    H4 large₂ X H C2 A2 CR ka wL wF T nW ↔ FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g⟩ => ⟨⟨a, b, c, d, e, f⟩, g⟩, fun ⟨⟨a, b, c, d, e, f⟩, g⟩ => ⟨a, b, c, d, e, f, g⟩⟩

def HypPage (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ)
    (h0 : ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ H3 large₂ H C2 A2 CR 0 wL T ∧
    FourthHypothesisSizes large₂ C2 A2 CR ka wL wF T ∧ (T : ℝ) ≤ large₂.sc.x ^ CT

theorem hyp_iff (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Hyp large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ↔
      HypPage large₂ X H C2 A2 CR CT ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧ H1 large₂ X H S wL nus ∧
        H2 X S ka wL wF ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, f, ((fourthHypothesis_iff_sizes_and_index ..).1 g).1, h⟩, c, d, e, ((fourthHypothesis_iff_sizes_and_index ..).1 g).2⟩,
    fun ⟨⟨a, b, f, g, h⟩, c, d, e, i⟩ => ⟨a, b, c, d, e, f, (fourthHypothesis_iff_sizes_and_index ..).2 ⟨g, i⟩, h⟩⟩

theorem hypC_iff (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR CT : ℝ) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j)
    (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ X H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus ↔
      HypPage large₂ X H C2 A2 CR CT ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
        Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ X wL nus ∧ H2 X S ka wL wF ∧ I4 large₂ X wL wF nW :=
  ⟨fun ⟨a, b, c, d, e, f, g, h⟩ => ⟨⟨a, b, f, ((fourthHypothesis_iff_sizes_and_index ..).1 g).1, h⟩, c, d, e, ((fourthHypothesis_iff_sizes_and_index ..).1 g).2⟩,
    fun ⟨⟨a, b, f, g, h⟩, c, d, e, i⟩ => ⟨a, b, c, d, e, f, (fourthHypothesis_iff_sizes_and_index ..).2 ⟨g, i⟩, h⟩⟩

theorem deepIn_iff (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepIn X ka large₂ CG AG Pd ↔ Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepHerm X ka ∧ Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepSubMul X ∧
      Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepLogD X ka Pd ∧ Formalism.MainNotions.Gaps.EtaleWeightGaps.PageGd X ka large₂ CG AG Pd := Iff.rfl

def ZSel {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF) (T : ℕ) : Prop :=
  (∀ k, ∑ i, G.alz k i = Formalism.MainNotions.Gaps.EtaleWeightGaps.a0 D j T) ∧
  (∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β) ∧
  (∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)

theorem tiedZ_iff {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF) (S : Scal B) (T : ℕ) (Gc : ℝ) :
    G.TiedZ S T Gc ↔
      (∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ G.th0 k ∈ B.Mlat j (X.wF0 wL wF) ∧
        WeightFamilies.meanLogSup B (G.th0 k) ≤ Gc * (X.wF0 wL wF).size) ∧ ZSel G T :=
  ⟨fun ⟨a, b, c⟩ => ⟨fun k => ⟨(a k).1, (a k).2.1, (a k).2.2.1⟩, fun k => (a k).2.2.2, b, c⟩,
    fun ⟨a, b, c, d⟩ => ⟨fun k => ⟨(a k).1, (a k).2.1, (a k).2.2, b k⟩, c, d⟩⟩

def refill {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF)
    (del : ℕ) (th' : Fin del → B.Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF)) (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ B.Cusp j ka)
    (rq : ℕ) (th : Fin rq → B.Mlat j ka) (iet : ℕ) (et : B.Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF :=
  ⟨G₀.N, G₀.w, del, th', rz, alz, th0, zc, rq, th, iet, et, G₀.mx⟩

theorem tiedW_refill {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData X ka wL wF) (S : Scal B) (Gc Prw : ℝ)
    (del : ℕ) (th' : Fin del → B.Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
    (th0 : Fin rz → B.Cusp j (X.wF0 wL wF)) (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ B.Cusp j ka)
    (rq : ℕ) (th : Fin rq → B.Mlat j ka) (iet : ℕ) (et : B.Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)) :
    (refill G₀ del th' rz alz th0 zc rq th iet et).TiedW S Gc Prw ↔ G₀.TiedW S Gc Prw := Iff.rfl

end Split

section Views

variable {D : D7} {G : DV.Geo D.what₂.LL} {Lev : Type}

def MSt (F : ShimFam D G Lev) : Prop := WeightFamilies.adm1 (toWeightFamilies F)

def GSt (F : ShimFam D G Lev) (large₂ : SizeData₂ D) (CG AG : ℝ) : Prop := WeightFamilies.adm2 large₂ (toWeightFamilies F) CG AG

variable (F : ShimFam D G Lev) (I : Type) (dat : I → Dat D Lev) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I)
  (hiW : ∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j)

def AdmissibilitySecond (large₂ : SizeData₂ D) (CA C1 A1 CG AG : ℝ) : Prop := WeightAlgebra.adm2 large₂ (toWeightAlgebra F I dat hI iW hiW) CA C1 A1 CG AG

def WSt (large₂ : SizeData₂ D) (CA C1 A1 CW AW : ℝ) : Prop := WeightAlgebra.ArchimedeanSignatureMatching large₂ (toWeightAlgebra F I dat hI iW hiW) CA C1 A1 CW AW

def IntegralityFamily (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    H2 (toWeightAlgebra F I dat hI iW hiW j h1 h2) (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) ka wL wF

def ScalSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ScalB large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H.C1 H.A1 (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) ka wL wF T

def FourthHypothesisIndexBound (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    I4 large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) wL wF nW

def DeepSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT CG AG : ℝ) (Pd : (j : ℕ) → WeightFamilies.Wt D j → ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal (toWeightFamilies F)) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (toWeightFamilies F).KO) → ℝ),
    Hyp large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepIn (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka large₂ CG AG (Pd j ka)

def LatSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.LatAt (toWeightFamilies F) j ka

def SupL2AtFamily (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT CG AG : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.SupBoundByL2AtWeight large₂ (toWeightFamilies F) j ka CG AG

def DeepHermSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepHerm (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka

def DeepSubMulSt : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m), Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepSubMul (toWeightAlgebra F I dat hI iW hiW j h1 h2)

def DeepLogDSt (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) (Pd : (j : ℕ) → WeightFamilies.Wt D j → ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepLogD (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka (Pd j ka)

def TiedWSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc Prw : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF,
      G.TiedW (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) Gc Prw

def TiedThSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j wF), Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j wF)) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ i, G.th' i ∈ Sh) →
        G.TiedTh (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) Gc

def TiedZSt (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF)),
      Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ k, G.th0 k ∈ Sh) → ZSel G T →
        G.TiedZ (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) T Gc

theorem tiedThSt_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ}
    (hS : ScalSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT)
    (hG : ∀ po ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∀ PLam : ℝ, PLam ≤ 1009 * Zb D large₂ → WeightAlgebra.Gc large₂ (toWeightFamilies F) PLam po ≤ Gc) :
    TiedThSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc := by
  intro j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨_, _, _, _, _, po, hpo, _, PLam, hPL, _, ⟨Sh, hsub, hspan, hmean⟩, _, _⟩ := hS j h1 h2 ka wL wF T nP nW h0 hp hc
  exact ⟨Sh, hspan, fun G hGm i => ⟨hsub (Finset.mem_coe.2 (hGm i)), (hmean _ (hGm i)).trans
    (mul_le_mul_of_nonneg_right (hG po hpo PLam hPL) (zero_le_one.trans (WeightFamilies.Wt.one_le_size _)))⟩⟩

theorem tiedThSt_iff {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ} :
    TiedThSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc ↔
      ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
        HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
        SupBoundPageRows D large₂ ka →
        ShortG (toWeightAlgebra F I dat hI iW hiW j h1 h2) wF
          ((toWeightAlgebra F I dat hI iW hiW j h1 h2).Thc (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T).sF wF) (Gc * wF.size) := by
  constructor
  · intro h j h1 h2 ka wL wF T nP nW h0 hp hc
    obtain ⟨Sh, hs, hG⟩ := h j h1 h2 ka wL wF T nP nW h0 hp hc
    have key := fun g (hg : g ∈ Sh) => hG ⟨0, fun k => k.elim0, 1, fun _ => g, 0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      0, fun k => k.elim0, 0, 0, 0⟩ (fun _ => hg) 0
    exact ⟨Sh, fun g hg => (key g (Finset.mem_coe.1 hg)).1, hs, fun g hg => (key g hg).2⟩
  · intro h j h1 h2 ka wL wF T nP nW h0 hp hc
    obtain ⟨Sh, hsub, hs, hm⟩ := h j h1 h2 ka wL wF T nP nW h0 hp hc
    exact ⟨Sh, hs, fun G hG i => ⟨hsub (Finset.mem_coe.2 (hG i)), hm _ (hG i)⟩⟩

theorem tiedZSt_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ}
    (hS : ScalSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT) (h2n : IntegralityFamily F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT)
    (hG : ∀ po ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∀ PLam : ℝ, PLam ≤ 1009 * Zb D large₂ → WeightAlgebra.Gc large₂ (toWeightFamilies F) PLam po ≤ Gc) :
    TiedZSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc := by
  intro j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨_, _, _, _, _, po, hpo, _, PLam, hPL, _, _, ⟨Sh, hsub, hspan, hmean⟩, _⟩ := hS j h1 h2 ka wL wF T nP nW h0 hp hc
  have hM := (h2n j h1 h2 ka wL wF T nP nW h0 hp).2.2.1
  exact ⟨Sh, hspan, fun G hGm hz => (tiedZ_iff G _ T Gc).2 ⟨fun k => ⟨hsub (Finset.mem_coe.2 (hGm k)), hM (hsub (Finset.mem_coe.2 (hGm k))),
    (hmean _ (hGm k)).trans (mul_le_mul_of_nonneg_right (hG po hpo PLam hPL) (zero_le_one.trans (WeightFamilies.Wt.one_le_size _)))⟩, hz⟩⟩

theorem tied_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc Prw : ℝ}
    (hW : TiedWSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc Prw) (hT : TiedThSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc)
    (hZ : TiedZSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (hp : HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0) (hc : SupBoundPageRows D large₂ ka) :
    ∃ (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF) (Sh : Finset ((toWeightFamilies F).Cusp j wF))
      (Sh0 : Finset ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))),
      Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j wF)) = ⊤ ∧
      Submodule.span (toWeightFamilies F).KO (Sh0 : Set ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))) = ⊤ ∧
      ∀ (del : ℕ) (th' : Fin del → (toWeightFamilies F).Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
        (th0 : Fin rz → (toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))
        (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ (toWeightFamilies F).Cusp j ka)
        (rq : ℕ) (th : Fin rq → (toWeightFamilies F).Mlat j ka) (iet : ℕ) (et : (toWeightFamilies F).Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)),
        (∀ i, th' i ∈ Sh) → (∀ k, th0 k ∈ Sh0) → ZSel (refill G₀ del th' rz alz th0 zc rq th iet et) T →
        (refill G₀ del th' rz alz th0 zc rq th iet et).TiedW (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) Gc Prw ∧
        (refill G₀ del th' rz alz th0 zc rq th iet et).TiedTh (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) Gc ∧
        (refill G₀ del th' rz alz th0 zc rq th iet et).TiedZ (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) T Gc := by
  obtain ⟨G₀, hw⟩ := hW j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨Sh, hs, hth⟩ := hT j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨Sh0, hs0, hz⟩ := hZ j h1 h2 ka wL wF T nP nW h0 hp hc
  exact ⟨G₀, Sh, Sh0, hs, hs0, fun del th' rz alz th0 zc rq th iet et a b c =>
    ⟨hw, hth (refill G₀ del th' rz alz th0 zc rq th iet et) a, hz (refill G₀ del th' rz alz th0 zc rq th iet et) b c⟩⟩

theorem MSt.latSt (h : MSt F) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : LatSt F I dat hI iW hiW large₂ H C2 A2 CR CT :=
  fun j h1 h2 ka _ _ _ _ _ _ _ => h j h1 h2 ka

theorem GSt.sup_L2_of_all_weights {large₂ : SizeData₂ D} {CG AG : ℝ} (h : GSt F large₂ CG AG) (H : KHyp) (C2 A2 CR CT : ℝ) :
    SupL2AtFamily F I dat hI iW hiW large₂ H C2 A2 CR CT CG AG :=
  fun j h1 h2 ka _ _ _ _ _ _ _ Fo σ => h j h1 h2 ka Fo σ

theorem deepSt_of {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT CG AG : ℝ} {Pd : (j : ℕ) → WeightFamilies.Wt D j → ℝ}
    (hH : DeepHermSt F I dat hI iW hiW large₂ H C2 A2 CR CT) (hM : DeepSubMulSt F I dat hI iW hiW)
    (hD : DeepLogDSt F I dat hI iW hiW large₂ H C2 A2 CR CT Pd)
    (hG : ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
      HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
      Formalism.MainNotions.Gaps.EtaleWeightGaps.PageGd (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka large₂ CG AG (Pd j ka)) :
    DeepSt F I dat hI iW hiW large₂ H C2 A2 CR CT CG AG Pd :=
  fun j h1 h2 _ ka wL wF T nP nW h0 _ hy =>
    have hp := ((hyp_iff ..).1 hy).1
    ⟨hH j h1 h2 ka wL wF T nP nW h0 hp, hM j h1 h2, hD j h1 h2 ka wL wF T nP nW h0 hp, hG j h1 h2 ka wL wF T nP nW h0 hp⟩

theorem hypC_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT : ℝ}
    (hS : ScalSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT) (h2n : IntegralityFamily F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT)
    (hI4 : FourthHypothesisIndexBound F I dat hI iW hiW large₂ H C2 A2 CR CT)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (toWeightFamilies F).KO) → ℝ)
    (hp : HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0) (hc : SupBoundPageRows D large₂ ka)
    (hH1 : Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) wL nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR 0 CT
      (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) ka wL wF T nP nW h0 nus :=
  (hypC_iff ..).2 ⟨hp, hS j h1 h2 ka wL wF T nP nW h0 hp hc, hH1, h2n j h1 h2 ka wL wF T nP nW h0 hp,
    hI4 j h1 h2 ka wL wF T nP nW h0 hp⟩

theorem AdmissibilitySecond.gSt {large₂ : SizeData₂ D} {CA C1 A1 CG AG : ℝ} (h : AdmissibilitySecond F I dat hI iW hiW large₂ CA C1 A1 CG AG) : GSt F large₂ CG AG := h.2

theorem admissibleModule_iff_lattice_quotients (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ) :
    WeightAlgebra.admitted large₂ (toWeightAlgebra F I dat hI iW hiW) K H Ch Ah Cq Aq ↔
      MSt F ∧ AdmissibilitySecond F I dat hI iW hiW large₂ H.CA H.C1 H.A1 K.CG K.AG ∧ WeightAlgebra.adm3 large₂ (toWeightAlgebra F I dat hI iW hiW) H.CA K.Cf K.Af ∧
        WSt F I dat hI iW hiW large₂ H.CA H.C1 H.A1 K.CW K.AW ∧ WeightAlgebra.adm5 large₂ (toWeightFamilies F) K.CL K.AL ∧ WeightAlgebra.adm6 (toWeightFamilies F) K.CRm ∧
        WeightAlgebra.adm7 large₂ (toWeightFamilies F) K.CRm H.CK Ch Ah Cq Aq := Iff.rfl

theorem hyp_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT : ℝ}
    (hS : ScalSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT) (h2n : IntegralityFamily F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT)
    (hI4 : FourthHypothesisIndexBound F I dat hI iW hiW large₂ H C2 A2 CR CT)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (toWeightFamilies F).KO) → ℝ)
    (hp : HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0) (hc : SupBoundPageRows D large₂ ka)
    (hH1 : H1 large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T) wL nus) :
    Hyp large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR 0 CT (Formalism.MainNotions.DIV.Cons.scalOf (toWeightFamilies F) hinj EX ka wL wF T)
      ka wL wF T nP nW h0 nus :=
  (hyp_iff ..).2 ⟨hp, hS j h1 h2 ka wL wF T nP nW h0 hp hc, hH1, h2n j h1 h2 ka wL wF T nP nW h0 hp,
    hI4 j h1 h2 ka wL wF T nP nW h0 hp⟩

theorem deepSt_apply {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT CG AG : ℝ} {Pd : (j : ℕ) → WeightFamilies.Wt D j → ℝ}
    (h : DeepSt F I dat hI iW hiW large₂ H C2 A2 CR CT CG AG Pd)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal (toWeightFamilies F)) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (toWeightFamilies F).KO) → ℝ)
    (hH : Hyp large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.DeepIn (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka large₂ CG AG (Pd j ka) :=
  h j h1 h2 S ka wL wF T nP nW h0 nus hH

theorem sW_scalOfP (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) {j : ℕ}
    (ka wL wF : WeightFamilies.Wt D j) (T : ℕ) :
    (Formalism.MainNotions.DIV.Cons.scalOfP B hinj EX p ka wL wF T).sW = (Formalism.MainNotions.DIV.Cons.scalOf B hinj EX ka wL wF T).sW := rfl

def IntegralityAtPrime (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    H2 (toWeightAlgebra F I dat hI iW hiW j h1 h2) (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) ka wL wF

def ScalStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ScalB large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H.C1 H.A1 (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) ka wL wF T

def TiedWStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc Prw : ℝ) : Prop :=
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF,
      G.TiedW (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) Gc Prw

def TiedThStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j wF), Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j wF)) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ i, G.th' i ∈ Sh) →
        G.TiedTh (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) Gc

def TiedZStP (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (p : ℕ) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR CT Gc : ℝ) : Prop :=
  OwnPr D p →
  ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
    HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
    SupBoundPageRows D large₂ ka →
    ∃ Sh : Finset ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF)),
      Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))) = ⊤ ∧
      ∀ G : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF, (∀ k, G.th0 k ∈ Sh) → ZSel G T →
        G.TiedZ (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) T Gc

theorem integrality_iff_at_prime {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT : ℝ} :
    IntegralityFamily F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT ↔ IntegralityAtPrime F I dat hI iW hiW hinj EX (Formalism.MainNotions.DIV.Cons.po D) large₂ H C2 A2 CR CT :=
  ⟨fun h _ => h, fun h => h (ownPr_po D)⟩

theorem scalars_iff_at_prime {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT : ℝ} :
    ScalSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT ↔ ScalStP F I dat hI iW hiW hinj EX (Formalism.MainNotions.DIV.Cons.po D) large₂ H C2 A2 CR CT :=
  ⟨fun h _ => h, fun h => h (ownPr_po D)⟩

theorem tiedWStP_iff {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} (p : ℕ) {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc Prw : ℝ} :
    TiedWStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT Gc Prw ↔ TiedWSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc Prw := Iff.rfl

theorem weightCondition_iff_at_prime {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc Prw : ℝ} :
    TiedWSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc Prw ↔ TiedWStP F I dat hI iW hiW hinj EX (Formalism.MainNotions.DIV.Cons.po D) large₂ H C2 A2 CR CT Gc Prw := Iff.rfl

theorem thetaCondition_iff_at_prime {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ} :
    TiedThSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc ↔ TiedThStP F I dat hI iW hiW hinj EX (Formalism.MainNotions.DIV.Cons.po D) large₂ H C2 A2 CR CT Gc :=
  ⟨fun h _ => h, fun h => h (ownPr_po D)⟩

theorem zeroCondition_iff_at_prime {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ} :
    TiedZSt F I dat hI iW hiW hinj EX large₂ H C2 A2 CR CT Gc ↔ TiedZStP F I dat hI iW hiW hinj EX (Formalism.MainNotions.DIV.Cons.po D) large₂ H C2 A2 CR CT Gc :=
  ⟨fun h _ => h, fun h => h (ownPr_po D)⟩

theorem tiedThStP_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ}
    (hS : ScalStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT)
    (hG : ∀ po ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∀ PLam : ℝ, PLam ≤ 1009 * Zb D large₂ → WeightAlgebra.Gc large₂ (toWeightFamilies F) PLam po ≤ Gc) :
    TiedThStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT Gc := by
  intro hown j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨_, _, _, _, _, po, hpo, _, PLam, hPL, _, ⟨Sh, hsub, hspan, hmean⟩, _, _⟩ := hS hown j h1 h2 ka wL wF T nP nW h0 hp hc
  exact ⟨Sh, hspan, fun G hGm i => ⟨hsub (Finset.mem_coe.2 (hGm i)), (hmean _ (hGm i)).trans
    (mul_le_mul_of_nonneg_right (hG po hpo PLam hPL) (zero_le_one.trans (WeightFamilies.Wt.one_le_size _)))⟩⟩

theorem tiedThStP_iff {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ} :
    TiedThStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT Gc ↔
      (OwnPr D p →
      ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ),
        HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0 →
        SupBoundPageRows D large₂ ka →
        ShortG (toWeightAlgebra F I dat hI iW hiW j h1 h2) wF
          ((toWeightAlgebra F I dat hI iW hiW j h1 h2).Thc (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T).sF wF) (Gc * wF.size)) := by
  constructor
  · intro h hown j h1 h2 ka wL wF T nP nW h0 hp hc
    obtain ⟨Sh, hs, hG⟩ := h hown j h1 h2 ka wL wF T nP nW h0 hp hc
    have key := fun g (hg : g ∈ Sh) => hG ⟨0, fun k => k.elim0, 1, fun _ => g, 0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      0, fun k => k.elim0, 0, 0, 0⟩ (fun _ => hg) 0
    exact ⟨Sh, fun g hg => (key g (Finset.mem_coe.1 hg)).1, hs, fun g hg => (key g hg).2⟩
  · intro h hown j h1 h2 ka wL wF T nP nW h0 hp hc
    obtain ⟨Sh, hsub, hs, hm⟩ := h hown j h1 h2 ka wL wF T nP nW h0 hp hc
    exact ⟨Sh, hs, fun G hG i => ⟨hsub (Finset.mem_coe.2 (hG i)), hm _ (hG i)⟩⟩

theorem tiedZStP_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc : ℝ}
    (hS : ScalStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT) (h2n : IntegralityAtPrime F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT)
    (hG : ∀ po ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∀ PLam : ℝ, PLam ≤ 1009 * Zb D large₂ → WeightAlgebra.Gc large₂ (toWeightFamilies F) PLam po ≤ Gc) :
    TiedZStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT Gc := by
  intro hown j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨_, _, _, _, _, po, hpo, _, PLam, hPL, _, _, ⟨Sh, hsub, hspan, hmean⟩, _⟩ := hS hown j h1 h2 ka wL wF T nP nW h0 hp hc
  have hM := (h2n hown j h1 h2 ka wL wF T nP nW h0 hp).2.2.1
  exact ⟨Sh, hspan, fun G hGm hz => (tiedZ_iff G _ T Gc).2 ⟨fun k => ⟨hsub (Finset.mem_coe.2 (hGm k)), hM (hsub (Finset.mem_coe.2 (hGm k))),
    (hmean _ (hGm k)).trans (mul_le_mul_of_nonneg_right (hG po hpo PLam hPL) (zero_le_one.trans (WeightFamilies.Wt.one_le_size _)))⟩, hz⟩⟩

theorem tiedP_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT Gc Prw : ℝ} (hown : OwnPr D p)
    (hW : TiedWStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT Gc Prw) (hT : TiedThStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT Gc)
    (hZ : TiedZStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT Gc)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (hp : HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0) (hc : SupBoundPageRows D large₂ ka) :
    ∃ (G₀ : Formalism.MainNotions.Gaps.EtaleWeightGaps.GlobalFamilyData (toWeightAlgebra F I dat hI iW hiW j h1 h2) ka wL wF) (Sh : Finset ((toWeightFamilies F).Cusp j wF))
      (Sh0 : Finset ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))),
      Submodule.span (toWeightFamilies F).KO (Sh : Set ((toWeightFamilies F).Cusp j wF)) = ⊤ ∧
      Submodule.span (toWeightFamilies F).KO (Sh0 : Set ((toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))) = ⊤ ∧
      ∀ (del : ℕ) (th' : Fin del → (toWeightFamilies F).Cusp j wF) (rz : ℕ) (alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ)
        (th0 : Fin rz → (toWeightFamilies F).Cusp j ((toWeightAlgebra F I dat hI iW hiW j h1 h2).wF0 wL wF))
        (zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin G₀.N) →₀ ℕ) →₀ (toWeightFamilies F).Cusp j ka)
        (rq : ℕ) (th : Fin rq → (toWeightFamilies F).Mlat j ka) (iet : ℕ) (et : (toWeightFamilies F).Cusp j (Formalism.MainNotions.Gaps.EtaleWeightGaps.etWt D j iet)),
        (∀ i, th' i ∈ Sh) → (∀ k, th0 k ∈ Sh0) → ZSel (refill G₀ del th' rz alz th0 zc rq th iet et) T →
        (refill G₀ del th' rz alz th0 zc rq th iet et).TiedW (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) Gc Prw ∧
        (refill G₀ del th' rz alz th0 zc rq th iet et).TiedTh (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) Gc ∧
        (refill G₀ del th' rz alz th0 zc rq th iet et).TiedZ (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) T Gc := by
  obtain ⟨G₀, hw⟩ := hW j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨Sh, hs, hth⟩ := hT hown j h1 h2 ka wL wF T nP nW h0 hp hc
  obtain ⟨Sh0, hs0, hz⟩ := hZ hown j h1 h2 ka wL wF T nP nW h0 hp hc
  exact ⟨G₀, Sh, Sh0, hs, hs0, fun del th' rz alz th0 zc rq th iet et a b c =>
    ⟨hw, hth (refill G₀ del th' rz alz th0 zc rq th iet et) a, hz (refill G₀ del th' rz alz th0 zc rq th iet et) b c⟩⟩

theorem hypCP_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT : ℝ} (hown : OwnPr D p)
    (hS : ScalStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT) (h2n : IntegralityAtPrime F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT)
    (hI4 : FourthHypothesisIndexBound F I dat hI iW hiW large₂ H C2 A2 CR CT)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (toWeightFamilies F).KO) → ℝ)
    (hp : HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0) (hc : SupBoundPageRows D large₂ ka)
    (hH1 : Formalism.MainNotions.Gaps.EtaleWeightGaps.WeightedPrimeSumBoundAlt large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) wL nus) :
    Formalism.MainNotions.Gaps.EtaleWeightGaps.HypC large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR 0 CT
      (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) ka wL wF T nP nW h0 nus :=
  (hypC_iff ..).2 ⟨hp, hS hown j h1 h2 ka wL wF T nP nW h0 hp hc, hH1, h2n hown j h1 h2 ka wL wF T nP nW h0 hp,
    hI4 j h1 h2 ka wL wF T nP nW h0 hp⟩

theorem hypP_of {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D} {p : ℕ} {large₂ : SizeData₂ D} {H : KHyp} {C2 A2 CR CT : ℝ} (hown : OwnPr D p)
    (hS : ScalStP F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT) (h2n : IntegralityAtPrime F I dat hI iW hiW hinj EX p large₂ H C2 A2 CR CT)
    (hI4 : FourthHypothesisIndexBound F I dat hI iW hiW large₂ H C2 A2 CR CT)
    (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
    (nus : HeightOneSpectrum (𝓞 (toWeightFamilies F).KO) → ℝ)
    (hp : HypPage large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR CT ka wL wF T nP nW h0) (hc : SupBoundPageRows D large₂ ka)
    (hH1 : H1 large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T) wL nus) :
    Hyp large₂ (toWeightAlgebra F I dat hI iW hiW j h1 h2) H C2 A2 CR 0 CT (Formalism.MainNotions.DIV.Cons.scalOfP (toWeightFamilies F) hinj EX p ka wL wF T)
      ka wL wF T nP nW h0 nus :=
  (hyp_iff ..).2 ⟨hp, hS hown j h1 h2 ka wL wF T nP nW h0 hp hc, hH1, h2n hown j h1 h2 ka wL wF T nP nW h0 hp,
    hI4 j h1 h2 ka wL wF T nP nW h0 hp⟩

end Views

end Formalism.MainNotions.Gaps.FamilyHypotheses
