import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AlgebraMapOlInjective
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LogSupSumLeOfNonvanishingDetLimit

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def etWt (D : D7) (j i : ℕ) : WeightFamilies.Wt D j :=
  wscalar D j (g0 D * i) (by unfold g0; exact ⟨5 ^ 4 * D.R.r * i, by ring⟩)

def a0 (D : D7) (j T : ℕ) : ℕ := T - WeightFamilies.dimY D j

def ga0 (wL : WeightFamilies.Wt D j) : ℝ :=
  (if h : 0 < (D.R.sigW j).1 then
      (⨅ τ, (wL.aP τ ⟨(D.R.sigW j).1 - 1, by omega⟩ : ℝ)) else 0) +
    (if h : 0 < (D.R.sigW j).2 then
      (⨅ τ, (wL.aM τ ⟨(D.R.sigW j).2 - 1, by omega⟩ : ℝ)) else 0) + wL.n

structure GlobalFamilyData (X : PJ D B P j) (ka wL wF : WeightFamilies.Wt D j) where
  N : ℕ
  w : Fin N → B.Cusp j wL
  del : ℕ
  th' : Fin del → B.Cusp j wF
  rz : ℕ
  alz : Fin rz → Fin (WeightFamilies.dimY D j) → ℕ
  th0 : Fin rz → B.Cusp j (X.wF0 wL wF)
  zc : Fin rz → ((Fin (WeightFamilies.dimY D j + 1) × Fin N) →₀ ℕ) →₀ B.Cusp j ka
  rq : ℕ
  th : Fin rq → B.Mlat j ka
  iet : ℕ
  et : B.Cusp j (etWt D j iet)

  mx : (B.KO →+* ℂ) → ℝ

namespace GlobalFamilyData

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF)

def Tied (large₂ : SizeData₂ D) (S : Scal B) (CRm : ℝ) (T : ℕ) (c Gc Prw Ch Ah Cf Af : ℝ) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL ∧ (∀ k, G.w k ∈ B.Mlat j wL) ∧
  Real.log G.N ≤ Prw * (wL.size - 1) ∧
  (∀ σ k, Real.log (B.supN j wL σ (G.w k)) ≤ G.mx σ) ∧
  (∑ σ, G.mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ Gc * wL.size ∧
  (∀ i, G.th' i ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B (G.th' i) ≤ Gc * wF.size) ∧
  (∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ G.th0 k ∈ B.Mlat j (X.wF0 wL wF) ∧
    WeightFamilies.meanLogSup B (G.th0 k) ≤ Gc * (X.wF0 wL wF).size ∧ ∑ i, G.alz k i = a0 D j T) ∧
  (∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β) ∧
  (∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0) ∧
  G.rq = WeightFamilies.rhoP B CRm T c j ka ∧
  (∀ i, ((G.th i : B.Mlat j ka) : B.Cusp j ka) ∈ X.Thc S.sK ka) ∧
  Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka)) ⊔
    WeightFamilies.MggK B CRm T c j ka = ⊤ ∧
  (∀ i, WeightFamilies.meanLogSup B ((G.th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) ∧
  (j < D.R.m → 0 < G.iet ∧ G.et ≠ 0 ∧ X.NonZeroComp _ G.et ∧
    (∀ la (y : X.Pt la), ((2 * G.iet * X.phiC la y : ℝ) : EReal) ≤ X.vAt la y (X.inc _ G.et)) ∧
    ∀ σ, Real.log (B.supN j _ σ G.et) / G.iet ≤ WeightFamilies.PPv D large₂ Cf Af)

end GlobalFamilyData

def DeepIn (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  (∃ (dH : ℕ) (Hm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => B.l2NormAlt j ka σ) dH), Hm.Conj) ∧ Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul X ∧
  Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd ∧ WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

def LAMw (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (C A : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (ka : WeightFamilies.Wt D j) (F : B.Cusp j ka), F ∈ B.Mlat j ka → F ≠ 0 →
    -(WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size) ≤ WeightFamilies.meanLogSup B F

def AdmW (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq : ℝ) : Prop :=
  adm1 B ∧ adm2 large₂ X H.CA H.C1 H.A1 K.CG K.AG ∧ adm3 large₂ X H.CA K.Cf K.Af ∧ ArchimedeanSignatureMatching large₂ X H.CA H.C1 H.A1 K.CW K.AW ∧
    LAMw large₂ B K.CL K.AL ∧ adm6 B K.CRm ∧ adm7 large₂ B K.CRm H.CK Ch Ah Cq Aq

def Shares (D : D7) {j : ℕ} (wL : WeightFamilies.Wt D j) (del rz rq d T : ℕ) (CRm c : ℝ) : Prop :=
  (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ d ∧
  (rz : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T ∧
  (rq : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def PolyDom (D : D7) {j : ℕ} (B : WeightFamilies.Prov D) (large₂ : SizeData₂ D) (K : KAdm) (H : KHyp) (C2 A2 CR Ch Ah Cq Aq : ℝ)
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

end Formalism.MainNotions.Gaps.EtaleWeightGaps
