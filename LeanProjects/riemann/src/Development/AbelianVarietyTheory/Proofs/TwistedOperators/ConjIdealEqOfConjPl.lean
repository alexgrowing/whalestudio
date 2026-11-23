import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertHeckeOperatorsLiftsRationalSelfAdjointLabel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SelfDualAntitoneListIffInertPrimeHeckeExponents
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.InertEigScalar

theorem conjIdeal_eq_of_conjPl {D : D7} (P : Pl D.host.E) (hc : conjPl P = P) :
    Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal := by
  have h1 : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = P.asIdeal.map (Formalism.DivisionValues.cO D.host.E) := by
    unfold Formalism.HermitianLatticesTheory.conjIdeal
    show _ = Ideal.span _
    congr 1
    ext r
    constructor
    · rintro ⟨s, hs, hr⟩
      refine ⟨s, hs, ?_⟩
      apply RingOfIntegers.ext
      change _ = (algebraMap (𝓞 D.host.E) D.host.E r)
      rw [hr]
      rfl
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s, hs, rfl⟩
  rw [h1]
  exact congrArg HeightOneSpectrum.asIdeal hc

set_option maxHeartbeats 1000000 in

theorem inert_label_scalar : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ (j : Fin D.R.m) (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ (R.HV j A3.A.fam.μ0).H), GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h → GlobalTheory.Hk3.NormalFam (GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0) h → ∀ (P : Pl D.host.E), GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → conjPl P = P → ∀ d, GlobalTheory.Hk3.IsLab (Vc D j) P d → ∃ a : ℂ, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s _hOk hC _hEx _hH _hPG j c h hh _hN P hP hc d hd
  have hlab := (GlobalTheory.T.isSphericalDoubleCosetLabel_iff_decreasing (Vc D j) P d).1 hd
  obtain ⟨s', hs2, hsp, hspos, rfl⟩ :=
    (GlobalTheory.Hk3.labIn_selfDual_iff (Vc D j).rank d).1 ⟨hlab.1, hlab.2.1, hlab.2.2 hc⟩
  have hPg : P ∉ R.Pg := fun hm => (hP P (Or.inl hm)).1 rfl
  have hPQ : P ∉ R.Q A3.A.fam.μ0 := fun hm => (hP P (Or.inr hm)).1 rfl
  have hfix := conjIdeal_eq_of_conjPl P hc
  have hSb : P ∉ R.Sb := by
    have e : R.Sb = R.Pg := hC.allPl
    rw [e]; exact hPg
  have hoff : Formalism.IndefR.Bridge.InertOff P (R.Sb : Set (Pl D.host.E)) := ⟨hfix, fun hm => hSb (Finset.mem_coe.1 hm)⟩
  have honto : R.in_onto := hC.inert.onto
  have hex : ∃ Q, R.plI Q = P := honto P hoff
  obtain ⟨Q, hQ⟩ := hex
  have hQok : Q ∈ A3.okI A3.A.fam.μ0 := by
    refine (hC.inert.tie.okI A3.A.fam.μ0 Q).2 ⟨?_, ?_⟩
    · rw [hQ]; exact hfix
    · rw [hQ, hC.allPl]
      simp only [Set.mem_union, Finset.mem_coe]
      tauto
  subst hQ
  have hLt : R.in_L := hC.inert.hL
  have hn := hLt j A3.A.fam.μ0
  obtain ⟨Comparison₂⟩ := hn
  let inR' : ↥(A3.okI A3.A.fam.μ0) × List ℕ → Prop :=
    fun k => Formalism.L2.Col.InertTypeOk (Vc D j).rank k.2 ∧ R.plI k.1 = R.plI Q
  let Tie' : Bridge.HeckeTie (Bridge.ratF (Vc D j)) (R.B.L j A3.A.fam.μ0).pres (A3.heckeLI j A3.A.fam.μ0) inR'
      (fun k => GlobalTheory.Hk3.IsLabElt (Vc D j) (R.plI k.1) (GlobalTheory.Hk3.labIn (Vc D j).rank k.2))
      (fun k => GlobalTheory.Hk3.IsLocElt (Vc D j) (R.plI k.1)) :=
    { hx := Comparison₂.hx, hA := Comparison₂.hA, hx_ok := fun i hi => Comparison₂.hx_ok i hi.1, hA_loc := fun i hi => Comparison₂.hA_loc i hi.1,
      chi_loc := fun i hi => Comparison₂.chi_loc i hi.1, hDC := fun i hi => Comparison₂.hDC i hi.1, op_eq := fun i hi => Comparison₂.op_eq i hi.1 }
  let k : ↥(A3.okI A3.A.fam.μ0) × List ℕ := (⟨Q, hQok⟩, s')
  have hk : inR' k := ⟨⟨hsp, hspos, hs2⟩, rfl⟩
  have hin : ∀ i, inR' i → GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 (R.plI i.1) ∧ conjPl (R.plI i.1) = R.plI i.1 ∧
      (GlobalTheory.Hk3.labIn (Vc D j).rank i.2).Pairwise (fun a b => b ≤ a) := by
    rintro ⟨Q', t'⟩ ⟨hty, hpl⟩
    simp only at hpl ⊢
    rw [hpl]
    exact ⟨hP, hc, ((GlobalTheory.Hk3.labIn_selfDual_iff _ _).2 ⟨t', hty.2.2, hty.1, hty.2.1, rfl⟩).2.1⟩
  have key := (GlobalTheory.InertHeckeLift.inert_lifts R.toRealDat F.lv2 hC.base.lev hC.base.fam hC.base.models j
    A3.A.fam.μ0 _ (fun k => R.plI k.1) (fun k => GlobalTheory.Hk3.labIn (Vc D j).rank k.2) (A3.heckeLI j A3.A.fam.μ0) inR'
    hin Tie' k hk).2.2.2 h hh
  have hK : (R.toCx3 F).KFormL := Formalism.IndefR.Links.RealDat3.kFormL_of (F := F) hC.base.models
  have hop : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) =
      Tw.map (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) (Finsupp.single (GlobalTheory.Hk3.labIn (Vc D j).rank s') 1)) := by
    apply LinearMap.ext_on_range (hK j A3.A.fam.μ0).2
    intro b
    rw [← Formalism.IndefR.Cx.CxData.jL_opL (R.toCx3 F) hK]
    show Tw.mk (twAt D.what₂.embLL A3.A.v0) (R.jV j A3.A.fam.μ0 (A3.heckeLI j A3.A.fam.μ0 k _)) =
      Tw.mk (twAt D.what₂.embLL A3.A.v0) (h (R.plI Q) _ (R.jV j A3.A.fam.μ0 _))
    exact congrArg (Tw.mk (twAt D.what₂.embLL A3.A.v0)) (key _)
  refine ⟨cj (twAt D.what₂.embLL A3.A.v0) (c (Sum.inr k)), fun x hx => ?_⟩
  have hx' : (R.toCx3 F).opLC j A3.A.fam.μ0 (Sum.inl (Sum.inr k)) x = c (Sum.inr k) • x :=
    (Formalism.IndefR.U2.mem_eigPart.1 hx) (Sum.inr k)
  rw [hop] at hx'
  exact congrArg (Tw.out (s := twAt D.what₂.embLL A3.A.v0)) hx'

end GlobalTheory.InertEigScalar
