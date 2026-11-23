import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointApplyOfEigen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjIdealEqOfConjPl
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodVOfGoodL

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

set_option maxHeartbeats 1000000

namespace GlobalTheory.InjEigen

theorem label_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ), ∃ h, GlobalTheory.Hk3.IsOpsV R.toRealDat j A3.A.fam.μ0 h ∧ ∃ e : Eig D, ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c, ∀ P d, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P → GlobalTheory.Hk3.IsLab (Vc D j) P d → h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) = e P d • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hOk hpg j c
  obtain ⟨h, hops, hnf⟩ :=
    (GlobalTheory.DefiniteOps.definite_ops R.toRealDat F.lv2 hch.base.lev hch.base.fam hch.base.models).2 j A3.A.fam.μ0
  have key : ∀ P d, ∃ a : ℂ, GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P →
      GlobalTheory.Hk3.IsLab (Vc D j) P d → ∀ x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c,
        h P (Finsupp.single d 1) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) =
          a • (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x : (R.HV j A3.A.fam.μ0).H) := by
    intro P d
    by_cases hg : GlobalTheory.Hk3.Good R.toRealDat A3.A.fam.μ0 P
    · by_cases hl : GlobalTheory.Hk3.IsLab (Vc D j) P d
      · first
          | exact (Classical.em (Formalism.L2.DIV.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
          | exact (Classical.em (Formalism.DivisionValues.conjPl P = P)).elim
              (fun hc => (GlobalTheory.InertEigScalar.inert_label_scalar R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
              (fun hc => (GlobalTheory.SplitEigen.label_scalar_split R F hok hch hex hOk hpg j c h hops hnf P hg hc d hl).imp
                (fun _ ha _ _ => ha))
      · exact ⟨0, fun _ hl' => absurd hl' hl⟩
    · exact ⟨0, fun hg' => absurd hg' hg⟩
  choose e he using key
  exact ⟨h, hops, e, fun x hx P d hg hl => he P d hg hl x hx⟩

theorem inj_eig : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → LiftInj R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → ∀ j (c : (A3.liftI j A3.A.fam.μ0).OpIx → ℂ) (x y : (R.toCx3 F).FLC j A3.A.fam.μ0), x ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c → (R.toCx3 F).θ' j A3.A.fam.μ0 x ≠ 0 → y ∈ U2.eigPart (U2.liftHeckeOperators A3 (R.toCx3 F) j) c ⊓ U2.goodL A3 (R.toCx3 F) F.P0 F.ψ0 F.P1 F.ψ1 j → (R.toCx3 F).θ' j A3.A.fam.μ0 y = 0 → y = 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hok hch hex hinj hOk hpg j c x y hx hθx hy hθy
  obtain ⟨h, hops, e, he⟩ := label_eigensystem R F hok hch hex hOk hpg j c
  have hy' := Submodule.mem_inf.mp hy
  have hgood := GlobalTheory.goodV_of_goodL R F hok hch hex hOk hpg j y hy'.2
  clear hok hch hex hOk hpg hy
  have hθ : ∀ z : (R.toCx3 F).FLC j A3.A.fam.μ0, (R.toCx3 F).θ' j A3.A.fam.μ0 z =
      R.phs j • Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) z := fun z => rfl
  have hp : R.phs j ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ, h0]
    exact zero_smul ℂ _
  have hcj : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) ≠ 0 := by
    intro h0
    apply hp
    rw [← Formalism.IndefR.Links.cj_cj (twAt D.what₂.embLL A3.A.v0) (R.phs j), h0, map_zero]
  have hx0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) ≠ 0 := by
    intro h0
    apply hθx
    rw [hθ]
    have h1 : Tw.map (twAt D.what₂.embLL A3.A.v0) (R.thG j A3.A.fam.μ0) x = 0 := h0
    rw [h1]
    first
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) (R.HW j _).H) (R.phs j)
      | exact smul_zero (M := Tw (twAt D.what₂.embLL A3.A.v0) _) (R.phs j)
      | (simp only [smul_zero]; rfl)
  have hy0 : R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := by
    have h2 : Formalism.IndefR.Links.cj (twAt D.what₂.embLL A3.A.v0) (R.phs j) • R.thG j A3.A.fam.μ0 (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) = 0 := hθy
    exact (smul_eq_zero.mp h2).resolve_left hcj
  exact hinj j h hops e (Tw.out (s := twAt D.what₂.embLL A3.A.v0) x) (Tw.out (s := twAt D.what₂.embLL A3.A.v0) y) (fun P d hg hl => he x hx P d hg hl)
    (fun P d hg hl => he y hy'.1 P d hg hl) hx0 hgood hy0

end GlobalTheory.InjEigen
