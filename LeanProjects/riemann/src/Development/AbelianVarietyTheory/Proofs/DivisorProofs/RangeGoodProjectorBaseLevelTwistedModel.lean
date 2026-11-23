import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RangeComplexPointsLevelFormsEqGoodFormsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodProjectorUnitaryFormsModelLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WatIffType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.WType

theorem range_w0C_type : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → R.toRealDat.LUnif → ∀ i, LinearMap.range ((R.toCx3 F).w0C false i) = Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat i)) ⊓ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F s hOk hW hEx hU i
  obtain ⟨hC, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hX : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hI := (GlobalTheory.T.goodProjector_unitaryFormsModel_laws R.toRealDat F.lv2 hC hX i).1
  have hs : ∀ a, cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding a) = sg0 D A3.A a := fun a => by
    show cj _ (A3.A.v0.embedding a) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 a, cj_cj]
  rw [GlobalTheory.T.range_complex_points_level_forms_eq_good_forms R F hOk hW hU false i]
  ext x
  have hw := GlobalTheory.WatType.wat_iff_type R.toRealDat F.lv2 hOk.ok2 hC false i (Tw.out x)
  have hL : x ∈ Tw.sub (twAt D.what₂.embLL A3.A.v0) ((R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A))).comap (R.HW i (sg0 D A3.A)).e) ↔ (R.HW i (sg0 D A3.A)).e (Tw.out x) ∈ R.toRealDat.Wat i (sg0 D A3.A) (R.toRealDat.levL F.lv2 false (sg0 D A3.A)) := Iff.rfl
  have hR : Tw.out x ∈ LinearMap.range (eH R.toRealDat i) ↔ eH R.toRealDat i (Tw.out x) = Tw.out x := by
    refine ⟨?_, fun h => ⟨_, h⟩⟩
    rintro ⟨y, hy⟩
    rw [← hy, ← Module.End.mul_apply, hI]
  have hT : x ∈ typeSubspace A3 (R.toCx3 F) i (R.gWx F i) F.P0 F.ψ0⁻¹ ↔ ∀ p : (F.lv2.lvl false).P, R.gW i (sg0 D A3.A) (p : G) (Tw.out x) = sg0 D A3.A ((((F.lv2.lvl false).ψ⁻¹ p : D.what₂.LLˣ)) : D.what₂.LL) • Tw.out x := by
    unfold typeSubspace
    refine (Submodule.mem_iInf (R := ℂ) (M := (R.toCx3 F).W i) _).trans (forall_congr' fun p => ?_)
    show R.gW i (sg0 D A3.A) (p : G) (Tw.out x) - cj (twAt D.what₂.embLL A3.A.v0) (A3.A.fam.v0.embedding ((F.ψ0⁻¹ p : D.what₂.LLˣ) : D.what₂.LL)) • Tw.out x = 0 ↔ _
    rw [sub_eq_zero, hs]
    rfl
  constructor
  · intro h
    rw [hL, hw] at h
    exact ⟨hR.2 h.1, hT.2 h.2⟩
  · intro h
    rw [hL, hw]
    exact ⟨hR.1 h.1, hT.1 h.2⟩

end GlobalTheory.WType

end
