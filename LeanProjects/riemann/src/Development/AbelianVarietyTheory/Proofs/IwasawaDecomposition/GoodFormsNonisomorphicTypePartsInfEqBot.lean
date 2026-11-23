import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
open Formalism.IndefR.Mult

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.TypesDisj

theorem prtW_inf_eq_bot : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat) (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (i : Fin D.R.m) (π π' : Φ), π ≠ π' → y.prtW F.lv2 i (rep π) ⊓ y.prtW F.lv2 i (rep π') = ⊥ := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG _ hI hP _ y Φ rep hR i π π' hne
  have hB : R.toRealDat.BaseW F.lv2 := hP.char.base
  have h0 := hB.models.νW i
  have hO := (GlobalTheory.FinTypesRows.isotL_span_orth D (Wc D i) _ R.θ (R.MW i (sg0 D A3.A)) (y.PW i) y.hF (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) (R.eWf i (sg0 D A3.A)) _ (R.fdW i) hI (D.sp.W_sig _)
    hB.models.inf (y.stdPsi.2 i) h0.1.1 h0.2 (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)).2
  have hHP := GlobalTheory.HilbertLevels.herm_lev hI hB.models.inf (D.sp.W_sig _) (R.MW i (sg0 D A3.A)) (R.βW i)
    (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))) h0.1.1 h0.2
  have hni : ¬ (rep π).Iso (rep π') := fun h => hne (hR.inj π π' h)
  rw [eq_bot_iff]
  rintro w ⟨hw, hw'⟩
  obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.1 hw
  obtain ⟨b, hb, hab⟩ := Submodule.mem_map.1 hw'
  have hba : b = a := LinearEquiv.injective _ hab
  subst hba
  have hz := hO _ _ hni b ha b hb
  have hm : b ∈ Mult R.θ (R.MW i (sg0 D A3.A)) (levS _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A))))
      (levChi _ (R.βW i) (R.datWp i (R.levL F.lv2 false (sg0 D A3.A)))) :=
    Mult.goodPart_le _ _ _ _ _ ha.1
  have hmT := Submodule.mem_map_of_mem (f := (PiTensorProduct.lift : MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap) hm
  by_contra hne0
  have hpos := hHP.pos ⟨_, hmT⟩ (fun h => hne0 ((Submodule.mem_bot ℂ).2 (congrArg Subtype.val h)))
  simp only at hpos
  unfold ipMT at hpos
  have hs : ∀ z, PiTensorProduct.lift.symm (((PiTensorProduct.lift : MMap (R.MW i (sg0 D A3.A)) ≃ₗ[ℂ] _).toLinearMap) z) = z :=
    fun z => LinearEquiv.symm_apply_apply _ z
  rw [hs, hz] at hpos
  simp at hpos

end GlobalTheory.Mem.R3.Rw.TypesDisj
