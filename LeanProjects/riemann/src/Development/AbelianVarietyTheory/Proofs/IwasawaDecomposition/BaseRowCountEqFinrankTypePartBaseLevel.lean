import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowFiniteTypesIsotypicPartsSpanOrthogonal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinksAnalyticHypothesesOfWeilRepHarishChandra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHermPosChainRealEndSpaceTuple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ISupIndepFiniteTypeComponentsThetaLiftForms
import Formalism.LocalToGlobal.IndefiniteReal.LinIndepOfOrth
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section

namespace GlobalTheory.BaseRowCount

theorem sum_finrank_le_of_indep {K V I : Type} [Field K] [AddCommGroup V] [Module K V] [Module.Finite K V]
    [Fintype I] (S : I → Submodule K V) (hi : iSupIndep S) :
    ∑ i, Module.finrank K (S i) ≤ Module.finrank K V := by
  classical
  have h : Module.finrank K ↥(⨆ i, S i) = ∑ i, Module.finrank K (S i) := by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hi.dfinsupp_lsum_injective]
    exact Module.finrank_directSum (R := K) (fun i => S i)
  rw [← h]
  exact Submodule.finrank_le _

set_option maxHeartbeats 2000000 in

theorem nRows0_eq_finrank_isotE : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → HostHyp D → ∀ π : D.what₂.FT, D.what₂.nRows0 π = Module.finrank ℂ (principalLevelFrame.isotE R.toRealDat.θ Y.PY (R.toRealDat.MY 0) (levS _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) (levChi _ (R.toRealDat.βY 0) (R.toRealDat.dat0 (R.toRealDat.levR F.lv2 false))) R.toRealDat.e0 (principalLevelFrame.rowRepR R.toRealDat.θ (Y.eFT π))) := by
  intro hW hDS hHC hCR D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH hHost
  classical
  have hI : Inputs D := GlobalTheory.LinksInputs.inputs_of_hypotheses hW hDS hHC hCR D
  have hB := hP.char.base
  have h0 := hB.models.ν0
  have hs := GlobalTheory.HilbertLevels.scaled (inv_pos.2 (GlobalTheory.HilbertLevels.nP_pos F.lv2 false)) h0.1.1 h0.2
  have hO := (GlobalTheory.FinTypesRows.isotL_span_orth D (Yc D 0) _ R.θ (R.MY 0) Y.PY Y.hF (R.βY 0)
    (R.dat0 (R.toRealDat.levR F.lv2 false)) R.e0 _ R.fd0 hI (D.sp.Y_sig _) hB.models.inf Y.stdPsi.1 hs.1 hs.2
    (GlobalTheory.Mem.R3.IsotIndep.gaL_finSum _ _ _ _ _)).2
  have hT := Y.tied.base
  let f : D.what₂.EE0 →ₗ[ℂ] _ := (Submodule.subtype _) ∘ₗ Y.Iz.jE.toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp Y.Iz.jE.injective
  let Wp : D.what₂.FT → Submodule ℂ D.what₂.EE0 := fun π => (Y.Iz.prt π).comap f

  have hOrth : ∀ π π', π ≠ π' → ∀ x ∈ Wp π, ∀ y ∈ Wp π', ⟪x, y⟫_ℂ = 0 := by
    intro π π' hne x hx y hy
    have hx' : f x ∈ Y.Iz.prt π := hx
    have hy' : f y ∈ Y.Iz.prt π' := hy
    rw [Y.prtE0] at hx' hy'
    obtain ⟨a, ha, hax⟩ := hx'
    obtain ⟨b, hb, hby⟩ := hy'
    have hni : ¬ (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π))).Iso
        (principalLevelFrame.FinTyp.conjT (principalLevelFrame.rowRepR R.θ (Y.eFT π'))) :=
      principalLevelFrame.not_iso_conjT fun h => hne (Y.eFT.injective (principalLevelFrame.rowRepR_inj R.θ _ _ h))
    have key := hO _ _ hni a ha b hb
    rw [hT.ee x y]
    unfold ChainReal.ipE ipMT
    refine Eq.trans ?_ key
    have e1 : ((Y.Iz.jE x : _) : _) = f x := rfl
    have e2 : ((Y.Iz.jE y : _) : _) = f y := rfl
    rw [e1, e2, ← hax, ← hby]
    congr 1
    · exact LinearEquiv.symm_apply_apply _ a
    · exact LinearEquiv.symm_apply_apply _ b
  have hInd : iSupIndep Wp := by
    apply OrthogonalFamily.independent
    rw [orthogonalFamily_iff_pairwise]
    intro σ σ' hne
    rw [Function.onFun, Submodule.isOrtho_iff_inner_eq]
    exact hOrth σ σ' hne
  have hle : ∀ π, D.what₂.nRows0 π ≤ Module.finrank ℂ (Wp π) := by
    intro π
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    let v : {σ // D.what₂.ft0 σ = π} → Wp π := fun σ => ⟨D.what₂.onb0 σ.1, by
      show f _ ∈ Y.Iz.prt π
      have := hT.ft σ.1
      rw [σ.2] at this
      exact this⟩
    have hli : LinearIndependent ℂ v := by
      apply LinearIndependent.of_comp (Wp π).subtype
      exact D.what₂.onb0.toBasis.linearIndependent.comp _ Subtype.val_injective
    exact hli.fintype_card_le_finrank
  have hdim : Module.finrank ℂ D.what₂.EE0 = D.what₂.D0 := by
    rw [Module.finrank_eq_card_basis D.what₂.onb0.toBasis, Fintype.card_fin]
  have hsum : ∑ π, D.what₂.nRows0 π = D.what₂.D0 := by
    unfold Formalism.BasicNotions.Rows.Data.nRows0
    rw [← Fintype.card_sigma, Fintype.card_congr (Equiv.sigmaFiberEquiv D.what₂.ft0), Fintype.card_fin]
  have hsle : ∑ π, Module.finrank ℂ (Wp π) ≤ D.what₂.D0 := hdim ▸ sum_finrank_le_of_indep Wp hInd
  have heq : ∀ π, D.what₂.nRows0 π = Module.finrank ℂ (Wp π) := by
    have h2 : ∑ π, D.what₂.nRows0 π = ∑ π, Module.finrank ℂ (Wp π) :=
      le_antisymm (Finset.sum_le_sum fun π _ => hle π) (hsle.trans hsum.ge)
    intro π
    exact (Finset.sum_eq_sum_iff_of_le (fun π _ => hle π)).1 h2 π (Finset.mem_univ π)
  intro π
  rw [heq π]
  have hrng : Y.Iz.prt π ≤ LinearMap.range f := by
    intro z hz
    rw [Y.prtE0] at hz
    obtain ⟨a, ha, rfl⟩ := hz
    have hz : (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap a ∈
        (toChainReal R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop).EEc false :=
      ⟨a, (Submodule.mem_inf.1 ha).1, rfl⟩
    refine ⟨Y.Iz.jE.symm ⟨_, hz⟩, ?_⟩
    change (Submodule.subtype _ (Y.Iz.jE (Y.Iz.jE.symm ⟨_, hz⟩))) = _
    rw [LinearEquiv.apply_symm_apply]
    rfl
  have hmap : (Wp π).map f = Y.Iz.prt π := by
    show ((Y.Iz.prt π).comap f).map f = _
    rw [Submodule.map_comap_eq, inf_eq_right.2 hrng]
  rw [(Submodule.equivMapOfInjective f hf (Wp π)).finrank_eq, hmap, Y.prtE0]
  first
    | exact LinearEquiv.finrank_map_eq _ _
    | exact LinearEquiv.finrank_map_eq (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _) _
    | exact ((Submodule.equivMapOfInjective (PiTensorProduct.lift : Mult.MMap (R.MY 0) ≃ₗ[ℂ] _).toLinearMap (LinearEquiv.injective _) _).finrank_eq).symm

end GlobalTheory.BaseRowCount
