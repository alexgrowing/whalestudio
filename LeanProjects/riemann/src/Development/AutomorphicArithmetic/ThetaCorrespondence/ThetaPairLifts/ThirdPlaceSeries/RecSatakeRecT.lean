import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProductSpehSatake
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecT
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EventuallyUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsHasSatakeOfUnr
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RecSpehQuotStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MTwinB
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRecTLocRecT

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
namespace GlobalTheory.FormDict.RecTLaws
section Core
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}
theorem hasSatGL_rec_alt (H : _root_.UpperTheory.Zero.LLC.IsRecT h rc) {n : ℕ} (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ)
    (hS : GlobalTheory.LFun.HasSatGL w σ.ρ S) :
    (rc (cls (ParLaws.toRep σ))).unr ∧
      (rc (cls (ParLaws.toRep σ))).frobEig = S.map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have hsph : IsSpherical (ParLaws.toRep σ).ρ := by
    have := hS.1
    unfold IsSpherical IsSphericalFor
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact this
  have hu : (rc (cls (ParLaws.toRep σ))).unr := (_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_unramified_iff_spherical H _).2 hsph
  obtain ⟨α, hα⟩ := _root_.UpperTheory.One.M.exists_hasSatake_of_unr_alt H hu
  have e : S = Finset.univ.val.map α := hS.unique (GlobalTheory.T.hasSatakeGL_of_hasSatakeParameters_principalSeries E w n _ σ.ρ α hα)
  refine ⟨hu, ?_⟩
  rw [_root_.GlobalTheory.CuspRep.ParLaws.reciprocity_eq_diagonal_inv_of_has_satake H hα, WD.frobEig_diag, e, Multiset.map_map]
  rfl
end Core
section Record
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} {A : NAut N}
  (T : GlobalTheory.RowTie.WDTie N A) (hL : _root_.UpperTheory.Zero.LLC.RecTExists)
theorem equiv_transported_reciprocity_eq_local_reciprocity (w : PlE H) {n : ℕ} (σ : LocIrr w n) :
    T.e w (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) = _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (N.plOm.2 w) (cls (ParLaws.toRep σ)) :=
  (T.e w).apply_symm_apply _
theorem transported_reciprocity_prod : RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w c n d hd σ σ' e
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.UpperTheory.One.M.locProd_eqG_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hd σ σ' e, List.map_ofFn]
  congr 2
  funext i
  exact (_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity T hL w (σ i)).symm
theorem transported_reciprocity_satake : RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w n σ S hS
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.FormDict.RecTLaws.hasSatGL_rec_alt (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) σ S hS
  have hu : A.unr (_root_.GlobalTheory.FormDict.recT_alt T hL w n σ) := (T.unr w _).2 (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h1)
  exact ⟨hu, (T.frobEig w _ hu).trans (by rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]; exact h2)⟩
theorem transported_reciprocity_speh_of_generic_unitary_dual (hTZ : GlobalTheory.Published.GenericUnitaryDualGL) (hSC : GlobalTheory.Published.StandardCosocleGL) :
    RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) := by
  intro w a d n hd P σ σ' hP hu hq
  have hg : IsGeneric σ.ρ := GlobalTheory.CuspRep.Generic.isGeneric_of_isLocComp H.E a P w σ hP
  apply (T.e w).injective
  rw [_root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity, e_lpSumList, _root_.GlobalTheory.T.local_langlands_speh_product' _ _ _ w _ _ (_root_.GlobalTheory.CuspRep.ParLawsT.isRecT_locRecT hL (N.plOm.2 w)) hTZ hSC a d n hd σ σ'
    hu hg hq, List.map_map]
  congr 1
  refine List.map_congr_left fun k _ => ?_
  simp only [Function.comp_apply, T.tw, _root_.GlobalTheory.FormDict.RecTLaws.equiv_transported_reciprocity_eq_local_reciprocity]
end Record
theorem transported_reciprocity_prod_and_speh_and_satake : GlobalTheory.Published.GenericUnitaryDualGL → GlobalTheory.Published.StandardCosocleGL →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂)
      (A : NAut N) (T : GlobalTheory.RowTie.WDTie N A), RecProd (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSpeh (_root_.GlobalTheory.FormDict.recT_alt T hL) ∧ RecSatake (_root_.GlobalTheory.FormDict.recT_alt T hL) :=
  fun hTZ hSC hL _ _ _ _ _ T => ⟨_root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_prod T hL, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_speh_of_generic_unitary_dual T hL hTZ hSC, _root_.GlobalTheory.FormDict.RecTLaws.transported_reciprocity_satake T hL⟩
end GlobalTheory.FormDict.RecTLaws
end
end
