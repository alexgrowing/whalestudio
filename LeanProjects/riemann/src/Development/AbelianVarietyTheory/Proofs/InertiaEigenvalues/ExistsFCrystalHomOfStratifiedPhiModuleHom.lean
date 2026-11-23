import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSemilinearBaseChangeExistsBasisEqImageOfBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FramedFCrystalExistsCoordsEveryPrismStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StratifiedCrystalValueMapCommFrobeniusStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsStratifiedPhiModuleHomValueMapStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {bk : BK K} {d : ℕ} {S : Strat bk d} {M : FCrys l ↥(OL K)}
  {e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)}

theorem IsCoord.v_eq_of_sum {B Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} (hV : IsCoord e V) (a : Hom B Q)
    (g : Hom bk.prism Q) (x : M.M B) (z : Fin d → Q.A) (hz : M.tr a x = ∑ i, z i • M.tr g (e i)) :
    V.v a g x = z := by
  obtain ⟨b, hb⟩ := GlobalTheory.T.isSemilinearBaseChange_exists_basis_eq_image_of_basis _ _ g.f _ _ (M.tr g) (M.tr_bc g) _ e
  have h := (hV a g x).symm.trans hz
  simp only [← hb] at h
  funext i
  have := congrArg (fun y => b.repr y i) h
  simpa [Finsupp.single_apply, Module.Basis.repr_self] using this

theorem IsCoord.v_tr {B B' Q : Obj l ↥(OL K)} {V : Eval S B (M.M B)} {V' : Eval S B' (M.M B')}
    (hV : IsCoord e V) (hV' : IsCoord e V') (k : Hom B B') (a : Hom B' Q) (g : Hom bk.prism Q) (x : M.M B) :
    V'.v a g (M.tr k x) = V.v (a.comp k) g x :=
  hV'.v_eq_of_sum a g _ _ (by rw [← M.tr_comp]; exact hV _ g x)

theorem exists_fHom_of_isStratHom : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d d' : ℕ)
    (S : Strat bk d) (S' : Strat bk d') (M M' : FCrys l ↥(OL K))
    (e : Module.Basis (Fin d) bk.prism.A (M.M bk.prism)) (e' : Module.Basis (Fin d') bk.prism.A (M'.M bk.prism)),
    Framed S M e → Framed S' M' e' → ∀ Y : Matrix (Fin d') (Fin d) bk.S, IsStratHom S S' Y →
    ∃ u : FHom M M', ∀ j, u.u bk.prism (e j) = ∑ i, bk.toP (Y i j) • e' i := by
  intro l _ K bk d d' S S' M M' e e' hF hF' Y hY
  choose V hV using GlobalTheory.T.framedFCrystal_exists_coords_every_prism l K bk d S M e hF
  choose V' hV' using GlobalTheory.T.framedFCrystal_exists_coords_every_prism l K bk d' S' M' e' hF'
  choose w hw using fun B => GlobalTheory.T.exists_stratifiedPhiModuleHom_valueMap l K bk d d' S S' Y hY B (M.M B) (M'.M B) (V B) (V' B)
  refine ⟨⟨w, fun {P P'} k x => ?_, fun P t x m k h =>
    GlobalTheory.T.stratifiedCrystalValueMap_comm_frobenius l K bk d d' S S' M e M' e' hF hF' Y hY P (V P) (V' P) (hV P) (hV' P) (w P) (hw P) t x m k h⟩,
    fun j => ?_⟩
  · obtain ⟨C, h, ⟨f⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk P'
    apply (GlobalTheory.T.injective_and_range_of_prism_cover l K bk d' S' P' C (M'.M P') (V' P') h f hc).1
    rw [hw, IsCoord.v_tr (hV P) (hV P'), IsCoord.v_tr (hV' P) (hV' P'), hw]
  · have h1 := hV' bk.prism (Hom.id _) (Hom.id _) (w bk.prism (e j))
    have h2 : (V bk.prism).v (Hom.id _) (Hom.id _) (e j) = Pi.single j 1 :=
      IsCoord.v_eq_of_sum (hV _) _ _ _ _ (by simp [M.tr_id, Pi.single_apply])
    have h3 := ((hw bk.prism _ (Hom.id _) (Hom.id _) (e j)).trans (congrArg _ h2)).trans
      (Matrix.mulVec_single_one _ j)
    rw [h3] at h1
    simp only [M'.tr_id] at h1
    refine h1.trans (Finset.sum_congr rfl fun i _ => ?_)
    exact congrArg (fun c : bk.prism.A => c • e' i) (show ((Y.map (BK.hf (Hom.id bk.prism))).col j) i = bk.toP (Y i j) from rfl)

end GlobalTheory.BSP
