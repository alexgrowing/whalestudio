import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanRhoTEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

namespace GlobalTheory.InertFrameLoc

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}

theorem secW_toCompl_tmul_mul (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    (b : Fv D.host.F v) (o m : D.host.E) :
    secW hw h (toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m) =
      pairA D.host.F 0 (singleFin v b) ⊗ₜ[D.host.F] (o * m) := by
  have e : toCompl h (b ⊗ₜ[D.host.F] o) * algebraMap D.host.E (w.adicCompletion D.host.E) m =
      toCompl h (b ⊗ₜ[D.host.F] (o * m)) := by
    rw [toCompl_tmul, toCompl_tmul, map_mul, mul_assoc]
  have e2 : toCompl h (b ⊗ₜ[D.host.F] (o * m)) = GlobalTheory.LFun.InertChart.complEquiv hw h (b ⊗ₜ[D.host.F] (o * m)) := rfl
  rw [e, e2]
  show GlobalTheory.EmbChart.tensAt D.host.E v ((GlobalTheory.LFun.InertChart.complEquiv hw h).symm _) = _
  rw [RingEquiv.symm_apply_apply, GlobalTheory.EmbChart.tensAt_tmul, GlobalTheory.EmbChart.atPlace_apply]

theorem secW_rank_one_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ frameLat S)
    {t : Fin T.rank → D.host.E} (ht : t ∈ frameLat T) {z : w.adicCompletion D.host.E} (hz : z ∈ Ov D.host.E w) :
    (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E)
      (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  obtain ⟨y, rfl⟩ := GlobalTheory.LFun.InertChart.toCompl_surjective h z
  have hy := (GlobalTheory.LFun.InertChart.mem_intLoc_iff hw h y).2 hz
  refine intLoc_induction (p := fun y => (Matrix.of fun i j => secW hw h (toCompl h y *
      algebraMap D.host.E (w.adicCompletion D.host.E) (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v)) (fun b hb o => ?_) ?_ (fun y y' h1 h2 => ?_)
      (fun y h1 => ?_) hy
  · refine AddSubgroup.subset_closure ⟨singleFin v b, fun u => ?_, fun u hu => evalV_singleFin_ne hu _, a, ha, s, hs,
      o • t, Submodule.smul_mem _ o ht, ?_⟩
    · by_cases e : u = v
      · subst e; rw [evalV_singleFin_self]; exact hb
      · rw [evalV_singleFin_ne e]; exact zero_mem _
    · ext i j
      rw [Matrix.of_apply, Matrix.of_apply, secW_toCompl_tmul_mul]
      congr 1
      rw [Pi.smul_apply, Algebra.smul_def]
      ring
  · convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  · convert add_mem h1 h2 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, map_add, add_mul]
  · convert neg_mem h1 using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.neg_apply, map_neg, neg_mul]

theorem secW_span_mem (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v)
    {c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E} (hc : IsConjAt D.sp.cm.sig h c) {S T : HSp D}
    {a : D.host.E} (ha : a ∈ D.host.AA) {p : Fin T.rank → w.adicCompletion D.host.E} (hp : p ∈ latAt w (frameLat T))
    {y : Fin S.rank → w.adicCompletion D.host.E} (hy : y ∈ latAt w (frameLat S)) :
    ∀ z ∈ Ov D.host.E w, (Matrix.of fun i j => secW hw h (z * algebraMap D.host.E (w.adicCompletion D.host.E) a * p i *
      ∑ k, c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) : WO S T) ∈
      latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  have hst : ∀ x : D.host.E, star x = D.sp.cm.sig x := fun _ => rfl
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t, ht, rfl⟩ := hp
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s, hs, rfl⟩ := hy
      intro z hz
      convert secW_rank_one_mem hw h ha hs ht hz using 1
      ext i j
      simp only [Matrix.of_apply, GlobalTheory.LFun.InertChart.conj_algebraMap hc, map_mul, map_sum, hst]
      ring_nf
    | zero =>
      intro z hz
      convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
      ext i j
      simp
    | add y y' _ _ h1 h2 =>
      intro z hz
      convert add_mem (h1 z hz) (h2 z hz) using 1
      ext i j
      simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    | smul o y _ h1 =>
      intro z hz
      convert h1 (z * c o) (mul_mem hz (GlobalTheory.LFun.InertChart.conj_mem hw hc o.2)) using 1
      ext i j
      have e : ∀ k, c ((o • y) k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j) =
          c o * (c (y k) * algebraMap D.host.E (w.adicCompletion D.host.E) (S.gram k j)) := fun k => by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, mul_assoc]
      simp only [Matrix.of_apply, e, ← Finset.mul_sum]
      congr 1
      ring
  | zero =>
    intro z hz
    convert zero_mem (latO S T (frameLat S) (frameLat T) (fun u => u = v)) using 1
    ext i j
    simp
  | add p p' _ _ h1 h2 =>
    intro z hz
    convert add_mem (h1 z hz) (h2 z hz) using 1
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply, Pi.add_apply, map_add, add_mul, mul_add]
  | smul o p _ h1 =>
    intro z hz
    convert h1 (z * o) (mul_mem hz o.2) using 1
    ext i j
    simp only [Matrix.of_apply, Pi.smul_apply, Subring.smul_def, smul_eq_mul]
    congr 1
    ring

theorem uPt_mem_latO : ∀ (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (S T : HSp D) (k : w.adicCompletion D.host.E) (aS : GL (Fin S.rank) (w.adicCompletion D.host.E)) (aT : GL (Fin T.rank) (w.adicCompletion D.host.E)), GlobalTheory.InertLoc.IsGen D w k → IsFrameAt w (frameLat S) aS → IsFrameAt w (frameLat T) aT → ∀ x : Matrix (Fin T.rank) (Fin S.rank) (w.adicCompletion D.host.E), (∀ i j, x i j ∈ Formalism.UG.intL (w.adicCompletion D.host.E)) → uPt hw h k aS aT x ∈ latO S T (frameLat S) (frameLat T) (fun u => u = v) := by
  intro D v w hw h S T k aS aT hk haS haT x hx
  obtain ⟨-, ⟨a₀, ha₀, rfl⟩, -⟩ := hk
  obtain ⟨c, hc, -⟩ := GlobalTheory.LFun.InertChart.existsUnique_isConjAt D.sp.cm.sig hw h
  obtain ⟨ϖ, hU⟩ := GlobalTheory.LFun.InertChart.exists_isUnramInv (isCMExt_host D) hw hc
  have hcc : ∀ z, c (c z) = z := hU.1
  set ι := algebraMap D.host.E (w.adicCompletion D.host.E) with hι
  set Gw := S.gram.map ι with hGw
  set Gi := (S.gram⁻¹).map ι with hGi
  have hGG : Gi * Gw = 1 := by
    rw [hGi, hGw, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit S),
      Matrix.map_one _ (map_zero _) (map_one _)]
  set N := (aS⁻¹).1 * Gi with hN
  have hG : ∀ l i, c (ι (S.gram l i)) = ι (S.gram i l) := fun l i => by
    rw [GlobalTheory.LFun.InertChart.conj_algebraMap hc, (GlobalTheory.Doubling.isHermND_gram S).1 i l]
  have hY : ∀ j, (fun l => c (N j l)) ∈ latAt w (frameLat S) := by
    intro j
    rw [GlobalTheory.LFun.InertChart.mem_latAt_iff hw hc (GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D S v)]
    intro y hy
    have hu := (haS ((aS⁻¹).1 *ᵥ y)).2 (by rwa [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]) j
    have e : Formalism.UG.hform c (S.gram.map ι) y (fun l => c (N j l)) = c ((N *ᵥ (Gw *ᵥ y)) j) := by
      simp only [Formalism.UG.hform, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hG, hGw]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [e, Matrix.mulVec_mulVec, hN, Matrix.mul_assoc, hGG, Matrix.mul_one]
    exact GlobalTheory.LFun.InertChart.conj_mem hw hc hu
  have hcol : ∀ j l, ∑ m, c (c (N j m)) * ι (S.gram m l) = (aS⁻¹).1 j l := fun j l => by
    simp only [hcc]
    have := congrFun (congrFun (show N * Gw = (aS⁻¹).1 by rw [hN, Matrix.mul_assoc, hGG, Matrix.mul_one]) j) l
    rw [← this, Matrix.mul_apply]
    rfl
  have hT : ∀ i, (fun r => aT.1 r i) ∈ latAt w (frameLat T) := fun i => by
    have := (haT (Pi.single i 1)).1 fun m => by
      by_cases e : m = i
      · subst e; simp
      · simp [e]
    convert this using 1
    funext r
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hdec : uPt hw h (ι a₀) aS aT x = ∑ i, ∑ j, (Matrix.of fun r l => secW hw h (x i j * ι a₀ * aT.1 r i *
      ∑ m, c (c (N j m)) * ι (S.gram m l)) : WO S T) := by
    ext r l
    simp only [uPt, Matrix.map_apply, Matrix.sum_apply, Matrix.of_apply, hcol]
    rw [show ∀ f : Fin T.rank → Fin S.rank → w.adicCompletion D.host.E, ∑ i, ∑ j, secW hw h (f i j) =
        secW hw h (∑ i, ∑ j, f i j) from fun f => by simp only [map_sum]]
    congr 1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hdec]
  exact sum_mem fun i _ => sum_mem fun j _ => secW_span_mem hw h hc ha₀ (hT i) (hY j) (x i j) (hx i j)

end GlobalTheory.InertFrameLoc
